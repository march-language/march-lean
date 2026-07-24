import MarchLean.Syntax
import MarchLean.CapLattice

/-!
# Capability checks 1, 4 and 5

march's three ERROR-level capability checks, ported from
`typecheck.ml`'s `check_module_needs`. All three share the single
subsumption relation in `CapLattice`.

**Checks 1b and 1c are deliberately absent.** They are WARNING-only in march
(`core-march-types.md` §2.8.6), so a checker that rejected on them would
manufacture false MISMATCHes against a march that accepts. The cost is real
and inherited on purpose: this checker will not catch a function body calling
a builtin that needs an undeclared capability.
-/
namespace MarchLean.CapCheck
open MarchLean.Syntax
open MarchLean.CapLattice

inductive CapResult where
  | ok
  | violation (msg : String)
  deriving Repr, Inhabited

/-- Every capability named by a `Cap(X)` type anywhere inside a type. -/
partial def capsInTy : Ty → List String
  | .con "Cap" [.con x _] => [x]
  | .con _ args => args.flatMap capsInTy
  | .arrow a b  => capsInTy a ++ capsInTy b
  | .tuple ts   => ts.flatMap capsInTy
  | .record fs  => fs.flatMap (fun (_, t) => capsInTy t)
  | .lin _ t    => capsInTy t
  | _           => []

/-- The caps a declaration's PARAMETER signature mentions. Only signatures
matter for Check 1 — body uses are Check 1b, which is warning-only and not
implemented. Return-type caps are handled separately by
`capsInReturnSignature` (they are gated differently — see `checkOneModule`). -/
def capsInSignature : Decl → List String
  | .dfn _ params _ _ =>
      params.flatMap (fun (_, _, annot) =>
        match annot with | some t => capsInTy t | none => [])
  | _ => []

/-- The caps a declaration's RETURN-type annotation mentions. march's Check 1
scans `param_tys @ ret_tys`, so a `Cap(X)` in return position counts exactly
like one in a parameter. Kept separate from `capsInSignature` because the
return scan is GATED on the enclosing module being fully in fragment — see
`checkOneModule`. -/
def capsInReturnSignature : Decl → List String
  | .dfn _ _ retAnnot _ =>
      match retAnnot with | some t => capsInTy t | none => []
  | _ => []

/-- The caps this module declares via `needs`. -/
def declaredNeeds (decls : List Decl) : List String :=
  decls.flatMap (fun d => match d with | .dneeds ps => ps | _ => [])

/-- Is `used` covered by any declared need? Reflexive and directional. -/
def covered (declared : List String) (used : String) : Bool :=
  declared.any (fun need => capSubsumes need used)

/-- Check one module (not recursing into nested modules — the caller does
that, since each module is checked against its OWN declared needs). -/
def checkOneModule (modName : String) (decls : List Decl)
    (moduleCaps : List (String × List String)) : CapResult :=
  let declared := declaredNeeds decls
  -- Check 1 — signature Cap(X) coverage over `param_tys @ ret_tys`
  -- (march's `check_module_needs`). Parameter caps are ALWAYS scanned.
  --
  -- RETURN caps are scanned only when this module is ENTIRELY in fragment. A
  -- module carrying an out-of-fragment declaration (e.g. a `proof cap`, which
  -- decodes to `Decl.unsupported`) may satisfy a return cap through machinery
  -- this checker does not model: march's self-declaration exemption lets a
  -- module's own `proof cap X` implicitly cover `Cap(Module.X)` returned by
  -- its public fns (accept/t62 — `Cap(Db.Migrated)` returned under `needs IO`,
  -- accepted). Rather than mis-reject such a return, defer — the file skips
  -- downstream via the out-of-fragment gate, exactly as it did before this
  -- scan existed. A fully-in-fragment module has only modeled IO caps and no
  -- such escape, so an uncovered return cap there is a real Check 1 violation
  -- (the M1 gap: e.g. `fn f(cap : Cap(IO.Console)) : Cap(IO.Network)` under
  -- `needs IO.Console`). Params are left unconditional so no existing
  -- signature-based reject changes.
  let retCaps :=
    if decls.any Decl.hasUnsupported then [] else decls.flatMap capsInReturnSignature
  let sigCaps := decls.flatMap capsInSignature ++ retCaps
  match sigCaps.find? (fun c => !covered declared c) with
  | some bad =>
      .violation s!"Check 1: `Cap({bad})` used in module `{modName}` but `{bad}` is not declared in `needs`"
  | none =>
  -- Check 5 — extern cap coverage
  let externCaps := decls.flatMap (fun d =>
    match d with | .dextern (some c) => [c] | _ => [])
  match externCaps.find? (fun c => !covered declared c) with
  | some bad =>
      .violation s!"Check 5: extern in module `{modName}` requires `Cap({bad})` but `{bad}` is not declared in `needs`"
  | none =>
  -- Check 4 — transitive `use` coverage
  let usedMods := decls.flatMap (fun d =>
    match d with | .duse p => [p] | _ => [])
  let unmet := usedMods.flatMap (fun m =>
    match moduleCaps.find? (fun (n, _) => n == m) with
    | some (_, reqs) => (reqs.filter (fun r => !covered declared r)).map (fun r => (m, r))
    | none => [])
  match unmet.head? with
  | some (m, r) =>
      .violation s!"Check 4: module `{modName}` imports `{m}` which requires `Cap({r})`, but `{r}` is not declared in `needs`"
  | none =>
  -- Check 7 — realtime exclusion (typecheck.ml:7162-7182). A fn whose
  -- PARAMETER signature carries BOTH a `Tagged(_, Realtime)` type and a
  -- `Cap(X)` with X ∈ {Alloc, IO, Panic} (the excluded roots — NOT other IO
  -- sub-caps like `IO.Network`) is rejected: realtime functions may not also
  -- hold allocation-, IO-, or panic-capable capabilities. Signature-level
  -- only (`dfn` param annotations) — this checker does not scan bodies
  -- (that is Check 1b, warning-only in march and deliberately not modelled;
  -- see the module docstring above).
  let isRealtimeTagged : Ty → Bool
    | .con "Tagged" [_, .con "Realtime" _] => true
    | _ => false
  let isExcludedCap : Ty → Bool
    | .con "Cap" [.con r _] => r == "Alloc" || r == "IO" || r == "Panic"
    | _ => false
  let paramTysOf : Decl → List Ty
    | .dfn _ params _ _ => params.filterMap (fun (_, _, a) => a)
    | _ => []
  match decls.find? (fun d =>
      (paramTysOf d).any isRealtimeTagged && (paramTysOf d).any isExcludedCap) with
  | some (.dfn name params _ _) =>
      let excludedName :=
        match (params.filterMap (fun (_, _, a) => a)).find? isExcludedCap with
        | some (.con "Cap" [.con r _]) => r
        | _ => "?"
      .violation s!"Check 7: fn `{name}` in module `{modName}` takes a `Tagged(_, Realtime)` param and an excluded `Cap({excludedName})` param (Alloc|IO|Panic are excluded alongside a realtime tag)"
  | _ => .ok

/-- Walk the whole module tree, checking each module against its own needs. -/
partial def checkDecls (moduleCaps : List (String × List String)) : List Decl → CapResult
  | [] => .ok
  | .dmod name inner :: rest =>
      match checkOneModule name inner moduleCaps with
      | .violation m => .violation m
      | .ok =>
        match checkDecls moduleCaps inner with   -- nested modules
        | .violation m => .violation m
        | .ok => checkDecls moduleCaps rest
  | _ :: rest => checkDecls moduleCaps rest

/-- Entry point. Also checks the top level as an implicit module, so a file
with `needs`/`Cap(X)` outside any `mod` block is still checked. -/
def checkCaps (m : Module) : CapResult :=
  match checkOneModule "<top-level>" m.decls m.moduleCaps with
  | .violation msg => .violation msg
  | .ok => checkDecls m.moduleCaps m.decls

end MarchLean.CapCheck

namespace MarchLean.CapCheck
open MarchLean.Syntax

/-- `mod Store do needs IO.FileRead; fn save(cap : Cap(IO.FileWrite), …) end`
— reject/t38: siblings do not cover each other. -/
def siblingViolation : Module := {
  decls := [Decl.dmod "Store" [
    Decl.dneeds ["IO.FileRead"],
    Decl.dfn "save" [("cap", Lin.unrestricted,
                      some (Ty.con "Cap" [Ty.con "IO.FileWrite" []]))]
             none (Term.lit (Lit.unit) (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps siblingViolation
  -- expect: violation — IO.FileWrite not covered by IO.FileRead

/-- accept/t46: the root `needs IO` covers `Cap(IO.Network)`. -/
def rootCovers : Module := {
  decls := [Decl.dmod "Server" [
    Decl.dneeds ["IO"],
    Decl.dfn "listen" [("cap", Lin.unrestricted,
                        some (Ty.con "Cap" [Ty.con "IO.Network" []]))]
             none (Term.lit (Lit.unit) (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rootCovers
  -- expect: ok

/-- reject/t39: `use Vault` where Vault needs IO.Mut, importer declares nothing. -/
def useUncovered : Module := {
  decls := [Decl.dmod "Main" [Decl.duse "Vault"]],
  schemes := [], insts := [], moduleCaps := [("Vault", ["IO.Mut"])] }
#eval checkCaps useUncovered
  -- expect: violation — Check 4, IO.Mut not covered

/-- accept/t49: same, but the importer declares `needs IO.Mut`. -/
def useCoveredExact : Module := {
  decls := [Decl.dmod "Main" [Decl.dneeds ["IO.Mut"], Decl.duse "Vault"]],
  schemes := [], insts := [], moduleCaps := [("Vault", ["IO.Mut"])] }
#eval checkCaps useCoveredExact
  -- expect: ok

/-- Check 4 uses the same subsumption: the root `needs IO` covers IO.Mut. -/
def useCoveredByRoot : Module := {
  decls := [Decl.dmod "Main" [Decl.dneeds ["IO"], Decl.duse "Vault"]],
  schemes := [], insts := [], moduleCaps := [("Vault", ["IO.Mut"])] }
#eval checkCaps useCoveredByRoot
  -- expect: ok

/-- Check 5: an extern declaring Cap(IO.Foreign) with no covering needs. -/
def externUncovered : Module := {
  decls := [Decl.dmod "F" [Decl.dextern (some "IO.Foreign")]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externUncovered
  -- expect: violation — Check 5

/-- Check 5 satisfied. -/
def externCovered : Module := {
  decls := [Decl.dmod "F" [Decl.dneeds ["IO.Foreign"], Decl.dextern (some "IO.Foreign")]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps externCovered
  -- expect: ok

/-- A module with no caps at all is trivially fine — the overwhelmingly
common case, and it must not be flagged. -/
def noCapsAtAll : Module := {
  decls := [Decl.dfn "f" [] none (Term.lit (Lit.int 1) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noCapsAtAll
  -- expect: ok

/-- True iff a `CapResult` is a violation — a `Bool` projection so the
`native_decide` guards below can pin the verdict at build time. (An end-to-end
guard that decodes real `march --emit-core-ast` output and cap-checks it lives
in `MarchLeanCheck.lean`, which already imports the decoder — this file's core
stays independent of `Elab`.) -/
def CapResult.isViolation : CapResult → Bool
  | .violation _ => true
  | .ok          => false

/-- Finding M1 regression, direct unit (no decode): a fully-in-fragment module
whose ONLY defect is an
uncovered RETURN cap is a Check 1 violation — the param `Cap(IO.Console)` is
covered by `needs IO.Console`, the return `Cap(IO.Network)` is not. -/
def retCapUncovered : Module := {
  decls := [Decl.dneeds ["IO.Console"],
    Decl.dfn "get_net"
      [("cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Console" []]))]
      (some (Ty.con "Cap" [Ty.con "IO.Network" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retCapUncovered  -- expect: violation (return IO.Network uncovered)
example : (checkCaps retCapUncovered).isViolation = true := by native_decide

/-- A covered RETURN cap must NOT be flagged: broad `needs IO` subsumes the
returned `Cap(IO.Network)` (the param here is a plain `Int`, isolating the
return path). -/
def retCapCovered : Module := {
  decls := [Decl.dneeds ["IO"],
    Decl.dfn "get_net"
      [("port", Lin.unrestricted, some (Ty.con "Int" []))]
      (some (Ty.con "Cap" [Ty.con "IO.Network" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retCapCovered  -- expect: ok
example : (checkCaps retCapCovered).isViolation = false := by native_decide

/-- Check 7 (reject/t41-shaped): a fn with BOTH a `Tagged(_, Realtime)` param
and a `Cap(IO)` param — one of the three excluded roots — is a violation. -/
def rtExcluded : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_d", Lin.unrestricted, some (Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []])),
       ("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rtExcluded
  -- expect: violation — Check 7, `Cap(IO)` excluded alongside the realtime tag

/-- Check 7 requires BOTH conditions: a realtime-tagged param alongside a
NON-excluded cap (`IO.Network`, not a root `IO`/`Alloc`/`Panic`) must NOT be
flagged. -/
def rtSafe : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_d", Lin.unrestricted, some (Ty.con "Tagged" [Ty.con "Int" [], Ty.con "Realtime" []])),
       ("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO.Network" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps rtSafe
  -- expect: ok — IO.Network is not an excluded root

/-- Check 7's other half: an excluded cap with NO realtime-tagged param must
NOT be flagged (this is just an ordinary Check-1-covered `Cap(IO)` use). -/
def noRt : Module := {
  decls := [Decl.dmod "RT" [
    Decl.dneeds ["IO"],
    Decl.dfn "step"
      [("_c", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      none (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noRt
  -- expect: ok

/-- The gate that keeps accept/t62 safe: a module carrying an out-of-fragment
declaration (here a bare `Decl.unsupported`, standing in for `proof cap
Migrated`) does NOT get its return caps scanned. march covers t62's returned
`Cap(Db.Migrated)` — under only `needs IO` — via the self-declaration
exemption this checker does not model, and ACCEPTS. So `checkCaps` must NOT
reject: it defers to the downstream out-of-fragment skip gate. Without the
gate, the uncovered `Db.Migrated` return would wrongly reject an accept file. -/
def retProofCapDeferred : Module := {
  decls := [Decl.unsupported,   -- e.g. `proof cap Migrated`
            Decl.dneeds ["IO"],
    Decl.dfn "run_migrations"
      [("cap", Lin.unrestricted, some (Ty.con "Cap" [Ty.con "IO" []]))]
      (some (Ty.con "Cap" [Ty.con "Db.Migrated" []]))
      (Term.lit (Lit.int 0) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps retProofCapDeferred  -- expect: ok (deferred, NOT rejected)
example : (checkCaps retProofCapDeferred).isViolation = false := by native_decide

end MarchLean.CapCheck
