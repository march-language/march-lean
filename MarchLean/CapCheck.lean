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

/-- The caps a declaration's *signature* mentions. Only signatures matter for
Check 1 — body uses are Check 1b, which is warning-only and not implemented. -/
def capsInSignature : Decl → List String
  | .dfn _ params _ =>
      params.flatMap (fun (_, _, annot) =>
        match annot with | some t => capsInTy t | none => [])
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
  -- Check 1 — signature Cap(X) coverage
  let sigCaps := decls.flatMap capsInSignature
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
  | none => .ok

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
             (Term.lit (Lit.unit) (Ty.con "Unit" []))]],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps siblingViolation
  -- expect: violation — IO.FileWrite not covered by IO.FileRead

/-- accept/t46: the root `needs IO` covers `Cap(IO.Network)`. -/
def rootCovers : Module := {
  decls := [Decl.dmod "Server" [
    Decl.dneeds ["IO"],
    Decl.dfn "listen" [("cap", Lin.unrestricted,
                        some (Ty.con "Cap" [Ty.con "IO.Network" []]))]
             (Term.lit (Lit.unit) (Ty.con "Unit" []))]],
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
  decls := [Decl.dfn "f" [] (Term.lit (Lit.int 1) (Ty.con "Int" []))],
  schemes := [], insts := [], moduleCaps := [] }
#eval checkCaps noCapsAtAll
  -- expect: ok

end MarchLean.CapCheck
