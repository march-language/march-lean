import MarchLean.Syntax
import MarchLean.Result

/-!
# `MarchLean.Linearity`

Independent linearity use-counting for the A1 fragment. March hands Lean
**no** linearity certificate — it discards use-counts once its own checker
has verified them — so this module re-derives linear/affine use-discipline
directly from the AST's `Lin` qualifiers (on `lam`/`let_`/`letfn`/`dfn`
binders) and the term's own structure, independently of march's elaborator.

This is pure use-COUNTING, not type-checking: `Check.checkModule` (Task 4)
already verified `resolved_ty` consistency; `checkLinearity` only asks "is
every linear binder used exactly once, and every affine binder used at most
once, within its scope?". `unrestricted` binders carry no constraint.

Reuses `Result.CheckResult` (`ok`/`reject`/`skip`) so both checks can be
combined by the Task 6 CLI without a second result type.

**N-ary note:** `Term.app` carries `(fn, args : List Term, ty)` and
`Term.lam`/`Decl.dfn` carry `params : List (String × Lin × Option Ty)`
(Task 4's N-ary refactor plus each param's optional surface annotation,
matching march's `EApp`/`ELam`/`DFn` faithfully). Linearity ignores the
`Option Ty` annotation entirely (it needs only name + `Lin`). `uses`
therefore sums over `fn` and every element of `args`; a name is shadowed
by a `lam`/`dfn` if it appears anywhere in that binder's param list; and
`enforceParams` enforces EVERY param in the list (not just the first).
`Term.letfn` was not touched by the N-ary refactor (march's `ELetFn` is
never decoded by `Elab.decodeTerm` — it falls to `Term.unsupported` — so
no real sample exercises this arm), so it keeps its original single
`(param : String)` shape.

**Known caveat (from Task 3):** a `Pattern.var` decoded from a match arm
always carries `Lin.unrestricted` — the JSON `PatVar` node has no `lin`
field of its own (linearity lives on the enclosing `binding`/`param`, not
on a bare pattern) — so match-bound pattern variables are NOT
linearity-enforced by this pass. Only `lam`/`let_`/`letfn`/`dfn` binders
carry a real (possibly linear/affine) `Lin`, and only those are checked
here. This is an accepted limitation of the A1 fragment, not a bug to fix
in this task.
-/

namespace MarchLean.Linearity

open MarchLean.Syntax MarchLean.Result

/-- Every name a pattern binds (recursively through `con`/`tuple`/`record`/`as`),
used by `uses`'s `match_` arm to detect when an arm's pattern SHADOWS the name
being counted (so uses of that name inside the arm body belong to the
pattern's own binder, not the outer one). Declared with an explicit `_root_`
path (rather than plain `Pattern.boundNames`, which — inside this file's
`namespace MarchLean.Linearity` — would land at `MarchLean.Linearity.Pattern.boundNames`
and NOT be found by dot notation on a `MarchLean.Syntax.Pattern` value) so
`p.boundNames` resolves everywhere below. -/
partial def _root_.MarchLean.Syntax.Pattern.boundNames : Pattern → List String
  | .var n _ => [n]
  | .as n p => n :: p.boundNames
  | .con _ args => args.foldl (fun acc p => acc ++ p.boundNames) []
  | .tuple elems => elems.foldl (fun acc p => acc ++ p.boundNames) []
  | .record fs => fs.foldl (fun acc (_, p) => acc ++ p.boundNames) []
  | .or_ alts => alts.foldl (fun acc p => acc ++ p.boundNames) []
  | .wild | .lit _ | .unsupported => []

/-- Count uses of `name` in a term (occurrences of `Term.var name`). -/
partial def uses (name : String) : Term → Nat
  | .var n _ _ => if n == name then 1 else 0
  | .app f args _ => uses name f + (args.map (uses name)).foldl (·+·) 0
  | .lam ps b _ => if ps.any (fun (p, _, _) => p == name) then 0 else uses name b   -- shadowed
  | .let_ n _ _ r b _ => uses name r + (if n == name then 0 else uses name b)
  | .letfn n p _ _ fb b _ =>
      (if n == name || p == name then 0 else uses name fb) + (if n == name then 0 else uses name b)
  | .ite c u v _ => uses name c + uses name u + uses name v
  | .con _ args _ => (args.map (uses name)).foldl (·+·) 0
  | .tuple es _ => (es.map (uses name)).foldl (·+·) 0
  | .record fs _ => (fs.map (fun (_, e) => uses name e)).foldl (·+·) 0
  | .field r _ _ _ => uses name r
  -- Match arms are mutually exclusive: along any single execution path a
  -- variable is used (scrutinee count) + (that ONE taken arm's count), so
  -- linear enforcement must take the MAX over arms, not the sum (a linear var
  -- used once in each of N arms is valid, not N uses). An arm whose pattern
  -- SHADOWS `name` (binds it itself) contributes 0 — inner uses there belong
  -- to the pattern's own binder, not this outer one. A guard runs (and may use
  -- `name`) whenever this arm is the one taken, exactly like the body, so it
  -- is counted the same way (summed with the body's count, within this arm).
  | .match_ s arms _ =>
      uses name s + (arms.map (fun (p, g, e) =>
        if (Pattern.boundNames p).contains name then 0
        else uses name e + (g.map (uses name)).getD 0)).foldl Nat.max 0
  -- `.opaque_` is grouped with `.unsupported`, NOT recursed into, and the
  -- reason is the same for all three linearity walks below: a `Term.opaque_`
  -- reports `hasUnsupported = true`, so `Compare.inferModule`'s skip gate
  -- returns `.skip` and `MarchLeanCheck.run` exits 2 BEFORE `checkLinearity`
  -- is ever called. This walk is unreachable on any module containing one, so
  -- the only correct choice is the one that changes nothing — and counting 0
  -- is additionally the SAFE half of the unreachable pair: `opaque_`'s
  -- children are an unordered bag with no modelled binder or
  -- mutual-exclusivity structure (an `ECond`'s arms are mutually exclusive
  -- like a `match_`'s, but nothing here records that), so summing their uses
  -- would over-count a linear binder used once per arm into a bogus "used N
  -- times" reject.
  | .lit _ _ | .opaque_ _ _ | .unsupported _ => 0

/-- The outermost linearity qualifier a type carries (`Ty.lin l _`), else
`unrestricted`. march writes a value's linearity either as a binder keyword
(`linear let`/`affine` param), as a *type* modifier on the binding's
annotation (`let c : affine Cap2 = ..`), or — for a call to a function with a
`linear`/`affine` return type — on the binding's *inferred* type (a plain
`let h = mk()` where `mk : linear Res` yields `h : linear Res`). Only the first
form reaches a binder's `Lin` field; the other two live on a `Ty`, so the
linearity pass must read them off the type to enforce them. -/
def Ty.outerLin : Ty → Lin
  | .lin l _ => l
  | _ => .unrestricted

/-- Effective linearity of a `let_` binding: the binder keyword if it carries
one, else the annotation's outer qualifier (`let c : affine T = ..`), else the
rhs's inferred-type outer qualifier (`let h = mk()` with `mk : linear ..`).
This makes A2 enforce affine-via-annotation (reject/t64) and linear-return
propagation (reject/t78), which march models but which don't surface on the
binder's own `Lin` field. -/
def effLin (binder : Lin) (annot : Option Ty) (rhs : Term) : Lin :=
  match binder with
  | .unrestricted =>
      let fromAnnot := match annot with | some t => Ty.outerLin t | none => .unrestricted
      match fromAnnot with
      | .unrestricted => Ty.outerLin rhs.ty
      | l => l
  | l => l

/-- Does `name` occur free INSIDE a closure (`Term.lam` body) anywhere within
`t`, i.e. is it captured by a closure? A `lam` whose param list rebinds `name`
shadows it (uses inside belong to the param, not our binder); otherwise any
free use of `name` in the lam body — `uses name b > 0`, which itself already
discounts shadowing and counts through nested lams — means `name` escaped into
a closure. Intervening `let_`/`letfn`/`match_` binders that rebind `name` cut
the scope short (a later capture is of a different binder). Used to detect the
closure-capture case A2's static use-counting cannot judge (reject/t62): a
closure may be invoked any number of times, so a captured linear/affine value's
use count is not statically knowable. -/
partial def capturedInLam (name : String) : Term → Bool
  | .lam ps b _ => if ps.any (fun (p, _, _) => p == name) then false else uses name b > 0
  | .let_ n _ _ r b _ => capturedInLam name r || (if n == name then false else capturedInLam name b)
  | .letfn n p _ _ fb b _ =>
      (if n == name || p == name then false else capturedInLam name fb) ||
      (if n == name then false else capturedInLam name b)
  | .app f args _ => capturedInLam name f || args.any (capturedInLam name)
  | .ite c u v _ => capturedInLam name c || capturedInLam name u || capturedInLam name v
  | .con _ args _ => args.any (capturedInLam name)
  | .tuple es _ => es.any (capturedInLam name)
  | .record fs _ => fs.any (fun (_, e) => capturedInLam name e)
  | .field r _ _ _ => capturedInLam name r
  | .match_ s arms _ =>
      capturedInLam name s || arms.any (fun (p, g, e) =>
        if (Pattern.boundNames p).contains name then false
        else capturedInLam name e || (g.map (capturedInLam name)).getD false)
  -- `.opaque_` with `.unsupported`: unreachable behind the skip gate (see
  -- `uses`), and `false` keeps this predicate consistent with `uses`'s 0 —
  -- reporting a capture whose use count is not being tracked would flip an
  -- unreachable file from its old answer to a `.skip` for no gain.
  | .lit _ _ | .var _ _ _ | .opaque_ _ _ | .unsupported _ => false

/-- Enforce a binder's linearity given its use count. -/
def enforce (name : String) (l : Lin) (n : Nat) : CheckResult :=
  match l with
  | .linear => if n == 1 then .ok else .reject s!"linear '{name}' used {n} times (must be exactly 1)"
  | .affine => if n <= 1 then .ok else .reject s!"affine '{name}' used {n} times (must be ≤ 1)"
  | .unrestricted => .ok

/-- Check one binder: if a linear/affine binder is captured by a closure within
its scope, the whole file must SKIP (A2 does not model closure escape analysis
— it cannot statically know how many times the closure runs); otherwise enforce
its use count. Skip takes precedence over a use-count reject, since a capture
means the count is not trustworthy in the first place. -/
def bindCheck (name : String) (l : Lin) (scope : Term) : CheckResult :=
  match l with
  | .unrestricted => .ok
  | _ =>
      if capturedInLam name scope then
        .skip s!"linear/affine binder '{name}' captured in a closure; escape analysis not modeled"
      else enforce name l (uses name scope)

/-- Check every param in a param list against `body` (use count + closure
capture). A captured linear/affine param skips the whole file. -/
def enforceParams (ps : List (String × Lin × Option Ty)) (body : Term) : CheckResult :=
  ps.foldl (fun acc (p, l, _) => match acc with | .ok => bindCheck p l body | o => o) .ok

/-- Walk a term enforcing every linear/affine binder it introduces. -/
partial def checkTerm : Term → CheckResult
  | .lam ps b _ =>
      match enforceParams ps b with
      | .ok => checkTerm b
      | other => other
  | .let_ n l annot r b _ =>
      match checkTerm r with
      | .ok => match bindCheck n (effLin l annot r) b with
               | .ok => checkTerm b
               | other => other
      | other => other
  | .letfn _ p l _ fb b _ =>
      match bindCheck p l fb with
      | .ok => match checkTerm fb with | .ok => checkTerm b | o => o
      | other => other
  | .app f args _ =>
      (f :: args).foldl (fun acc t => match acc with | .ok => checkTerm t | o => o) .ok
  | .ite c u v _ => match checkTerm c with | .ok => (match checkTerm u with | .ok => checkTerm v | o => o) | o => o
  | .con _ args _ => args.foldl (fun acc t => match acc with | .ok => checkTerm t | o => o) .ok
  | .tuple es _ => es.foldl (fun acc t => match acc with | .ok => checkTerm t | o => o) .ok
  | .record fs _ => fs.foldl (fun acc (_, t) => match acc with | .ok => checkTerm t | o => o) .ok
  | .field r _ _ _ => checkTerm r
  | .match_ s arms _ => match checkTerm s with
      | .ok => arms.foldl (fun acc (_, g, e) => match acc with
          | .ok => (match g with
              | some gt => (match checkTerm gt with | .ok => checkTerm e | o => o)
              | none => checkTerm e)
          | o => o) .ok
      | o => o
  -- `.opaque_` with `.unsupported`: unreachable behind the skip gate (see
  -- `uses`). `.ok` is the behavior-preserving answer and cannot mask
  -- anything — the file exits 2 before this pass runs either way.
  | .lit _ _ | .var _ _ _ | .opaque_ _ _ | .unsupported _ => .ok

def checkDecl : Decl → CheckResult
  | .dfn _ ps _ body =>
      match enforceParams ps body with
      | .ok => checkTerm body
      | other => other
  | .dlet _ body => checkTerm body
  | .dtype _ _ _ => .ok
  -- A3 Task 2/3 decode-only constructors: no term of their own to check.
  -- `dmod` is inert-but-unreachable here: `checkLinearity` flattens nested
  -- `dmod`s via `flattenDecls` before this is ever called, so its children
  -- already appear as top-level decls.
  | .dmod .. | .dneeds _ | .duse _ | .dextern .. | .dproofcap _ | .dopts _ => .ok
  | .unsupported => .ok

/-- Flattens nested `dmod` bodies into the enclosing scope first — linearity
treats a module as transparent (see `flattenDecls`'s docstring). -/
def checkLinearity (m : Module) : CheckResult :=
  (flattenDecls m.decls).foldl (fun acc d => match acc with | .ok => checkDecl d | o => o) .ok

end MarchLean.Linearity

-- Living tests (executable documentation; run at build time via `#eval`).
namespace MarchLean.Linearity.Test
open MarchLean.Syntax MarchLean.Result MarchLean.Linearity

-- linear param used exactly once -> ok
def linOnce : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] none
      (Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linOnce))  -- expected: CheckResult.ok

-- linear param used twice -> reject
def linTwice : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] none
      (Term.tuple [Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []),
                   Term.var "x" ⟨"f",1,3,1,4⟩ (Ty.con "Int" [])] (Ty.tuple [Ty.con "Int" [], Ty.con "Int" []]))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linTwice)) -- expected: CheckResult.reject ...

-- linear param never used -> reject
def linNever : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] none (Term.lit (Lit.int 1) (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linNever)) -- expected: CheckResult.reject ...

-- Regression (coordinator review): linear param used once in EACH of two
-- mutually-exclusive match arms -> ok. Proves the MAX-over-arms fix: along
-- any single execution path only one arm runs, so this is exactly one use,
-- not two. Summing (the pre-fix behaviour) would wrongly reject this.
def linMatchBalanced : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] none
      (Term.match_ (Term.lit (Lit.bool true) (Ty.con "Bool" []))
        [(Pattern.wild, none, Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" [])),
         (Pattern.wild, none, Term.var "x" ⟨"f",1,3,1,4⟩ (Ty.con "Int" []))]
        (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linMatchBalanced)) -- expected: CheckResult.ok

-- Regression (coordinator review): a match arm's pattern SHADOWS the outer
-- linear param `x` (rebinds the same name), and the outer `x` is never used
-- anywhere else -> the outer binder is genuinely unused -> reject. Proves the
-- shadow fix: without it, the arm body's use of the shadowing (inner) `x`
-- would be misattributed to the outer linear param, masking the real
-- unused-linear-binder bug.
def linMatchShadowed : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] none
      (Term.match_ (Term.lit (Lit.int 0) (Ty.con "Int" []))
        [(Pattern.var "x" Lin.unrestricted, none, Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))]
        (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linMatchShadowed)) -- expected: CheckResult.reject "linear 'x' used 0 times ..."

-- Affine-via-type-annotation, used twice -> reject (reject/t64). The binder's
-- own `Lin` is `unrestricted` (there is no `affine let` keyword); the affine
-- lives on the annotation `c : affine Cap2`, so `effLin` must read it off the
-- annotation type for enforcement to fire.
def affineAnnotTwice : Module :=
  { decls := [Decl.dlet "main"
      (Term.let_ "c" Lin.unrestricted (some (Ty.lin Lin.affine (Ty.con "Cap2" [])))
        (Term.con "C" [Term.lit (Lit.int 1) (Ty.con "Int" [])] (Ty.con "Cap2" []))
        (Term.tuple [Term.var "c" ⟨"f",1,1,1,2⟩ (Ty.con "Cap2" []),
                     Term.var "c" ⟨"f",1,3,1,4⟩ (Ty.con "Cap2" [])] (Ty.tuple []))
        (Ty.tuple []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity affineAnnotTwice)) -- expected: CheckResult.reject "affine 'c' used 2 times ..."

-- Linear-return propagation: `let h = mk()` where the rhs's inferred type is
-- `linear Res`, and `h` is never used -> reject (reject/t78). The binder `Lin`
-- is `unrestricted` and there is no annotation; the linear qualifier lives on
-- the rhs's resolved type, which `effLin` reads via `Ty.outerLin rhs.ty`.
def linearReturnUnconsumed : Module :=
  { decls := [Decl.dlet "main"
      (Term.let_ "h" Lin.unrestricted none
        (Term.app (Term.var "mk" ⟨"f",1,1,1,3⟩ (Ty.arrow (Ty.tuple []) (Ty.lin Lin.linear (Ty.con "Res" []))))
                  [] (Ty.lin Lin.linear (Ty.con "Res" [])))
        (Term.tuple [] (Ty.tuple []))
        (Ty.tuple []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linearReturnUnconsumed)) -- expected: CheckResult.reject "linear 'h' used 0 times ..."

-- Closure capture of a linear binder -> whole-file SKIP (reject/t62). `r` is
-- `linear` and used exactly once syntactically, but that one use is INSIDE a
-- closure (`let f = fn -> take(r)`), so its runtime use count is not statically
-- knowable. A2 must skip rather than accept (its single-use count would wrongly
-- pass) or reject (it cannot prove a violation either).
def linearCapturedInClosure : Module :=
  { decls := [Decl.dlet "main"
      (Term.let_ "r" Lin.linear none
        (Term.con "R" [Term.lit (Lit.int 1) (Ty.con "Int" [])] (Ty.con "Res" []))
        (Term.let_ "f" Lin.unrestricted none
          (Term.lam [] (Term.app (Term.var "take" ⟨"f",1,1,1,5⟩ (Ty.arrow (Ty.con "Res" []) (Ty.con "Int" [])))
                                  [Term.var "r" ⟨"f",1,6,1,7⟩ (Ty.con "Res" [])] (Ty.con "Int" []))
                     (Ty.arrow (Ty.tuple []) (Ty.con "Int" [])))
          (Term.tuple [] (Ty.tuple []))
          (Ty.tuple []))
        (Ty.tuple []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linearCapturedInClosure)) -- expected: CheckResult.skip "...captured in a closure..."

-- Guard against over-skip: a linear binder used once OUTSIDE any closure, in a
-- program that also HAS a closure (over an unrelated unrestricted value), must
-- still be checked normally (ok), not skipped.
def linearNotCaptured : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] none
      (Term.let_ "g" Lin.unrestricted none
        (Term.lam [("y", Lin.unrestricted, none)] (Term.var "y" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))
                  (Ty.arrow (Ty.con "Int" []) (Ty.con "Int" [])))
        (Term.var "x" ⟨"f",2,1,2,2⟩ (Ty.con "Int" []))
        (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linearNotCaptured)) -- expected: CheckResult.ok

end MarchLean.Linearity.Test

-- Real linear-use-sample coverage (both accepted single-use linear programs
-- must be `.ok`) lives in `scripts/conformance-harness.sh` over the full
-- corpus. Build-time `IO.FS.readFile` of the gitignored sample dir was removed
-- (it broke CI on a fresh checkout). The synthetic `#eval`s above
-- (linOnce/linTwice/linNever/linMatchBalanced/linMatchShadowed) keep the
-- exactly-once / per-branch / shadowing properties covered at build time.
