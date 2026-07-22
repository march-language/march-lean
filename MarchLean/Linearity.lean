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
  -- to the pattern's own binder, not this outer one.
  | .match_ s arms _ =>
      uses name s + (arms.map (fun (p, e) =>
        if (Pattern.boundNames p).contains name then 0 else uses name e)).foldl Nat.max 0
  | .lit _ _ | .unsupported _ => 0

/-- Enforce a binder's linearity given its use count. -/
def enforce (name : String) (l : Lin) (n : Nat) : CheckResult :=
  match l with
  | .linear => if n == 1 then .ok else .reject s!"linear '{name}' used {n} times (must be exactly 1)"
  | .affine => if n <= 1 then .ok else .reject s!"affine '{name}' used {n} times (must be ≤ 1)"
  | .unrestricted => .ok

/-- Enforce every param in a param list against `body`'s use counts. -/
def enforceParams (ps : List (String × Lin × Option Ty)) (body : Term) : CheckResult :=
  ps.foldl (fun acc (p, l, _) => match acc with | .ok => enforce p l (uses p body) | o => o) .ok

/-- Walk a term enforcing every linear/affine binder it introduces. -/
partial def checkTerm : Term → CheckResult
  | .lam ps b _ =>
      match enforceParams ps b with
      | .ok => checkTerm b
      | other => other
  | .let_ n l _ r b _ =>
      match checkTerm r with
      | .ok => match enforce n l (uses n b) with
               | .ok => checkTerm b
               | other => other
      | other => other
  | .letfn _ p l _ fb b _ =>
      match enforce p l (uses p fb) with
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
      | .ok => arms.foldl (fun acc (_, e) => match acc with | .ok => checkTerm e | o => o) .ok
      | o => o
  | .lit _ _ | .var _ _ _ | .unsupported _ => .ok

def checkDecl : Decl → CheckResult
  | .dfn _ ps body =>
      match enforceParams ps body with
      | .ok => checkTerm body
      | other => other
  | .dlet _ body => checkTerm body
  | .dtype _ _ _ => .ok
  | .unsupported => .ok

def checkLinearity (m : Module) : CheckResult :=
  m.decls.foldl (fun acc d => match acc with | .ok => checkDecl d | o => o) .ok

end MarchLean.Linearity

-- Living tests (executable documentation; run at build time via `#eval`).
namespace MarchLean.Linearity.Test
open MarchLean.Syntax MarchLean.Result MarchLean.Linearity

-- linear param used exactly once -> ok
def linOnce : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)]
      (Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linOnce))  -- expected: CheckResult.ok

-- linear param used twice -> reject
def linTwice : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)]
      (Term.tuple [Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []),
                   Term.var "x" ⟨"f",1,3,1,4⟩ (Ty.con "Int" [])] (Ty.tuple [Ty.con "Int" [], Ty.con "Int" []]))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linTwice)) -- expected: CheckResult.reject ...

-- linear param never used -> reject
def linNever : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)] (Term.lit (Lit.int 1) (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linNever)) -- expected: CheckResult.reject ...

-- Regression (coordinator review): linear param used once in EACH of two
-- mutually-exclusive match arms -> ok. Proves the MAX-over-arms fix: along
-- any single execution path only one arm runs, so this is exactly one use,
-- not two. Summing (the pre-fix behaviour) would wrongly reject this.
def linMatchBalanced : Module :=
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)]
      (Term.match_ (Term.lit (Lit.bool true) (Ty.con "Bool" []))
        [(Pattern.wild, Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" [])),
         (Pattern.wild, Term.var "x" ⟨"f",1,3,1,4⟩ (Ty.con "Int" []))]
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
  { decls := [Decl.dfn "f" [("x", Lin.linear, none)]
      (Term.match_ (Term.lit (Lit.int 0) (Ty.con "Int" []))
        [(Pattern.var "x" Lin.unrestricted, Term.var "x" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))]
        (Ty.con "Int" []))],
    schemes := [], insts := [] }
#eval (repr (checkLinearity linMatchShadowed)) -- expected: CheckResult.reject "linear 'x' used 0 times ..."

end MarchLean.Linearity.Test

-- Real linear-use-sample coverage (both accepted single-use linear programs
-- must be `.ok`) lives in `scripts/conformance-harness.sh` over the full
-- corpus. Build-time `IO.FS.readFile` of the gitignored sample dir was removed
-- (it broke CI on a fresh checkout). The synthetic `#eval`s above
-- (linOnce/linTwice/linNever/linMatchBalanced/linMatchShadowed) keep the
-- exactly-once / per-branch / shadowing properties covered at build time.
