import MarchLean.Syntax

/-!
# `MarchLean.Result`

Shared result type and type-level helpers, originally salvaged out of A1's
`Check.lean` (now retired) so they would survive `checkModule`'s removal:
they depend only on `Syntax`, never on `Check`'s own verification logic.
Used today by `MarchLean.Compare` (A2's inference oracle) and
`MarchLean.Linearity` (independent use-counting).
-/

namespace MarchLean.Result

open MarchLean.Syntax

inductive CheckResult where
  | ok
  | reject (msg : String)
  | skip (reason : String)
  deriving Repr, Inhabited

/-- A2's INDEPENDENT verdict on a program, distinct from A1's `CheckResult`:
`reject` (inference found it ill-typed) is kept separate from `typesDiffer`
(A2 accepts it as well-typed, but its per-node types disagree with march's
`resolved_ty`). `MarchLeanCheck` maps these to distinct exit codes (1 vs 4) so
the harness can tell "A2 rejects the program" apart from "A2 accepts it but
disagrees on types" — collapsing them would hide a reject-file disagreement. -/
inductive OracleVerdict where
  | accept
  | reject (msg : String)
  | typesDiffer (msg : String)
  | skip (reason : String)
  deriving Repr, Inhabited

/-- Sequence two checks: run the continuation only if the first is `.ok`,
otherwise short-circuit with the first non-`ok` result. -/
def CheckResult.andThen : CheckResult → (Unit → CheckResult) → CheckResult
  | .ok, f => f ()
  | other, _ => other

/-- Datatype environment: name → (type-param names, constructor sigs). Built
from `Decl.dtype`; used to canonicalize named types and to type ADT ctors. -/
abbrev TyEnv := List (String × (List String × List CtorSig))

def buildTyEnv (decls : List Decl) : TyEnv :=
  decls.foldr (fun d acc =>
    match d with
    | .dtype n ps ctors => (n, (ps, ctors)) :: acc
    | _ => acc) []

/-- Substitute type arguments for quantified ids in a type. -/
partial def substTy (s : List (Int × Ty)) : Ty → Ty
  | .var id => match s.lookup id with | some t => t | none => .var id
  | .con n args => .con n (args.map (substTy s))
  | .arrow a b => .arrow (substTy s a) (substTy s b)
  | .tuple ts => .tuple (ts.map (substTy s))
  | .record fs => .record (fs.map (fun (n, t) => (n, substTy s t)))
  | .lin l t => .lin l (substTy s t)
  | .natOp o a b => .natOp o (substTy s a) (substTy s b)
  | t => t

/-- Canonicalize a type before equality: recurse structurally so nested types
normalize. Named records would expand to their structural form here, but Task 3
maps `TDRecord`/aliases to `Decl.unsupported` (skip-gated), so `TCon`s reaching
this point are nominal (variant ADTs / primitives) and are left as-is (recursing
into their args). -/
partial def canon (env : TyEnv) : Ty → Ty
  | .con n args => .con n (args.map (canon env))
  | .arrow a b => .arrow (canon env a) (canon env b)
  | .tuple ts => .tuple (ts.map (canon env))
  | .record fs => .record (fs.map (fun (n, t) => (n, canon env t)))
  | .lin l t => .lin l (canon env t)
  | .natOp o a b => .natOp o (canon env a) (canon env b)
  | t => t

/-- Canonical type equality (§4). -/
def tyEq (env : TyEnv) (a b : Ty) : Bool := (canon env a).beq (canon env b)

/-- `Num`: satisfied by numeric primitives (or a still-free var). -/
def numOk (env : TyEnv) (t : Ty) : Option (Sum String String) :=
  match canon env t with
  | .con "Int" [] | .con "Float" [] | .var _ => none
  | other => some (.inr s!"Num not satisfied by {repr other}")

/-- `Ord`: satisfied by the ordered primitives (or a still-free var). -/
def ordOk (env : TyEnv) (t : Ty) : Option (Sum String String) :=
  match canon env t with
  | .con "Int" [] | .con "Float" [] | .con "String" [] | .con "Bool" [] | .var _ => none
  | other => some (.inr s!"Ord not satisfied by {repr other}")

/-- Is this scheme constraint out of the checked fragment (a user `CInterface`
whose name is not `Num`/`Eq`/`Ord`, or an `unsupported` constraint)? Used by
the whole-file skip gate — shared by A1's `Check.checkModule` and A2's
`Compare.inferModule`, which apply the same judgment call. -/
def constraintOutOfFragment : Constraint → Bool
  | .interface "Num" _ | .interface "Ord" _ | .interface "Eq" _ => false
  | .interface _ _ => true
  | .unsupported => true
  | _ => false

end MarchLean.Result
