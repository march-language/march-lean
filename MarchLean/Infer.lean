import MarchLean.Syntax
import MarchLean.Result

/-!
# `MarchLean.Infer`

Core data structures for the independent Hindley–Milner inference engine
(A2). `MTy` is the inference-time type representation; `InferM` is the
monad inference runs in; `repr`/`zonk` follow and deep-resolve
metavariable links.

Later tasks add `unify` (Task 3), `generalize`/`instantiate` (Task 4), and
`infer` (Task 5).

## Adaptation: metavariables are `Nat` ids into an arena, not raw `IO.Ref`s

The brief's interface spec calls for `MTy.mvar (r : IO.Ref MVar)` — a
metavariable holding a *direct* mutable reference to its own cell,
mirroring the classic ML-union-find encoding where `ref` cells are
embedded straight into the recursive type. **This does not kernel-check
in Lean 4.** Verified directly: even the minimal, non-mutual

```
inductive Foo where
  | leaf
  | ref (r : IO.Ref Foo)
```

is rejected by the kernel with `(kernel) arg #1 of 'Foo.ref' contains a
non valid occurrence of the datatypes being declared` — Lean's strict
positivity / nested-inductive checker cannot certify a self-nested
occurrence of the type being defined as a type argument to `IO.Ref`
(`ST.Ref`'s own definition threads the parameter through a `Nonempty`
field in a way the nested-occurrence checker won't unfold). Marking the
inductive `unsafe` "fixes" that error but then poisons every consumer:
any ordinary (`def`/`partial def`) code that touches the type is
rejected with `invalid declaration, it uses unsafe declaration` — which
would force `unsafe` through `repr`, `zonk`, and eventually `unify`,
`infer`, and the `march-lean-check` entry point itself. Both failure
modes were reproduced directly against this toolchain before choosing
the fix below.

The fix: `MTy.mvar` holds a `Nat` id, not a ref. The mutable union-find
cells live in one `IO.Ref (Array MVar)` *external* to the recursive
type — a `Supply` arena, addressed by id. This is the same technique
Lean's own elaborator uses for `Expr.mvar` (`MVarId` is a plain id;
the assignment lives in `MetavarContext`, not inside `Expr`). Semantics
are unchanged: `repr` still follows `link` chains and path-compresses
by overwriting the arena slot; `zonk` still deep-resolves. The
observable behavior the brief's `#eval`s check (repr resolves a link;
zonk resolves a nested link inside an arrow) is preserved exactly, only
addressed through `Supply` instead of a bare ref.

This means `freshMVar`, `repr`, and `zonk` all take an explicit
`Supply` argument (the arena), which the brief's signatures did not
have (no `IO.Ref` for `repr`/`zonk` to close over instead). Downstream
tasks (`unify` in Task 3, `generalize`/`instantiate` in Task 4, `infer`
in Task 5) will need to thread the same `Supply` through.
-/
namespace MarchLean.Infer
open MarchLean.Syntax

/-- Type-class constraints a metavariable may be required to satisfy
(numeric, equality, ordering). -/
inductive Class where | num | eq | ord
  deriving DecidableEq, Repr, Inhabited

mutual
  /-- Inference-time type. `mvar` holds the `Nat` id of a cell in a
  `Supply` arena (see the module doc for why this isn't a direct
  `IO.Ref`); the rest mirror `Syntax.Ty` plus `nat`/`natOp` for the
  numeric-literal / arithmetic fragment. -/
  inductive MTy where
    | mvar (id : Nat)
    | con (n : String) (args : List MTy)
    | arrow (a : MTy) (b : MTy)
    | tuple (ts : List MTy)
    | record (fs : List (String × MTy))
    | lin (l : Lin) (t : MTy)
    | nat (n : Nat)
    | natOp (op : String) (a : MTy) (b : MTy)
  /-- The contents of a metavariable cell: either still-unbound (with a
  fresh id, its binding level, and any class constraints), or `link`ed to
  a resolved type. -/
  inductive MVar where
    | unbound (id : Nat) (level : Nat) (classes : List Class)
    | link (t : MTy)
end

/-- Inference monad: errors short-circuit as `String`, effects (arena
reads/writes, fresh-id allocation) run in `IO`. -/
abbrev InferM := ExceptT String IO

/-- The mutable arena backing all metavariable cells for one inference
run, plus the fresh-id counter. `cells[id]` is the current contents of
metavariable `id`; `next` is the next id to hand out. Both are `IO.Ref`s
(per the design note: metavariables are backed by mutable refs), just
held once, outside the recursive `MTy`/`MVar` type, rather than one ref
per node (see module doc). -/
structure Supply where
  next  : IO.Ref Nat
  cells : IO.Ref (Array MVar)

/-- A fresh, empty arena. -/
def Supply.new : IO Supply := do
  pure { next := (← IO.mkRef 0), cells := (← IO.mkRef #[]) }

def freshId (s : Supply) : InferM Nat := do
  let n ← s.next.get
  s.next.set (n + 1)
  pure n

/-- Look up the current contents of metavariable `id`. -/
def getMVar (s : Supply) (id : Nat) : InferM MVar := do
  let arr ← s.cells.get
  match arr[id]? with
  | some v => pure v
  | none => throw s!"internal error: metavariable ?{id} not in arena"

/-- Overwrite the contents of metavariable `id` (used by `repr`'s path
compression, and later by `unify`'s binding step). -/
def setMVar (s : Supply) (id : Nat) (v : MVar) : InferM Unit :=
  s.cells.modify (fun arr => arr.set! id v)

/-- Allocate a fresh unbound metavariable at the given binding `level`,
optionally constrained by `classes`. -/
def freshMVar (s : Supply) (level : Nat) (classes : List Class := []) : InferM MTy := do
  let id ← freshId s
  s.cells.modify (fun arr => arr.push (MVar.unbound id level classes))
  pure (MTy.mvar id)

/-- Follow `link` chains, path-compressing as we go. Returns a non-`link`
head (either a solved `mvar` pointing at an `unbound` cell, or a concrete
node). -/
partial def repr (s : Supply) : MTy → InferM MTy
  | .mvar id => do
    match ← getMVar s id with
    | .link t =>
      let t' ← repr s t
      setMVar s id (.link t')
      pure t'
    | .unbound .. => pure (.mvar id)
  | t => pure t

/-- Deep-resolve every level. -/
partial def zonk (s : Supply) (t : MTy) : InferM MTy := do
  match ← repr s t with
  | .con n args => pure (.con n (← args.mapM (zonk s)))
  | .arrow a b => pure (.arrow (← zonk s a) (← zonk s b))
  | .tuple ts => pure (.tuple (← ts.mapM (zonk s)))
  | .record fs => pure (.record (← fs.mapM (fun (n, t) => do pure (n, ← zonk s t))))
  | .lin l t => pure (.lin l (← zonk s t))
  | .natOp op a b => pure (.natOp op (← zonk s a) (← zonk s b))
  | other => pure other   -- mvar(unbound), nat, con[] already handled

namespace Test
open MarchLean.Infer

-- repr follows a link chain to the target.
#eval show IO Unit from do
  let s ← Supply.new
  s.cells.modify (fun a => a.push (MVar.link (MTy.con "Int" [])))  -- id 0, already linked
  match ← (repr s (MTy.mvar 0)).run with
  | .ok (MTy.con "Int" []) => IO.println "repr-ok"
  | _ => IO.println "repr-FAIL"
-- expected: repr-ok

-- zonk resolves a solved arrow to a fully-linked structure.
#eval show IO Unit from do
  let s ← Supply.new
  s.cells.modify (fun a => a.push (MVar.link (MTy.con "Bool" [])))  -- id 0, already linked
  match ← (zonk s (MTy.arrow (MTy.mvar 0) (MTy.con "Int" []))).run with
  | .ok (MTy.arrow (MTy.con "Bool" []) (MTy.con "Int" [])) => IO.println "zonk-ok"
  | _ => IO.println "zonk-FAIL"
-- expected: zonk-ok

end Test
end MarchLean.Infer
