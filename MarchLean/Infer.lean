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
per node (see module doc).

**Single-`Supply` invariant.** An `MTy.mvar id` is only meaningful
relative to the `Supply` that minted it (i.e. whose `freshMVar`
allocated that `id`) — `id` is nothing but an index into that
`Supply`'s `cells` array. Looking it up against a *different* `Supply`
either throws (`getMVar`/`setMVar` report the index out of range) or,
worse, silently aliases an unrelated cell if the two arenas happen to
be large enough to both contain that index. Every function that
participates in one inference run — `repr`, `zonk`, `unify`, and the
later `generalize`/`instantiate`/`infer` — must thread the *same*
`Supply` value throughout. There is exactly one `Supply` per module
inference run; never mix `MTy`/`MVar` values minted from two different
`Supply`s. -/
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
compression, and later by `unify`'s binding step). Bounds-checked:
an out-of-range `id` `throw`s (mirroring `getMVar`'s explicit error)
rather than silently no-oping the way bare `Array.set!` would. -/
def setMVar (s : Supply) (id : Nat) (v : MVar) : InferM Unit := do
  let arr ← s.cells.get
  if id < arr.size then
    s.cells.set (arr.set! id v)
  else
    throw s!"internal error: metavariable ?{id} not in arena (setMVar)"

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

/-- `repr`, then peel off any top-level `.lin` qualifier(s), re-`repr`ing
underneath. `unify` never unifies the `.lin` qualifier itself — linearity
is owned entirely by the later Linearity pass — so every unify site
compares/binds against the *unwrapped* structural type, never a `.lin`
node. Looping (rather than a single peel) covers the (currently
unreachable, but cheap to make robust) case of a link resolving to
another `.lin`. -/
partial def reprUnwrap (s : Supply) (t : MTy) : InferM MTy := do
  match ← repr s t with
  | .lin _ t' => reprUnwrap s t'
  | t' => pure t'

/-- Occurs-check: does metavariable `id` occur anywhere inside `t`
(following links via `repr`)? As a side effect (standard HM level
management), every *other* unbound metavariable encountered along the
way has its level lowered to `≤ level` when it is currently higher —
this keeps generalization sound once `id` is bound at `level`.

The recursion is written explicitly (no `List.any`/`.map` shorthand):
each compound case recurses into every child and folds the results with
`||`, so the check genuinely returns `true` the moment `id` is found in
*any* branch, and otherwise (once all branches are explored) `false`. -/
partial def occursAndAdjust (s : Supply) (id : Nat) (level : Nat) (t : MTy) : InferM Bool := do
  match ← repr s t with
  | .mvar mid =>
    match ← getMVar s mid with
    | .unbound id2 lvl2 cs =>
      if id2 == id then
        pure true
      else do
        if lvl2 > level then setMVar s mid (.unbound id2 level cs)
        pure false
    | .link _ => pure false  -- unreachable: repr already followed links
  | .con _ args =>
    args.foldlM (fun found a => do
      if found then pure true else occursAndAdjust s id level a) false
  | .arrow a b => pure ((← occursAndAdjust s id level a) || (← occursAndAdjust s id level b))
  | .tuple ts =>
    ts.foldlM (fun found t => do
      if found then pure true else occursAndAdjust s id level t) false
  | .record fs =>
    fs.foldlM (fun found (_, t) => do
      if found then pure true else occursAndAdjust s id level t) false
  | .lin _ t => occursAndAdjust s id level t
  | .natOp _ a b => pure ((← occursAndAdjust s id level a) || (← occursAndAdjust s id level b))
  | .nat _ => pure false

/-- Bind unbound metavariable `id` (currently at `level`, with class
constraints `_classes`) to `t`, after an occurs-check. Constraint
(`Num`/`Eq`/`Ord`) propagation onto `t` is Task 4's job (the
generalize/instantiate constraint layer); here we only solve the
equality. -/
def bindMVar (s : Supply) (id : Nat) (level : Nat) (_classes : List Class) (t : MTy) : InferM Unit := do
  if ← occursAndAdjust s id level t then
    throw s!"occurs check failed: ?{id} occurs in its own solution"
  setMVar s id (.link t)

/-- Unify two inference types, destructively solving metavariables
(`setMVar s id (.link t)`) as it goes. Structural on `con`/`arrow`/
`tuple`/`record`/`nat`/`natOp`; a shape mismatch (different `con` name,
arity, tuple/record width, or record field name) `throw`s. Binding an
unbound metavariable runs the occurs-check first (`bindMVar`); an
occurs failure `throw`s rather than looping. The `.lin` qualifier is
*not* unified here — `reprUnwrap` strips it from both sides before the
structural match, since ownership of linearity belongs to the later
Linearity pass, not to type unification. -/
partial def unify (s : Supply) (a b : MTy) : InferM Unit := do
  let a ← reprUnwrap s a
  let b ← reprUnwrap s b
  match a, b with
  | .mvar id1, .mvar id2 =>
    if id1 == id2 then
      pure ()
    else
      match ← getMVar s id1 with
      | .unbound _ lvl1 cs1 => bindMVar s id1 lvl1 cs1 b
      | .link _ => throw s!"internal error: ?{id1} still linked after repr"
  | .mvar id, _ =>
    match ← getMVar s id with
    | .unbound _ lvl cs => bindMVar s id lvl cs b
    | .link _ => throw s!"internal error: ?{id} still linked after repr"
  | _, .mvar id =>
    match ← getMVar s id with
    | .unbound _ lvl cs => bindMVar s id lvl cs a
    | .link _ => throw s!"internal error: ?{id} still linked after repr"
  | .con n1 a1, .con n2 a2 =>
    if n1 != n2 || a1.length != a2.length then
      throw s!"cannot unify {n1} with {n2}"
    else
      (a1.zip a2).forM (fun (x, y) => unify s x y)
  | .arrow a1 b1, .arrow a2 b2 => do
    unify s a1 a2
    unify s b1 b2
  | .tuple t1, .tuple t2 =>
    if t1.length != t2.length then
      throw "cannot unify tuples of different arity"
    else
      (t1.zip t2).forM (fun (x, y) => unify s x y)
  | .record f1, .record f2 =>
    if f1.length != f2.length then
      throw "cannot unify records of different width"
    else
      (f1.zip f2).forM (fun ((n1, x), (n2, y)) =>
        if n1 != n2 then throw s!"record field mismatch: {n1} ≠ {n2}" else unify s x y)
  | .nat n1, .nat n2 =>
    if n1 == n2 then pure () else throw s!"cannot unify Nat literal {n1} with {n2}"
  | .natOp o1 a1 b1, .natOp o2 a2 b2 =>
    if o1 != o2 then
      throw s!"cannot unify natOp {o1} with {o2}"
    else do
      unify s a1 a2
      unify s b1 b2
  | _, _ => throw "type mismatch"

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

/-- Did `act` succeed (`.ok`)? Small `InferM Unit → IO Bool` probe used
by the `unify` tests below so each `#eval` can just print a boolean. -/
def runOk (act : InferM Unit) : IO Bool := do
  match ← act.run with
  | .ok _ => pure true
  | .error _ => pure false

-- unify: same nullary con succeeds.
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"int~int: {← runOk (unify s (MTy.con "Int" []) (MTy.con "Int" []))}"
-- expected: int~int: true

-- unify: different con names fail.
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"int~bool: {← runOk (unify s (MTy.con "Int" []) (MTy.con "Bool" []))}"
-- expected: int~bool: false

-- unify: `a ~ Int` binds `a`, and zonking `a` afterward yields `Int`.
#eval show IO Unit from do
  let s ← Supply.new
  match ← (do
      let a ← freshMVar s 0
      unify s a (MTy.con "Int" [])
      let z ← zonk s a
      pure (z matches MTy.con "Int" [])
    ).run with
  | .ok isInt => IO.println s!"var-bind: {isInt}"
  | .error e => IO.println s!"var-bind-ERROR: {e}"
-- expected: var-bind: true

-- unify: `a ~ (a -> b)` fails the occurs-check.
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"occurs: {← runOk (do
      let a ← freshMVar s 0
      let b ← freshMVar s 0
      unify s a (MTy.arrow a b))}"
-- expected: occurs: false

end Test
end MarchLean.Infer
