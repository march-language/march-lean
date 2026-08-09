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
  deriving DecidableEq, BEq, Repr, Inhabited

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

/-! ## `generalize` / `instantiate` (let-polymorphism) and primitive
constraint solving (`Num`/`Eq`/`Ord`)

Modeled directly on march's own `lib/typecheck/typecheck.ml`
`generalize`/`instantiate`/`discharge_constraints` (§8, roughly lines
798–970 in the reference compiler at
`/Users/80197052/code/march/lib/typecheck/typecheck.ml`): level-based
generalization with **no value restriction** — any let/letfn/lambda
binder generalizes purely by comparing binding levels, never by
syntactic shape of the bound term. The one representational difference
from march's source is where class constraints live: march threads them
as a side list (`constraint_` values appended to
`env.pending_constraints`, discharged at each declaration boundary by
`discharge_constraints`), whereas this arena's `MVar.unbound` cell
already carries its own `classes : List Class` directly (a Task 2/3
decision, not revisited here). `generalize` simply reads that
per-cell list off into the `Scheme` instead of consulting a separate
list. -/

/-- A generalized type (march's `Poly (ids, cs, ty)`). `vars` are the
quantified metavariable ids — each still appears as `MTy.mvar id`
inside `body`; `instantiate` is what later replaces them, matching by
id. `classes` records, for every quantified id, each primitive class
(`Num`/`Eq`/`Ord`) that was on its arena cell at generalization time
(one `(id, c)` pair per class; an id with two classes appears twice). -/
structure Scheme where
  vars : List Nat
  classes : List (Nat × Class)
  body : MTy

/-- Walks `t` (assumed already `zonk`ed, so the only `mvar` case
reachable is an `unbound` cell — a `link` here would mean `zonk` failed
to resolve it, which cannot happen) accumulating `(idsSoFar,
classesSoFar)`: every unbound metavariable whose binding level is
strictly greater than `level` gets its id added to `idsSoFar` (skipped
if already present — this is `generalize`'s dedup) and its recorded
classes appended to `classesSoFar`. Threaded functionally (not via a
mutable ref, unlike march's OCaml `let ids = ref []`) since `InferM`
already gives us a clean way to carry the accumulator through the
`InferM`-monadic traversal. -/
partial def genCollect (s : Supply) (level : Nat)
    (acc : List Nat × List (Nat × Class)) (t : MTy) :
    InferM (List Nat × List (Nat × Class)) := do
  match t with
  | .mvar id => do
    match ← getMVar s id with
    | .unbound _ lvl cs =>
      if lvl > level then
        let (ids, classes) := acc
        if ids.contains id then
          pure acc
        else
          pure (id :: ids, (cs.map (fun c => (id, c))) ++ classes)
      else
        pure acc
    | .link _ => pure acc  -- unreachable: `t` is already zonked
  | .con _ args => args.foldlM (genCollect s level) acc
  | .arrow a b => do
    let acc ← genCollect s level acc a
    genCollect s level acc b
  | .tuple ts => ts.foldlM (genCollect s level) acc
  | .record fs => fs.foldlM (fun acc (_, t) => genCollect s level acc t) acc
  | .lin _ t => genCollect s level acc t
  | .natOp _ a b => do
    let acc ← genCollect s level acc a
    genCollect s level acc b
  | .nat _ => pure acc

/-- `generalize s level t`: zonk `t`, then quantify every unbound
metavariable whose binding level is strictly greater than `level`
(march's `generalize level ty` — called after leaving a
let/letfn-binding's level to achieve let-polymorphism; NO value
restriction, any binder generalizes). `body` is the zonked type with
quantified mvars left in place as `MTy.mvar id`; `instantiate` performs
the actual substitution later, keyed by id.

This function itself has no value restriction — but that does not mean the
checker as a whole lacks one: see `demoteToLevel0`, which is called BEFORE
`generalize` at a `cap_narrow` let-binding specifically to pin that binding's
result to level 0 so this very function's level check makes it
non-generalizable. Read the two together, not `generalize` alone, if the
question is "does this checker apply a value restriction anywhere". -/
def generalize (s : Supply) (level : Nat) (t : MTy) : InferM Scheme := do
  let zt ← zonk s t
  let (idsRev, classesRev) ← genCollect s level ([], []) zt
  pure { vars := idsRev.reverse, classes := classesRev.reverse, body := zt }

/-- Structural rebuild of `t`, replacing every quantified mvar (looked
up **by id** in `subst`, via `repr` so a since-solved cell is still
matched correctly) with its fresh instance; non-quantified mvars (not
in `subst`) pass through unchanged (shared with whatever else still
holds them — this is `instantiate`'s "non-quantified mvars are
shared" requirement). -/
partial def instSubst (s : Supply) (subst : List (Nat × MTy)) (t : MTy) : InferM MTy := do
  match ← repr s t with
  | .mvar id =>
    match subst.find? (fun p => p.1 == id) with
    | some (_, t') => pure t'
    | none => pure (.mvar id)
  | .con n args => pure (.con n (← args.mapM (instSubst s subst)))
  | .arrow a b => pure (.arrow (← instSubst s subst a) (← instSubst s subst b))
  | .tuple ts => pure (.tuple (← ts.mapM (instSubst s subst)))
  | .record fs => pure (.record (← fs.mapM (fun (n, t) => do pure (n, ← instSubst s subst t))))
  | .lin l t => pure (.lin l (← instSubst s subst t))
  | .natOp op a b => pure (.natOp op (← instSubst s subst a) (← instSubst s subst b))
  | other => pure other  -- nat literal / con[] already resolved by repr

/-- `instantiate s level sch`: allocate one fresh metavariable per
quantified id in `sch.vars` (at `level`, carrying forward that id's
recorded classes from `sch.classes`), then rebuild `sch.body`
substituting each quantified occurrence for its fresh copy
(`instSubst`, matched by id). Two calls with the same `sch` allocate
two disjoint sets of fresh cells, so unifying one instance never
affects the other (this is exactly what makes let-polymorphism sound:
`instantiate` is march's "make everything fresh again" step). -/
def instantiate (s : Supply) (level : Nat) (sch : Scheme) : InferM MTy := do
  let subst ← sch.vars.mapM (fun id => do
    let classes := (sch.classes.filter (fun p => p.1 == id)).map (·.2)
    let fresh ← freshMVar s level classes
    pure (id, fresh))
  instSubst s subst sch.body

/-- Human-readable class name, for `requireClass` error messages. -/
def className : Class → String
  | .num => "Num"
  | .eq => "Eq"
  | .ord => "Ord"

/-- Does the nullary primitive constructor named `n` satisfy class `c`?
Mirrors march's `builtin_impls` (`typecheck.ml` ~lines 1148–1160): `Num`
⇒ Int/Float; `Ord` ⇒ Int/Float/String; `Eq` ⇒ Int/Float/String/Bool
(march's real `Eq` impls also cover `Unit`/`Atom`, which this
simplified `MTy` fragment has no constructor for, so they're omitted
here — not a semantic gap, just nothing to model). -/
def primSatisfies (c : Class) (n : String) : Bool :=
  match c with
  | .num => n == "Int" || n == "Float"
  | .ord => n == "Int" || n == "Float" || n == "String"
  | .eq  => n == "Int" || n == "Float" || n == "String" || n == "Bool"

/-- Assert that `t` satisfies primitive class `c` (used by `infer` for
operators like `+`/`==`/`<`). `reprUnwrap`s first (matching `unify`'s
convention: a `.lin` qualifier is never itself examined by
type-level constraint checks — linearity is the later Linearity
pass's job). A nullary primitive `con` that satisfies `c`
(`primSatisfies`) succeeds silently; an unbound metavariable has `c`
recorded onto its arena cell (deferred — solved later, by a future
`unify` or by `defaultResiduals`); anything else definite — a
non-primitive `con` (with args), `arrow`, `tuple`, `record`, `nat`, or
`natOp` — is a MISMATCH and `throw`s (e.g. this is how `Num Bool`
fails). -/
partial def requireClass (s : Supply) (c : Class) (t : MTy) : InferM Unit := do
  match ← reprUnwrap s t with
  | .mvar id =>
    match ← getMVar s id with
    | .unbound id2 lvl cs =>
      if cs.contains c then
        pure ()
      else
        setMVar s id (.unbound id2 lvl (c :: cs))
    | .link _ => throw s!"internal error: ?{id} still linked after reprUnwrap"
  | .con n args =>
    if args.isEmpty && primSatisfies c n then
      pure ()
    else
      throw s!"`{n}` does not implement {className c}"
  | .arrow .. => throw s!"function type does not implement {className c}"
  | .tuple .. => throw s!"tuple type does not implement {className c}"
  | .record .. => throw s!"record type does not implement {className c}"
  | .nat _ => throw s!"Nat-literal type does not implement {className c}"
  | .natOp .. => throw s!"natOp type does not implement {className c}"
  | .lin .. => throw s!"internal error: reprUnwrap left a .lin qualifier"

/-- Walks `t` (assumed already `zonk`ed) defaulting residual
constrained metavariables. **March-faithfulness judgment call:** the
brief's literal wording ("resolve leftover `Num`/`Ord` mvars to
`Int`/etc.") would default every constrained class. The actual
reference compiler does not do this — its `discharge_constraints`
(`/Users/80197052/code/march/lib/typecheck/typecheck.ml:4953-4970`)
only defaults `CNum`: "`numeric defaulting: unresolved Num → Int`".
The `COrd` branch of that same match explicitly does the opposite —
`(* COrd unresolved — leave polymorphic *)`, i.e. `()`, no unification
— and the `CInterface` case (which is how march represents `Eq`; see
`typecheck.ml:1242-1243`, `("==", poly1_iface "Eq" ...)`) likewise just
returns `()` when the constrained type is still a bare type variable
("`Still polymorphic — cannot check yet`"). So only `Num` residuals are
defaulted here (to `Int`, matching march); `Ord`/`Eq` residuals are
left as unresolved metavariables, exactly like march leaves them
polymorphic. This is chosen over the brief's wording because Task 6
diffs Lean's output against march's actual computed types, and
defaulting `Ord`/`Eq` here would produce a residual form march never
produces. -/
partial def defaultWalk (s : Supply) (t : MTy) : InferM Unit := do
  match t with
  | .mvar id =>
    match ← getMVar s id with
    | .unbound _ _ cs =>
      if cs.contains Class.num then
        unify s (.mvar id) (MTy.con "Int" [])
      else
        pure ()
    | .link _ => pure ()  -- unreachable: `t` is already zonked
  | .con _ args => args.forM (defaultWalk s)
  | .arrow a b => do defaultWalk s a; defaultWalk s b
  | .tuple ts => ts.forM (defaultWalk s)
  | .record fs => fs.forM (fun (_, t) => defaultWalk s t)
  | .lin _ t => defaultWalk s t
  | .natOp _ a b => do defaultWalk s a; defaultWalk s b
  | .nat _ => pure ()

/-- `defaultResiduals s t`: zonk `t`, then default every residual `Num`
metavariable found anywhere inside it to `Int` (march's numeric
defaulting; see `defaultWalk`'s doc comment for why `Ord`/`Eq`
residuals are deliberately left untouched). Intended to run at module
end, before comparing against march's output (Task 6). -/
def defaultResiduals (s : Supply) (t : MTy) : InferM Unit := do
  let zt ← zonk s t
  defaultWalk s zt

/-! ## `infer` — Hindley–Milner inference over the whole Core fragment (Task 5)

The engine's payoff: `infer` walks a bare `Syntax.Term` (ignoring march's
`resolved_ty` annotations entirely — A2 re-derives types independently) and
produces an inferred `MTy` for each node, destructively solving
metavariables through `unify` as it goes. `inferModule'` sets up the
datatype + built-in-operator environment, folds `infer` over the module's
declarations, and returns the per-`var`/`field`-node `(Span × MTy)` records
that Task 6 (`Compare`) diffs against march's own computed types.

### Built-in operator/primitive environment

march encodes `+`/`<`/`==`/… and stdlib prelude functions as ordinary
variables carrying a scheme (`lib/typecheck/typecheck.ml:1195-1290`). Since
A2 does its own inference it needs the same signatures. The exact names and
types below are transcribed from that source (not guessed): arithmetic is
`Num`-constrained (`poly1_num`), ordering/equality use march's interface
constraints `Ord`/`Eq` (`poly1_iface`, which A2 models with `Class.ord`/
`Class.eq` — `primSatisfies` already matches march's Int/Float/String and
Int/Float/String/Bool impl sets), and the prelude conversions/`println` are
monomorphic. `Unit` is `TTuple []` in march (`t_unit = TTuple []`), so it's
`MTy.tuple []` here. A `var` whose name is neither a user binder nor a
built-in `throw`s — that surfaces as an inference failure Task 6 maps to a
skip (out of fragment), never a false accept.

### `SKIP:`-marked throws (Task 8b: coverage-gap vs. genuine-mismatch)

`Compare.inferModule` (Task 6/8b) needs to tell apart two different reasons
`infer` can fail on a march-accepted module: (a) the engine genuinely
disagrees with march about a type (a real `MISMATCH`), vs. (b) the engine
simply doesn't model some NAME or CONSTRUCT at all — an unbound identifier
(a stdlib/cross-module reference this fragment's `builtins` env doesn't
carry, e.g. `Array.empty`, `List.range`, a qualified `Module.member`) or an
unknown constructor (e.g. `None`, or any ADT ctor not decoded into
`ctx.ctors` — always a `DType` gap, never a march type error) — which is a
coverage gap, not a disagreement, and should `.skip` rather than falsely
`.reject`. The convention: a throw whose message is prefixed with the
literal marker `"SKIP: "` is a coverage gap; every other throw is a genuine
type error and stays a `MISMATCH`. Exactly three sites carry the marker —
the `var` arm's unbound-variable throw (`infer`) and the two unknown-
constructor throws (`inferPattern`'s `.con` arm, `infer`'s `.con` arm).
Every other throw in this file (unify mismatches, arity, occurs-check,
field-not-found, `requireClass` violations, internal-invariant throws)
is deliberately left unmarked — see each site's own doc comment. -/

/-- A term-variable environment entry: `let`/`dfn`-bound names carry a
generalized `Scheme` (instantiated fresh per use); lambda/pattern-bound
names carry a monotype `MTy` (shared across uses). -/
inductive EnvEntry where
  | scheme (sch : Scheme)
  | mono (t : MTy)

/-- The inference context threaded through `infer`. `term` is the
term-variable environment (most-recent binding first, so `find?` gives
shadowing for free); `ctors` maps every constructor name to its `CtorSig`
(built from the module's `DType` decls); `level` is the current binding
level (bumped when entering a `let`/`dfn` right-hand side, for level-based
generalization); `acc` accumulates `(span, MTy)` records for every
`var`/`field` node (the only `Term` nodes carrying a span); `pending`
collects `(class, mvar)` constraints raised at each scheme instantiation,
discharged at module end (mirroring march's `pending_constraints` /
`discharge_constraints` per-declaration constraint solving). -/
structure Ctx where
  term    : List (String × EnvEntry)
  ctors   : List (String × CtorSig)
  level   : Nat
  acc     : IO.Ref (List (Span × MTy))
  pending : IO.Ref (List (Class × MTy))

def Ctx.lookup (ctx : Ctx) (n : String) : Option EnvEntry :=
  (ctx.term.find? (fun p => p.1 == n)).map (·.2)

def Ctx.addMono (ctx : Ctx) (n : String) (t : MTy) : Ctx :=
  { ctx with term := (n, .mono t) :: ctx.term }

def Ctx.addScheme (ctx : Ctx) (n : String) (sch : Scheme) : Ctx :=
  { ctx with term := (n, .scheme sch) :: ctx.term }

/-- The `MTy` of a literal (march resolves value literals to their primitive
`TCon`; `Unit` is `TTuple []`). Shared by the `lit` term arm and the `lit`
pattern arm. -/
def litMTy : Lit → MTy
  | .int _   => .con "Int" []
  | .float _ => .con "Float" []
  | .str _   => .con "String" []
  | .bool _  => .con "Bool" []
  | .unit    => .tuple []

/-- Collect every `Ty.var` id appearing in a resolved type (a `DType`
constructor signature's type-parameter references). Written as an explicit
`foldl` accumulation rather than `flatMap` to avoid depending on a specific
core-library argument order. -/
partial def tyVars : Ty → List Int
  | .var i => [i]
  | .con _ args => args.foldl (fun acc t => acc ++ tyVars t) []
  | .arrow a b => tyVars a ++ tyVars b
  | .tuple ts => ts.foldl (fun acc t => acc ++ tyVars t) []
  | .record fs => fs.foldl (fun acc (_, t) => acc ++ tyVars t) []
  | .lin _ t => tyVars t
  | .natOp _ a b => tyVars a ++ tyVars b
  | .nat _ | .err | .unsupported => []

/-- Translate a `Syntax.Ty` (a `DType` ctor signature's declared type) into
an `MTy`, replacing each type-parameter `Ty.var i` with its fresh
metavariable from `subst`. `Ty.err`/`Ty.unsupported` `throw` — an
out-of-fragment ctor type must fail inference (Task 6 skip), never bind. -/
partial def tyToMTy (s : Supply) (subst : List (Int × MTy)) : Ty → InferM MTy
  | .con n args => do pure (.con n (← args.mapM (tyToMTy s subst)))
  | .arrow a b => do pure (.arrow (← tyToMTy s subst a) (← tyToMTy s subst b))
  | .tuple ts => do pure (.tuple (← ts.mapM (tyToMTy s subst)))
  | .record fs => do pure (.record (← fs.mapM (fun (n, t) => do pure (n, ← tyToMTy s subst t))))
  | .var i =>
    match subst.find? (fun p => p.1 == i) with
    | some (_, m) => pure m
    | none => throw s!"infer: constructor type references unbound type var {i}"
  | .lin l t => do pure (.lin l (← tyToMTy s subst t))
  | .nat n => pure (.nat n)
  | .natOp op a b => do pure (.natOp op (← tyToMTy s subst a) (← tyToMTy s subst b))
  | .err => throw "infer: constructor type contains a TError"
  | .unsupported => throw "infer: constructor type is out of fragment"

/-- Instantiate a constructor signature at `level`: allocate one fresh
metavariable per distinct type-parameter id used across the ctor's argument
and result types, then translate both under that substitution. Returns the
(fresh) declared argument types and the (fresh) result type — used by both
the `con` term arm (unify args, return result) and the `con` pattern arm
(unify result with the scrutinee, bind the arg patterns). -/
def instCtor (s : Supply) (level : Nat) (sig : CtorSig) : InferM (List MTy × MTy) := do
  let ids := (sig.argTys.foldl (fun acc t => acc ++ tyVars t) []) ++ tyVars sig.resultTy
  let idsU := ids.foldl (fun acc i => if acc.contains i then acc else acc ++ [i]) []
  let subst ← idsU.mapM (fun i => do pure (i, ← freshMVar s level))
  let argMTys ← sig.argTys.mapM (tyToMTy s subst)
  let resMTy ← tyToMTy s subst sig.resultTy
  pure (argMTys, resMTy)

/-- Like `instantiate`, but also registers each fresh class-constrained
metavariable onto `ctx.pending` so the constraint is discharged at module
end (march's `pending_constraints`). This is how operator class constraints
(`Num`/`Ord`/`Eq`) actually get *checked*: `unify`'s `bindMVar` deliberately
drops a cell's class list when solving it (that's the Linearity-pass-style
separation baked into Task 3), so a bare `unify` never rejects `Num Bool`.
Collecting the instantiated constrained mvars and re-running `requireClass`
on them after all unification (when they've been solved to concrete types)
recovers the check exactly where march performs it. -/
def instantiateRec (s : Supply) (ctx : Ctx) (sch : Scheme) : InferM MTy := do
  let subst ← sch.vars.mapM (fun id => do
    let classes := (sch.classes.filter (fun p => p.1 == id)).map (·.2)
    let fresh ← freshMVar s ctx.level classes
    for c in classes do ctx.pending.modify (fun l => (c, fresh) :: l)
    pure (id, fresh))
  instSubst s subst sch.body

/-- Infer the bindings a pattern introduces, unifying the pattern's implied
shape against the `expected` scrutinee/sub-term type. `Pattern.var` binds a
fresh monotype (the `expected` slot); `Pattern.con` looks up the ctor sig,
instantiates it fresh, unifies its result with `expected`, and recurses into
the argument patterns against the (fresh) declared argument types — an
unknown constructor name is a coverage gap, not a type error, so that throw
carries the `SKIP:` marker (see the module doc, "Task 8b"), routed by
`Compare.inferModule` to `.skip` rather than `.reject`; `Pattern.unsupported`
`throw`s (unmarked — defensively unreachable, already skip-gated upstream).
Returns the accumulated `(name, MTy)` bindings for the arm body's
environment. -/
partial def inferPattern (s : Supply) (ctx : Ctx) : Pattern → MTy → InferM (List (String × MTy))
  | .wild, _ => pure []
  | .var name _, expected => pure [(name, expected)]
  | .as name p, expected => do
      let b ← inferPattern s ctx p expected
      pure ((name, expected) :: b)
  | .lit l, expected => do
      unify s expected (litMTy l)
      pure []
  | .con name args, expected => do
      match ctx.ctors.find? (fun p => p.1 == name) with
      | none => throw s!"SKIP: unknown constructor pattern `{name}`"
      | some (_, sig) => do
        let (argMTys, resMTy) ← instCtor s ctx.level sig
        unify s expected resMTy
        if argMTys.length != args.length then
          throw s!"infer: constructor pattern `{name}` arity mismatch"
        let bindss ← (args.zip argMTys).mapM (fun (p, m) => inferPattern s ctx p m)
        pure (bindss.foldl (· ++ ·) [])
  | .tuple ps, expected => do
      let ms ← ps.mapM (fun _ => freshMVar s ctx.level)
      unify s expected (.tuple ms)
      let bindss ← (ps.zip ms).mapM (fun (p, m) => inferPattern s ctx p m)
      pure (bindss.foldl (· ++ ·) [])
  | .record fs, expected => do
      let fms ← fs.mapM (fun (n, p) => do pure (n, p, ← freshMVar s ctx.level))
      unify s expected (.record (fms.map (fun (n, _, m) => (n, m))))
      let bindss ← fms.mapM (fun (_, p, m) => inferPattern s ctx p m)
      pure (bindss.foldl (· ++ ·) [])
  | .or_ alts, expected => do
      -- march unifies every alternative's inferred type against a shared
      -- `expected` and merges their bindings (`typecheck.ml:3773`, `PatOr`),
      -- rejecting name/type disagreement between alternatives — a check this
      -- differential inference pass does not replicate (out of scope: it
      -- exists for `Compare`'s cross-check, not for diagnosing march's own
      -- pattern-binding errors). Unifying each alt against the same
      -- `expected` and concatenating bindings is enough for that purpose.
      let bindss ← alts.mapM (fun p => inferPattern s ctx p expected)
      pure (bindss.foldl (· ++ ·) [])
  | .unsupported, _ => throw "infer: unsupported pattern (should have been skip-gated)"

/-- Demote every unbound metavariable reachable in `t` to level 0, march's
`demote_to_monomorphic` (`typecheck.ml:4684-4694`). Used for the result of a
`cap_narrow(...)` application: because an application is expansive, its result
must never let-generalize. `generalize` only quantifies unbound vars whose
level is strictly greater than the level it generalizes at, so pinning them to
level 0 (the outermost, never-generalized level) keeps `let x = cap_narrow(e)`
monomorphic — its single use is the only thing that pins the cap var, exactly
like march. Mirrors `zonk`'s structural walk, `repr`-ing at every node so
nested mvars (e.g. the `X` in `Cap(X)`) are reached, not just the top one. -/
partial def demoteToLevel0 (s : Supply) (t : MTy) : InferM Unit := do
  match ← repr s t with
  | .mvar id => do
      match ← getMVar s id with
      | .unbound id' level classes =>
          if level > 0 then setMVar s id' (.unbound id' 0 classes)
      | .link t' => demoteToLevel0 s t'   -- unreachable after `repr`, but total
  | .con _ args => args.forM (demoteToLevel0 s)
  | .arrow a b => do demoteToLevel0 s a; demoteToLevel0 s b
  | .tuple ts => ts.forM (demoteToLevel0 s)
  | .record fs => fs.forM (fun (_, t) => demoteToLevel0 s t)
  | .lin _ t => demoteToLevel0 s t
  | .natOp _ a b => do demoteToLevel0 s a; demoteToLevel0 s b
  | .nat _ => pure ()

/-- Infer the type of a `Term`, threading the arena `s` and context `ctx`.
One explicit arm per constructor (no wildcard); `.unsupported` `throw`s
defensively (Task 6's gate removes such nodes before inference runs). Every
`var`/`field` node records `(span, its inferred MTy)` into `ctx.acc`. The
`var` arm's unbound-name throw and the `con` arm's unknown-constructor throw
carry the `SKIP:` marker (module doc, "Task 8b") — an unmodeled name/ctor is
a coverage gap, not a type disagreement, so `Compare.inferModule` routes it
to `.skip` instead of `.reject`. -/
partial def infer (s : Supply) (ctx : Ctx) : Term → InferM MTy
  | .lit l _ => pure (litMTy l)
  | .var name span _ => do
      match ctx.lookup name with
      | some (.scheme sch) => do
          let t ← instantiateRec s ctx sch
          ctx.acc.modify (fun l => (span, t) :: l)
          pure t
      | some (.mono t) => do
          ctx.acc.modify (fun l => (span, t) :: l)
          pure t
      | none => throw s!"SKIP: unbound variable `{name}`"
  | .app fn args _ => do
      let fnTy ← infer s ctx fn
      let argTys ← args.mapM (infer s ctx)
      let rho ← freshMVar s ctx.level
      unify s fnTy (argTys.foldr MTy.arrow rho)
      -- march's value restriction for `cap_narrow` (typecheck.ml:4684-4694,
      -- `demote_to_monomorphic`): a `cap_narrow(...)` application is
      -- expansive, so its result must never let-generalize. Demoting every
      -- metavariable reachable in `rho` to level 0 means the enclosing
      -- `let`'s `generalize` (which only quantifies vars whose level is
      -- strictly greater than the level it generalizes at) can never pick
      -- them up — the enclosing binder's one use is the only thing that
      -- ever pins the cap var, exactly like march. See `demoteToLevel0`.
      match fn with
      | .var "cap_narrow" _ _ => demoteToLevel0 s rho
      | _ => pure ()
      pure rho
  | .lam params body _ => do
      let paramMTys ← params.mapM (fun _ => freshMVar s ctx.level)
      -- Honor surface param annotations: an annotated binder HAS that type by
      -- definition (march-faithful), so fix its fresh mvar to the annotation;
      -- an unannotated param stays inferred. (`tyToMTy` under the empty subst —
      -- these top-level annotations reference no `DType` type parameters.)
      for ((_, _, annot), m) in params.zip paramMTys do
        match annot with
        | some t => unify s m (← tyToMTy s [] t)
        | none => pure ()
      let ctx' := (params.zip paramMTys).foldl (fun c ((n, _, _), m) => c.addMono n m) ctx
      let bTy ← infer s ctx' body
      pure (paramMTys.foldr MTy.arrow bTy)
  | .let_ name _ annot rhs body _ => do
      -- level-based let-polymorphism: infer the rhs one level deeper, then
      -- generalize back to the current level (any mvar minted at level+1 is
      -- quantified; `instantiate` makes fresh copies per use, so nothing
      -- later mutates the scheme's quantified vars — no generalize-aliasing).
      let rhsTy ← infer s { ctx with level := ctx.level + 1 } rhs
      -- march checks the rhs against a binding annotation (`let x : T = e`)
      -- before generalizing — unify here so the scheme is fixed to the
      -- annotated (possibly more-specific) type, not the rhs's general one.
      match annot with
      | some t => unify s rhsTy (← tyToMTy s [] t)
      | none => pure ()
      let sch ← generalize s ctx.level rhsTy
      infer s (ctx.addScheme name sch) body
  | .letfn name param _ paramAnnot fnBody body _ => do
      -- march's `ELetFn`: a recursive single-parameter function let. Never
      -- decodes in practice (A1 confirmed), so this arm is faithful but
      -- untested. Bind `name` recursively (fresh mvar) and `param` fresh at
      -- an inner level, infer the arrow, unify with the recursive mvar,
      -- generalize, then infer the body under the generalized scheme.
      let lvl := ctx.level + 1
      let recTy ← freshMVar s lvl
      let paramTy ← freshMVar s lvl
      match paramAnnot with
      | some t => unify s paramTy (← tyToMTy s [] t)
      | none => pure ()
      let ctxIn := (ctx.addMono name recTy).addMono param paramTy
      let fnBodyTy ← infer s { ctxIn with level := lvl } fnBody
      unify s recTy (.arrow paramTy fnBodyTy)
      let sch ← generalize s ctx.level recTy
      infer s (ctx.addScheme name sch) body
  | .ite c t e _ => do
      let ct ← infer s ctx c
      unify s ct (.con "Bool" [])
      let tt ← infer s ctx t
      let et ← infer s ctx e
      unify s tt et
      pure tt
  | .con name args _ => do
      match ctx.ctors.find? (fun p => p.1 == name) with
      | none => throw s!"SKIP: unknown constructor `{name}`"
      | some (_, sig) => do
        let (argMTys, resMTy) ← instCtor s ctx.level sig
        if argMTys.length != args.length then
          throw s!"infer: constructor `{name}` arity mismatch"
        let inferred ← args.mapM (infer s ctx)
        (argMTys.zip inferred).forM (fun (d, i) => unify s d i)
        pure resMTy
  | .tuple es _ => do pure (.tuple (← es.mapM (infer s ctx)))
  | .record fs _ => do
      let fs' ← fs.mapM (fun (n, e) => do pure (n, ← infer s ctx e))
      pure (.record fs')
  | .field r name span _ => do
      let rt ← infer s ctx r
      match ← reprUnwrap s rt with
      | .record fs =>
        match fs.find? (fun p => p.1 == name) with
        | some (_, ft) => do ctx.acc.modify (fun l => (span, ft) :: l); pure ft
        | none => throw s!"infer: record has no field `{name}`"
      | _ => throw s!"infer: field access `.{name}` on a non-record type"
  | .match_ scrut arms _ => do
      let scrutTy ← infer s ctx scrut
      let resTy ← freshMVar s ctx.level
      -- The guard (`Option Term`, A3 slice (c) Task 3) is evaluated in the
      -- pattern's own binder scope (`ctx'`, after `inferPattern`), and march
      -- REJECTS a non-`Bool` guard (verified directly:
      -- `reject/t10_guard_not_bool`'s `n when n + 1 -> ..` — "Match guards
      -- must be Bool. March does not coerce Int to Bool."). Unifying it
      -- against `Bool` here closes exactly that gap: without it, `t10` would
      -- newly ACCEPT once guards decode instead of forcing a whole-file skip
      -- (a live false accept this task's guard-decoding change would
      -- otherwise introduce), since nothing else in this checker inspects
      -- the guard's type.
      for (pat, guard, body) in arms do
        let binds ← inferPattern s ctx pat scrutTy
        let ctx' := binds.foldl (fun c (n, m) => c.addMono n m) ctx
        match guard with
        | some g => do
            let gt ← infer s ctx' g
            unify s gt (.con "Bool" [])
        | none => pure ()
        let bt ← infer s ctx' body
        unify s resTy bt
      pure resTy
  | .unsupported _ => throw "infer: unsupported node (should have been skip-gated)"

/-- Build one poly-1 scheme `∀a[:cls]. build a` by minting a fresh
metavariable for the quantified var (carrying its class), used for the
`Num`/`Ord`/`Eq` operator built-ins. -/
def mkPoly1 (s : Supply) (cls : List Class) (build : MTy → MTy) : InferM Scheme := do
  let a ← freshMVar s 0 cls
  let aid := match a with | .mvar i => i | _ => 0
  pure { vars := [aid], classes := cls.map (fun c => (aid, c)), body := build a }

/-- The built-in operator/prelude environment (see the section doc). Names
and signatures transcribed from march's `typecheck.ml` builtin env. -/
def builtins (s : Supply) : InferM (List (String × EnvEntry)) := do
  let i := MTy.con "Int" []
  let f := MTy.con "Float" []
  let b := MTy.con "Bool" []
  let str := MTy.con "String" []
  let u := MTy.tuple []
  let mono (n : String) (t : MTy) : String × EnvEntry := (n, .mono t)
  let arr := MTy.arrow
  -- Num-constrained arithmetic: ∀a:Num. a→a→a  (and negate: a→a)
  let mut out : List (String × EnvEntry) := []
  for name in ["+", "-", "*", "/"] do
    out := (name, .scheme (← mkPoly1 s [Class.num] (fun a => arr a (arr a a)))) :: out
  out := ("negate", .scheme (← mkPoly1 s [Class.num] (fun a => arr a a))) :: out
  -- Ord-constrained comparisons: ∀a:Ord. a→a→Bool
  for name in ["<", ">", "<=", ">="] do
    out := (name, .scheme (← mkPoly1 s [Class.ord] (fun a => arr a (arr a b)))) :: out
  -- Eq-constrained equality: ∀a:Eq. a→a→Bool
  for name in ["==", "!="] do
    out := (name, .scheme (← mkPoly1 s [Class.eq] (fun a => arr a (arr a b)))) :: out
  -- Capability-narrowing: ∀a b. Cap(a)→Cap(b)  (march main, R4a).
  --
  -- Was `∀a. Cap(IO)→Cap(a)`: the argument was LITERALLY the root, so a
  -- holder of anything narrower could not attenuate at all. march's R4a
  -- widened the type precisely to allow delegation-with-attenuation
  -- (`accept/t148_cap_narrow_chains`), which this checker rejected with
  -- "cannot unify IO with IO.FileSystem".
  --
  -- **The subsumption guarantee moved, it did not disappear.** Before R4a
  -- the argument type enforced it through unification; now nothing in the
  -- TYPE does, and `CapCheck.capNarrowViolation` carries it instead —
  -- mirroring march's own deferred `check_cap_narrow_sites` sweep
  -- (`typecheck.ml:9406-9432`). Retyping here WITHOUT that sweep would turn
  -- `reject/t153`/`t154`/`t155` into false accepts: those three reject today
  -- only as a side effect of this unification failure, not because anything
  -- checks the lattice. See `capNarrowViolation`'s docstring.
  let cap := fun (t : MTy) => MTy.con "Cap" [t]
  -- Still needed by `root_cap` below: R2 keeps the NAME bound at `Cap(IO)`
  -- (march does the same, `typecheck.ml:5118-5125`, so one mistake reports a
  -- single capability error instead of cascading unification failures);
  -- `CapCheck`'s R2 gate is what refuses references to it.
  let capIO := cap (MTy.con "IO" [])
  let capA ← freshMVar s 0 []
  let capB ← freshMVar s 0 []
  let aid := match capA with | .mvar i => i | _ => 0
  let bid := match capB with | .mvar i => i | _ => 0
  out := ("cap_narrow",
    .scheme { vars := [aid, bid], classes := [],
              body := arr (cap capA) (cap capB) }) :: out
  pure <| out ++ [
    -- The IO capability root, threaded from the entry point. (typecheck.ml:1971)
    mono "root_cap" capIO,
    -- Monomorphic operators / prelude functions.
    mono "%"  (arr i (arr i i)),
    mono "+." (arr f (arr f f)), mono "-." (arr f (arr f f)),
    mono "*." (arr f (arr f f)), mono "/." (arr f (arr f f)),
    mono "&&" (arr b (arr b b)), mono "||" (arr b (arr b b)),
    mono "not" (arr b b),
    mono "++" (arr str (arr str str)), mono "string_concat" (arr str (arr str str)),
    mono "string_length" (arr str i),
    mono "print" (arr str u), mono "println" (arr str u),
    mono "print_int" (arr i u), mono "print_float" (arr f u),
    mono "int_to_string" (arr i str), mono "float_to_string" (arr f str),
    mono "bool_to_string" (arr b str)
  ]

-- A `builtinCtorSigs` registration for `Option`/`Result`/`List` (so a bare
-- `Some`/`None`/`Ok`/`Err`/`Nil`/`Cons` resolves in `ctx.ctors` instead of
-- throwing the `"SKIP: unknown constructor"` coverage-gap marker) was tried
-- here and REVERTED (A3 slice (c) Task 3): it fixes `accept/t59`'s match, but
-- it also makes `println(None)`/`println(to_string(None))`
-- (`accept/t86_bare_none_unpinned`) reach unification against this checker's
-- monomorphic `println : String → ()` signature (this checker does not model
-- march's `Show` typeclass) — the None-as-Option now resolves, then fails to
-- unify with `String`, turning `t86`'s pre-existing SKIP (unresolved `None`)
-- into a live FALSE REJECT (march accepts `t86`; a `builtinCtorSigs`-carrying
-- checker rejects it, verified directly). Since Task 3's own non-negotiable
-- constraint is "no new false rejects", this checker keeps treating a match
-- over `Option`/`Result`/`List` as an inference-level SKIP rather than
-- resolving it — `accept/t59` (this task's own corpus target) stays exit 2
-- (skip), not exit 0, as a result; see the task report for the full account.
-- A real fix needs `println`/`print`/etc. modeled as polymorphic-over-`Show`
-- (or some other coverage-gap-safe treatment of builtin-ADT term/pattern
-- resolution), which is out of this task's scope.

/-- Infer every declaration of a module, returning the `(span, MTy)` record
for each `var`/`field` node (Task 6 diffs these against march's computed
types). Constructors from all `DType` decls are gathered first (so ctor
references resolve regardless of decl order); the built-in env seeds the
term environment; then `dfn`/`dlet` decls are folded in order, each binding
its generalized scheme for later decls. A `dfn` binds its own name
recursively (self-recursion); a `dlet` value binds non-recursively (march
value bindings aren't self-referential). At the end, pending class
constraints are discharged (`requireClass`) and residual `Num` mvars are
defaulted before zonking the recorded types. -/
def inferModule' (s : Supply) (m : Module) : InferM (List (Span × MTy)) := do
  let acc ← IO.mkRef ([] : List (Span × MTy))
  let pending ← IO.mkRef ([] : List (Class × MTy))
  let ctors := m.decls.foldl (fun cs d =>
    match d with
    | .dtype _ _ cts => cs ++ cts.map (fun c => (c.name, c))
    | _ => cs) []
  let bs ← builtins s
  let mut ctx : Ctx := { term := bs, ctors, level := 0, acc, pending }
  for d in m.decls do
    match d with
    | .dtype .. => pure ()
    -- A3 Task 2 decode-only constructors: no term of their own to infer.
    -- `dmod`'s nested decls are not walked here — Task 4's flattening
    -- (splicing them into this same loop) is what will make them visible
    -- to inference; until then they're simply not type-checked, same as
    -- any other not-yet-spliced-in scope.
    | .dmod .. | .dneeds .. | .duse .. | .dextern .. | .dproofcap .. | .dopts .. => pure ()
    | .dlet name rhs => do
        let t ← infer s { ctx with level := ctx.level + 1 } rhs
        let sch ← generalize s ctx.level t
        ctx := ctx.addScheme name sch
    | .dfn name params retAnnot body => do
        let lvl := ctx.level + 1
        let recTy ← freshMVar s lvl
        let paramMTys ← params.mapM (fun _ => freshMVar s lvl)
        -- Honor surface param annotations (see the `lam` arm): fix each
        -- annotated param's fresh mvar to its declared type.
        for ((_, _, annot), m) in params.zip paramMTys do
          match annot with
          | some t => unify s m (← tyToMTy s [] t)
          | none => pure ()
        let ctxIn := (params.zip paramMTys).foldl
          (fun c ((n, _, _), mt) => c.addMono n mt) (ctx.addMono name recTy)
        let bodyTy ← infer s { ctxIn with level := lvl } body
        -- Honor the surface RETURN annotation, exactly as the parameter
        -- annotations above are honored, and for the same reason: march
        -- CHECKS the body against the declared return type rather than
        -- inferring it freely, so an annotated return HAS that type by
        -- definition.
        --
        -- This used to be skipped ("inference derives the body's type and
        -- cross-checks resolved_ty, rather than trusting the annotation"),
        -- which was invisible while every builtin's result was pinned by its
        -- argument types. R4a broke that: `cap_narrow` is now `∀a b. Cap(a) →
        -- Cap(b)`, so in `pfn same_level(r : Cap(IO.FileRead)) :
        -- Cap(IO.FileRead) do cap_narrow(r) end` the result is pinned ONLY by
        -- the return annotation. Without this unification the body stays a
        -- metavariable, march resolves it to `Cap(IO.FileRead)`, and the
        -- per-node cross-check reports types_differ (exit 4) on
        -- `accept/t148_cap_narrow_chains`.
        match retAnnot with
        | some t => unify s bodyTy (← tyToMTy s [] t)
        | none   => pure ()
        unify s recTy (paramMTys.foldr MTy.arrow bodyTy)
        let sch ← generalize s ctx.level recTy
        ctx := ctx.addScheme name sch
    | .unsupported => throw "infer: unsupported declaration (should have been skip-gated)"
  -- Discharge pending class constraints against their now-solved mvars.
  let pend ← pending.get
  for (c, t) in pend do requireClass s c t
  -- Default residual Num mvars, then zonk each recorded node type.
  let recorded ← acc.get
  for (_, t) in recorded do defaultResiduals s t
  let out ← recorded.mapM (fun (sp, t) => do pure (sp, ← zonk s t))
  pure out.reverse

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

-- unify: tuples of different arity fail (coverage gap from Task 3).
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"tuple-arity: {← runOk (unify s
      (MTy.tuple [MTy.con "Int" []])
      (MTy.tuple [MTy.con "Int" [], MTy.con "Bool" []]))}"
-- expected: tuple-arity: false

-- unify: records with a mismatched field name fail (coverage gap from Task 3).
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"record-field: {← runOk (unify s
      (MTy.record [("x", MTy.con "Int" [])])
      (MTy.record [("y", MTy.con "Int" [])]))}"
-- expected: record-field: false

-- unify: natOp with mismatched op names fail (coverage gap from Task 3).
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"natop-mismatch: {← runOk (unify s
      (MTy.natOp "add" (MTy.nat 1) (MTy.nat 2))
      (MTy.natOp "mul" (MTy.nat 1) (MTy.nat 2)))}"
-- expected: natop-mismatch: false

-- generalize/instantiate: polymorphic identity instantiated twice stays
-- independent (unifying one instance's domain with Int must not force
-- the other instance).
#eval show IO Unit from do
  let s ← Supply.new
  match ← (do
      let a ← freshMVar s 1                       -- level 1, "inner" binding
      let sch ← generalize s 0 (MTy.arrow a a)     -- leave to level 0: a (lvl 1 > 0) ⇒ quantified
      let i1 ← instantiate s 0 sch
      let i2 ← instantiate s 0 sch
      match i1 with
      | .arrow d1 _ => unify s d1 (MTy.con "Int" [])
      | _ => throw "not arrow"
      let z2 ← zonk s i2
      pure (z2 matches MTy.arrow (MTy.mvar _) (MTy.mvar _))  -- i2 domain still unresolved
    ).run with
  | .ok r => IO.println s!"poly-indep: {r}"
  | .error e => IO.println s!"poly-indep-ERROR: {e}"
-- expected: poly-indep: true

-- requireClass: Num is satisfied by Int.
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"num-int: {← runOk (requireClass s Class.num (MTy.con "Int" []))}"
-- expected: num-int: true

-- requireClass: Num is violated by Bool (definite non-primitive w.r.t. Num).
#eval show IO Unit from do
  let s ← Supply.new
  IO.println s!"num-bool: {← runOk (requireClass s Class.num (MTy.con "Bool" []))}"
-- expected: num-bool: false

-- defaultResiduals: a residual Num mvar defaults to Int.
#eval show IO Unit from do
  let s ← Supply.new
  match ← (do
      let a ← freshMVar s 0 [Class.num]
      defaultResiduals s a
      let z ← zonk s a
      pure (z matches MTy.con "Int" [])
    ).run with
  | .ok isInt => IO.println s!"default-num: {isInt}"
  | .error e => IO.println s!"default-num-ERROR: {e}"
-- expected: default-num: true

-- defaultResiduals: march-faithfulness check — a residual Ord mvar does
-- NOT default (march's discharge_constraints leaves unresolved Ord/Eq
-- polymorphic; only Num defaults to Int). See the doc comment on
-- `defaultResiduals` for the source citation.
#eval show IO Unit from do
  let s ← Supply.new
  match ← (do
      let a ← freshMVar s 0 [Class.ord]
      defaultResiduals s a
      let z ← zonk s a
      pure (z matches MTy.mvar _)
    ).run with
  | .ok stillVar => IO.println s!"default-ord-stays-poly: {stillVar}"
  | .error e => IO.println s!"default-ord-ERROR: {e}"
-- expected: default-ord-stays-poly: true

/-! ### `infer` hand-built term tests (Task 5)

Committed tests use hand-built `Term`s only — no `IO.FS.readFile` of the
gitignored `samples/` dir (that broke fresh-checkout CI; see A1 #4). The
real-sample infer gate runs from the (uncommitted) conformance harness. -/

private def dSpan : Span := ⟨"t", 0, 0, 0, 0⟩
private def dTy : Ty := Ty.con "Int" []  -- filler; `infer` ignores the `ty` field
private def freshCtx (s : Supply) (ctors : List (String × CtorSig) := []) : IO Ctx := do
  pure { term := (← (builtins s).run).toOption.getD [], ctors, level := 0,
         acc := (← IO.mkRef []), pending := (← IO.mkRef []) }

/- Identity lambda `λx.x` infers to an arrow `?a → ?a` (same mvar both sides). -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let idLam := Term.lam [("x", .unrestricted, none)] (Term.var "x" dSpan dTy) dTy
  match ← (infer s ctx idLam).run with
  | .ok (.arrow (.mvar a) (.mvar b)) => IO.println s!"id-lam: {a == b}"
  | .ok _ => IO.println "id-lam-FAIL: wrong shape"
  | .error e => IO.println s!"id-lam-ERROR: {e}"
-- expected: id-lam: true

/- Surface annotation honored: `λ(x : Int). x` infers to the concrete
`Int → Int`, NOT the over-general `?a → ?a` — the param's annotation fixes
its type (march-faithful: an annotated binder HAS that type by definition).
This is the exact behavior the A2 corpus run found missing (t02/t21). -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let annLam := Term.lam [("x", .unrestricted, some (Ty.con "Int" []))]
    (Term.var "x" dSpan dTy) dTy
  match ← (do let t ← infer s ctx annLam; zonk s t).run with
  | .ok (.arrow (.con "Int" []) (.con "Int" [])) => IO.println "annot-lam: true"
  | .ok _ => IO.println "annot-lam-FAIL: wrong shape"
  | .error e => IO.println s!"annot-lam-ERROR: {e}"
-- expected: annot-lam: true

/- Annotation MISMATCH is a genuine inference failure: `λ(x : Int). x`
applied to a `Bool` literal cannot type — the annotation fixes `x : Int`, so
the argument unification `Int ~ Bool` `throw`s (this is precisely how the
honored annotation lets A2 reject what an over-general `?a → ?a` would have
wrongly accepted). -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let annLam := Term.lam [("x", .unrestricted, some (Ty.con "Int" []))]
    (Term.var "x" dSpan dTy) dTy
  let badApp := Term.app annLam [Term.lit (.bool true) dTy] dTy
  match ← (do let t ← infer s ctx badApp; zonk s t).run with
  | .ok _ => IO.println "annot-mismatch-FAIL: should not type"
  | .error _ => IO.println "annot-mismatch: true"
-- expected: annot-mismatch: true

/- Let annotation honored: `let f : Int = 5 in f` — the binding annotation
`Int` matches the rhs, and `f` records `Int`. (A binding whose annotation is
a strict instance of a polymorphic rhs is exercised end-to-end by the real
t21 sample through the conformance harness.) -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let letAnn := Term.let_ "f" .unrestricted (some (Ty.con "Int" []))
    (Term.lit (.int 5) dTy) (Term.var "f" dSpan dTy) dTy
  match ← (do let t ← infer s ctx letAnn; zonk s t).run with
  | .ok (.con "Int" []) => IO.println "annot-let: true"
  | .ok _ => IO.println "annot-let-FAIL: wrong shape"
  | .error e => IO.println s!"annot-let-ERROR: {e}"
-- expected: annot-let: true

/- Application `(λx.x) 1` infers to `Int`. -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let idLam := Term.lam [("x", .unrestricted, none)] (Term.var "x" dSpan dTy) dTy
  let app := Term.app idLam [Term.lit (.int 1) dTy] dTy
  match ← (do let t ← infer s ctx app; zonk s t).run with
  | .ok (.con "Int" []) => IO.println "app-int: true"
  | .ok _ => IO.println "app-int-FAIL: wrong shape"
  | .error e => IO.println s!"app-int-ERROR: {e}"
-- expected: app-int: true

/- Let-poly `let id = λx.x in (id 1, id true)` infers to `(Int, Bool)` —
`id` is used at two distinct types, which only typechecks if `let`
generalizes it. -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let idLam := Term.lam [("x", .unrestricted, none)] (Term.var "x" dSpan dTy) dTy
  let useInt := Term.app (Term.var "id" dSpan dTy) [Term.lit (.int 1) dTy] dTy
  let useBool := Term.app (Term.var "id" dSpan dTy) [Term.lit (.bool true) dTy] dTy
  let body := Term.tuple [useInt, useBool] dTy
  let letId := Term.let_ "id" .unrestricted none idLam body dTy
  match ← (do let t ← infer s ctx letId; zonk s t).run with
  | .ok (.tuple [.con "Int" [], .con "Bool" []]) => IO.println "let-poly: true"
  | .ok _ => IO.println "let-poly-FAIL: wrong shape"
  | .error e => IO.println s!"let-poly-ERROR: {e}"
-- expected: let-poly: true

/- ADT match: `match Red with Red => 1 | Green => 2` over `Color = Red | Green`
infers to `Int`. -/
#eval show IO Unit from do
  let s ← Supply.new
  let redSig : CtorSig := { name := "Red", argTys := [], resultTy := .con "Color" [] }
  let greenSig : CtorSig := { name := "Green", argTys := [], resultTy := .con "Color" [] }
  let ctx ← freshCtx s [("Red", redSig), ("Green", greenSig)]
  let m := Term.match_ (Term.con "Red" [] dTy)
    [(Pattern.con "Red" [], none, Term.lit (.int 1) dTy),
     (Pattern.con "Green" [], none, Term.lit (.int 2) dTy)] dTy
  match ← (do let t ← infer s ctx m; zonk s t).run with
  | .ok (.con "Int" []) => IO.println "adt-match: true"
  | .ok _ => IO.println "adt-match-FAIL: wrong shape"
  | .error e => IO.println s!"adt-match-ERROR: {e}"
-- expected: adt-match: true

/- ADT match with a constructor argument binder: `Box(a) = Box(a)`,
`match Box(1) with Box(n) => n` infers to `Int` (the bound `n` has the
constructor's instantiated argument type). -/
#eval show IO Unit from do
  let s ← Supply.new
  let boxSig : CtorSig := { name := "Box", argTys := [.var 0], resultTy := .con "Box" [.var 0] }
  let ctx ← freshCtx s [("Box", boxSig)]
  let m := Term.match_ (Term.con "Box" [Term.lit (.int 1) dTy] dTy)
    [(Pattern.con "Box" [Pattern.var "n" .unrestricted], none, Term.var "n" dSpan dTy)] dTy
  match ← (do let t ← infer s ctx m; zonk s t).run with
  | .ok (.con "Int" []) => IO.println "adt-bind: true"
  | .ok _ => IO.println "adt-bind-FAIL: wrong shape"
  | .error e => IO.println s!"adt-bind-ERROR: {e}"
-- expected: adt-bind: true

/- Record + field access: `{x = 1, y = "hi"}.x` infers to `Int`. -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let recd := Term.record [("x", Term.lit (.int 1) dTy), ("y", Term.lit (.str "hi") dTy)] dTy
  let fld := Term.field recd "x" dSpan dTy
  match ← (do let t ← infer s ctx fld; zonk s t).run with
  | .ok (.con "Int" []) => IO.println "record-field: true"
  | .ok _ => IO.println "record-field-FAIL: wrong shape"
  | .error e => IO.println s!"record-field-ERROR: {e}"
-- expected: record-field: true

/- Operator built-in with class enforcement: `1 + 2` infers to `Int`, and
the pending `Num` constraint discharged via a module-style flow succeeds
(Num Int). Modeled as a mini `dlet` so `inferModule'`'s discharge runs. -/
#eval show IO Unit from do
  let s ← Supply.new
  let plus := Term.app (Term.var "+" dSpan dTy)
    [Term.lit (.int 1) dTy, Term.lit (.int 2) dTy] dTy
  let m : Module := { decls := [.dlet "r" plus], schemes := [], insts := [] }
  match ← (inferModule' s m).run with
  | .ok _ => IO.println "op-num-ok: true"
  | .error e => IO.println s!"op-num-ok-FAIL: {e}"
-- expected: op-num-ok: true

/- Capability-narrowing builtins (A3 slice b, Task 1): a module-level
`fn boot(root : Cap(IO)) : Cap(IO.Network) do cap_narrow(root) end` infers
with no unbound-variable throw for `cap_narrow`/`root_cap`. Modeled as a
`dfn` run through `inferModule'`, exactly like `op-num-ok` above. -/
#eval show IO Unit from do
  let s ← Supply.new
  let capIO : Ty := Ty.con "Cap" [Ty.con "IO" []]
  let capNet : Ty := Ty.con "Cap" [Ty.con "IO.Network" []]
  let boot : Decl := .dfn "boot" [("root", .unrestricted, some capIO)] (some capNet)
    (Term.app (Term.var "cap_narrow" dSpan dTy) [Term.var "root" dSpan dTy] dTy)
  let m : Module := { decls := [boot], schemes := [], insts := [] }
  match ← (inferModule' s m).run with
  | .ok _ => IO.println "cap-narrow-module-ok: true"
  | .error e => IO.println s!"cap-narrow-module-FAIL: {e}"
-- expected: cap-narrow-module-ok: true

/- Same shape as above, but checking that `cap_narrow`'s polymorphic result
actually unifies with the `Cap(IO.Network)` return annotation (`inferModule'`
ignores `retAnnot`, so this unify is done explicitly here — see its doc
comment above `.dfn`'s case). `λ(root : Cap(IO)). cap_narrow(root)` infers to
`Cap(IO) → ?a`; unifying `?a` with `Cap(IO.Network)` and zonking must yield
exactly `Cap(IO) → Cap(IO.Network)`. -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let capIO : Ty := Ty.con "Cap" [Ty.con "IO" []]
  let boot := Term.lam [("root", .unrestricted, some capIO)]
    (Term.app (Term.var "cap_narrow" dSpan dTy) [Term.var "root" dSpan dTy] dTy) dTy
  match ← (do
      let t ← infer s ctx boot
      let bodyTy := match t with | .arrow _ r => r | other => other
      let retMTy ← tyToMTy s [] (Ty.con "Cap" [Ty.con "IO.Network" []])
      unify s bodyTy retMTy
      zonk s t
    ).run with
  | .ok (.arrow (.con "Cap" [.con "IO" []]) (.con "Cap" [.con "IO.Network" []])) =>
      IO.println "cap-narrow-unify-ok: true"
  | .ok _ => IO.println "cap-narrow-unify-FAIL: wrong shape"
  | .error e => IO.println s!"cap-narrow-unify-ERROR: {e}"
-- expected: cap-narrow-unify-ok: true

/- VALUE RESTRICTION — the discriminating test for `demoteToLevel0`.

`let net = cap_narrow(root) in (net, net)` must make `net` MONOMORPHIC: both
uses share one metavariable, so unifying the first component with
`Cap(IO.Network)` and the second with `Cap(IO.Console)` must FAIL.

Without the demotion `net` would let-generalize to `∀a. Cap(a)`, each use
would instantiate its own fresh var, and BOTH unifications would wrongly
succeed. A single-use body cannot tell the two apart (one use instantiates
once either way), which is why this test binds two uses. Verified to have
teeth: stubbing out the `demoteToLevel0` call makes this print FALSE.
march rejects the same program for the same reason (typecheck.ml:4684). -/
#eval show IO Unit from do
  let s ← Supply.new
  let ctx ← freshCtx s
  let capIO : Ty := Ty.con "Cap" [Ty.con "IO" []]
  let netUse := Term.var "net" dSpan dTy
  let boot := Term.lam [("root", .unrestricted, some capIO)]
    (Term.let_ "net" .unrestricted none
      (Term.app (Term.var "cap_narrow" dSpan dTy) [Term.var "root" dSpan dTy] dTy)
      (Term.tuple [netUse, netUse] dTy) dTy) dTy
  match ← (do
      let t ← infer s ctx boot
      let tupTy := match t with | .arrow _ r => r | other => other
      let (a, b) := match tupTy with
        | .tuple [x, y] => (x, y)
        | other => (other, other)
      unify s a (← tyToMTy s [] (Ty.con "Cap" [Ty.con "IO.Network" []]))
      unify s b (← tyToMTy s [] (Ty.con "Cap" [Ty.con "IO.Console" []]))
    ).run with
  | .error _ => IO.println "value-restriction-ok: true"
  | .ok _    => IO.println "value-restriction-ok: FALSE (net wrongly polymorphic)"
-- expected: value-restriction-ok: true

end Test
end MarchLean.Infer
