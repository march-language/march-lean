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
the actual substitution later, keyed by id. -/
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

end Test
end MarchLean.Infer
