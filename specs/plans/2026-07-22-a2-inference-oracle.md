# A2 inference oracle — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Executes in the `march-lean` repo**, on a branch off `main`. Design doc:
> `specs/plans/2026-07-22-a2-inference-oracle-design.md` — read it first (esp.
> §2 architecture, §3 flow, §4 the up-to-equivalence comparison). The march
> emitter is **unchanged**; A2 consumes the existing `format_version` 2 output.
>
> **Base-branch note:** base off a `main` that includes march-lean #4 (the
> CI/readFile fix + A1 hardening). If #4 is not yet merged when execution
> starts, base off the `claude/a1-elaboration-checker` branch head (`c2b8edb`)
> instead, which has it.

**Goal:** Replace A1's "verify march's elaboration" checker with an independent Hindley–Milner inference engine that re-derives accept-side types from the bare AST and holds march to them — comparing both the verdict (inference must succeed) and per-node types (inferred vs `resolved_ty`, up-to-equivalence).

**Architecture:** A mutable-ref union-find HM engine (`MarchLean/Infer.lean`) infers types over the Core+linearity fragment; a thin up-to-equivalence comparison (`MarchLean/Compare.lean`) checks the inferred types against march's `resolved_ty` modulo metavariable renaming, defaulting, and record canonicalization. A1's `Check.lean` (annotation/witness verification) is retired; `Syntax`/`Elab`/`Linearity`/harness are reused.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.29.0`), `Lean.Data.Json`, Lake, mutable refs (`IO.Ref`). No Mathlib.

## Global Constraints

- **Independent inference:** the engine must NOT read march's `resolved_ty` or the `schemes`/`instantiations` witness tables as *inputs* — it derives types from the bare AST structure. `resolved_ty` is used ONLY as the per-node comparison target; the witness tables are ignored entirely.
- **Same fragment (Core+linearity), accept side only.** Reject-verdict files skip at the verdict gate (unchanged). Out-of-fragment constructs → whole-file skip (reuse `hasUnsupported`).
- **Exit contract unchanged:** 0=accept/agree, 1=MISMATCH, 2=skip, 3=error.
- **Two comparisons:** (a) inference must succeed on a march-accepted in-fragment file (failure ⇒ MISMATCH); (b) each node's inferred type must equal its `resolved_ty` up-to-equivalence (metavar renaming, defaulting, named-record canonicalization; structural disagreement ⇒ MISMATCH).
- **Mirror march's defaulting** (unresolved `Num`→`Int`, etc.) inside the engine so residual types line up with march's before comparison.
- **No Mathlib.** Build with EXPLICIT targets `lake build MarchLean march-lean-check` (bare `lake build` is a 0-job no-op in this repo).
- **Monad realization:** the design says "`ST.Ref`"; realize it with `IO.Ref` + `ExceptT String IO` since the `march-lean-check` pipeline is already `IO` and `#eval`/`main` run in `IO`. Same mutable-ref union-find technique; note this adaptation in reports.

---

## File Structure

- `MarchLean/Result.lean` — **create**: the shared `CheckResult` type + the salvaged `TyEnv`/`buildTyEnv`/`substTy`/`canon`/`numOk`/`ordOk` (moved out of the retiring `Check.lean` so `Linearity`, `Infer`, `Compare`, and `main` share one home).
- `MarchLean/Infer.lean` — **create**: `MTy` + metavar refs + `InferM` + `repr`/`zonk` + `unify` + `generalize`/`instantiate` + constraint solving/defaulting + `infer` over the fragment + datatype env.
- `MarchLean/Compare.lean` — **create**: the up-to-equivalence comparison (zonk vs `resolved_ty` with a metavar↔`TVar`-id bijection) + `inferModule : Module → CheckResult`.
- `MarchLean/Check.lean` — **delete** (Task 8): its verification logic is superseded; shared bits already moved to `Result.lean` in Task 1.
- `MarchLean/Linearity.lean` — **modify** (Task 1 only): import `Result` for `CheckResult` instead of `Check`.
- `MarchLeanCheck.lean` — **modify** (Task 8): call `Compare.inferModule` instead of `Check.checkModule`.
- `MarchLean.lean` — **modify**: aggregator imports `Result`/`Infer`/`Compare`, drops `Check`.
- `scripts/expected-skips.txt` — **regenerate** (Task 9) for A2's skip set.
- `scripts/conformance-harness.sh`, `.github/workflows/conformance.yml` — reused unchanged (A1 already handles the skip regime; CI already pinned to march `733e7a0b`).

Local test resources (present from A1): real emitted samples at `.superpowers/sdd/samples/*.json`; march v2 binary at `/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/_build/default/bin/main.exe`; corpus at `.../a1-emit-core-ast-v2/specs/lang/types`.

---

## Task 1: Salvage shared types into `Result.lean`

Pure refactor — no behavior change. Moves the shared result/helper code out of `Check.lean` so later tasks (which retire `Check`) have a stable home.

**Files:**
- Create: `MarchLean/Result.lean`
- Modify: `MarchLean/Check.lean` (import `Result`; delete the moved defs), `MarchLean/Linearity.lean` (import `Result`), `MarchLean.lean`

**Interfaces:**
- Produces: `MarchLean.Result.CheckResult` (`| ok | reject (msg : String) | skip (reason : String)`), `Result.TyEnv := List (String × (List String × List CtorSig))`, `Result.buildTyEnv : List Decl → TyEnv`, `Result.substTy : List (Int × Ty) → Ty → Ty`, `Result.canon : TyEnv → Ty → Ty`, `Result.numOk`/`Result.ordOk : TyEnv → Ty → Option (Sum String String)`.

- [ ] **Step 1: Create `MarchLean/Result.lean` by moving the shared defs**

Move these verbatim from `MarchLean/Check.lean` (they currently live there — `CheckResult` at line 76, `TyEnv`/`buildTyEnv`/`substTy`/`canon`/`tyEq`/`numOk`/`ordOk` at 94–191) into a new `MarchLean/Result.lean`:

```lean
import MarchLean.Syntax
namespace MarchLean.Result
open MarchLean.Syntax

inductive CheckResult where
  | ok
  | reject (msg : String)
  | skip (reason : String)
  deriving Repr

-- (paste TyEnv, buildTyEnv, substTy, canon, tyEq, numOk, ordOk verbatim from
--  Check.lean lines 94–191 — they depend only on Syntax, no other Check code.)

end MarchLean.Result
```

- [ ] **Step 2: Rewire `Check.lean` and `Linearity.lean` to import `Result`**

In `MarchLean/Check.lean`: add `import MarchLean.Result` and `open MarchLean.Result`, delete the moved defs (leaving `checkModule` + its `checkTerm`/`checkDecl`/`checkInstantiations` intact, now referencing `Result.CheckResult`/`canon`/etc.). In `MarchLean/Linearity.lean`: change `import MarchLean.Check` → `import MarchLean.Result` and `open MarchLean.Check` → `open MarchLean.Result` (it only used `CheckResult` from Check). Add `import MarchLean.Result` to `MarchLean.lean` (before `Check`/`Linearity`).

- [ ] **Step 3: Build to verify the refactor is green**

Run: `export PATH="$PATH:/Users/80197052/.elan/bin" && lake build MarchLean march-lean-check 2>&1 | tail -5`
Expected: clean build (pure code motion; every consumer now resolves `CheckResult` etc. from `Result`).

- [ ] **Step 4: Verify no behavior change via the samples**

Run: `for s in accept_poly accept_if_ord reject_int_str; do cat .superpowers/sdd/samples/$s.json | ./.lake/build/bin/march-lean-check; echo " $s=$?"; done`
Expected: `accept_poly=0 accept_if_ord=0 reject_int_str=2` (identical to A1 — the refactor changed nothing).

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Result.lean MarchLean/Check.lean MarchLean/Linearity.lean MarchLean.lean
git commit -m "refactor(marchlean): salvage CheckResult+canon into Result.lean (A2 Task 1)"
```

---

## Task 2: `MTy`, metavariables, `InferM`, `repr`/`zonk`

**Files:**
- Create: `MarchLean/Infer.lean`
- Modify: `MarchLean.lean` (add `import MarchLean.Infer`)

**Interfaces:**
- Consumes: `Syntax.Ty`, `Result.*`.
- Produces:
  - `Infer.Class := | num | eq | ord` (`deriving DecidableEq, Repr`).
  - `Infer.MVar` and `Infer.MTy` (mutually inductive): `MTy := | mvar (r : IO.Ref MVar) | con (n : String) (args : List MTy) | arrow (a b : MTy) | tuple (ts : List MTy) | record (fs : List (String × MTy)) | lin (l : Lin) (t : MTy) | nat (n : Nat) | natOp (op : String) (a b : MTy)`; `MVar := | unbound (id : Nat) (level : Nat) (classes : List Class) | link (t : MTy)`.
  - `Infer.InferM := ExceptT String IO` (α).
  - `Infer.Supply` — a fresh-id source; `Infer.freshMVar (level : Nat) (classes : List Class := []) : InferM MTy`.
  - `Infer.repr : MTy → InferM MTy` (follow links, path-compress).
  - `Infer.zonk : MTy → InferM MTy` (deep-`repr` the whole structure).

- [ ] **Step 1: Write the failing sanity examples**

At the bottom of the new `MarchLean/Infer.lean`, add `#eval` checks (living tests). Write them first:

```lean
namespace MarchLean.Infer.Test
open MarchLean.Infer

-- repr follows a link chain to the target.
#eval show IO Unit from do
  let r ← IO.mkRef (MVar.link (MTy.con "Int" []))
  match ← (repr (MTy.mvar r)).run with
  | .ok (MTy.con "Int" []) => IO.println "repr-ok"
  | _ => IO.println "repr-FAIL"
-- expected: repr-ok

-- zonk resolves a solved arrow to a fully-linked structure.
#eval show IO Unit from do
  let r ← IO.mkRef (MVar.link (MTy.con "Bool" []))
  match ← (zonk (MTy.arrow (MTy.mvar r) (MTy.con "Int" []))).run with
  | .ok (MTy.arrow (MTy.con "Bool" []) (MTy.con "Int" [])) => IO.println "zonk-ok"
  | _ => IO.println "zonk-FAIL"
-- expected: zonk-ok

end MarchLean.Infer.Test
```

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Infer 2>&1 | head -20`
Expected: FAIL — module/types don't exist.

- [ ] **Step 3: Implement the core**

Create `MarchLean/Infer.lean`:

```lean
import MarchLean.Syntax
import MarchLean.Result
namespace MarchLean.Infer
open MarchLean.Syntax

inductive Class where | num | eq | ord
  deriving DecidableEq, Repr, Inhabited

mutual
  inductive MTy where
    | mvar (r : IO.Ref MVar)
    | con (n : String) (args : List MTy)
    | arrow (a : MTy) (b : MTy)
    | tuple (ts : List MTy)
    | record (fs : List (String × MTy))
    | lin (l : Lin) (t : MTy)
    | nat (n : Nat)
    | natOp (op : String) (a : MTy) (b : MTy)
  inductive MVar where
    | unbound (id : Nat) (level : Nat) (classes : List Class)
    | link (t : MTy)
end

abbrev InferM := ExceptT String IO

/-- A monotonic fresh-id ref, created once per module inference. -/
abbrev Supply := IO.Ref Nat

def freshId (s : Supply) : InferM Nat := do
  let n ← s.get; s.set (n+1); pure n

def freshMVar (s : Supply) (level : Nat) (classes : List Class := []) : InferM MTy := do
  let id ← freshId s
  pure (MTy.mvar (← IO.mkRef (MVar.unbound id level classes)))

/-- Follow `link` chains, path-compressing as we go. Returns a non-`link`
head (either a solved `mvar` pointing at an `unbound`, or a concrete node). -/
partial def repr : MTy → InferM MTy
  | .mvar r => do
    match ← r.get with
    | .link t => let t' ← repr t; r.set (.link t'); pure t'
    | .unbound .. => pure (.mvar r)
  | t => pure t

/-- Deep-resolve every level. -/
partial def zonk (t : MTy) : InferM MTy := do
  match ← repr t with
  | .con n args => pure (.con n (← args.mapM zonk))
  | .arrow a b => pure (.arrow (← zonk a) (← zonk b))
  | .tuple ts => pure (.tuple (← ts.mapM zonk))
  | .record fs => pure (.record (← fs.mapM (fun (n, t) => do pure (n, ← zonk t))))
  | .lin l t => pure (.lin l (← zonk t))
  | .natOp op a b => pure (.natOp op (← zonk a) (← zonk b))
  | other => pure other   -- mvar(unbound), nat, con[] already handled
```

Add `import MarchLean.Infer` to `MarchLean.lean`.

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5`
Expected: clean; the two `#eval`s print `repr-ok` and `zonk-ok`.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Infer.lean MarchLean.lean
git commit -m "feat(infer): MTy + metavars + repr/zonk (A2 Task 2)"
```

---

## Task 3: `unify` + occurs-check

**Files:**
- Modify: `MarchLean/Infer.lean`

**Interfaces:**
- Consumes: `MTy`, `repr`, `MVar`.
- Produces: `Infer.unify : MTy → MTy → InferM Unit` — succeeds (`.ok ()`) on unifiable types, `throw`s a message on failure. Solves metavariables destructively (`r.set (.link …)`), with an occurs-check that also lowers levels.

- [ ] **Step 1: Write the failing tests**

Append to `Infer.Test`:

```lean
def runU (a b : MTy) : IO Bool := do
  match ← (unify a b).run with | .ok _ => pure true | .error _ => pure false

#eval do IO.println s!"int~int: {← runU (MTy.con \"Int\" []) (MTy.con \"Int\" [])}"      -- true
#eval do IO.println s!"int~bool: {← runU (MTy.con \"Int\" []) (MTy.con \"Bool\" [])}"     -- false
#eval do  -- a ~ Int binds a, then a is Int
  let s ← IO.mkRef 0
  IO.println s!"var-bind: {← (do let a ← freshMVar s 0; unify a (MTy.con \"Int\" []); let z ← zonk a; pure (z matches MTy.con \"Int\" [])).run |>.toBool?}"
#eval do  -- occurs: a ~ (a -> b) must fail
  let s ← IO.mkRef 0
  IO.println s!"occurs: {← (do let a ← freshMVar s 0; let b ← freshMVar s 0; unify a (MTy.arrow a b)).run |>.toBool?}"  -- false
```

(Use whatever small `toBool?`/`ExceptT`-inspection helper elaborates cleanly — the point is: int~int �so, int~bool ✗, var binds, occurs ✗. If the exact `#eval` plumbing is awkward, write a single `IO` test function returning a `List Bool` and assert it equals `[true, false, true, false]`.)

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Infer 2>&1 | head -20` — Expected: FAIL (`unify` undefined).

- [ ] **Step 3: Implement `unify`**

Add to `MarchLean/Infer.lean`:

```lean
/-- Occurs-check: does `id` occur in `t`? Also lower the level of every
unbound var in `t` to `≤ level` (standard HM level management). -/
partial def occursAndAdjust (id : Nat) (level : Nat) : MTy → InferM Bool
  | t => do
    match ← repr t with
    | .mvar r =>
      match ← r.get with
      | .unbound id2 lvl2 cs =>
        if id2 == id then pure true
        else do
          if lvl2 > level then r.set (.unbound id2 level cs)
          pure false
      | .link _ => pure false  -- repr already followed
    | .con _ args => (args.mapM (occursAndAdjust id level)).map (·.any id)
    | .arrow a b => pure ((← occursAndAdjust id level a) || (← occursAndAdjust id level b))
    | .tuple ts => (ts.mapM (occursAndAdjust id level)).map (·.any id)
    | .record fs => (fs.mapM (fun (_, t) => occursAndAdjust id level t)).map (·.any id)
    | .lin _ t => occursAndAdjust id level t
    | .natOp _ a b => pure ((← occursAndAdjust id level a) || (← occursAndAdjust id level b))
    | .nat _ => pure false

/-- Bind an unbound mvar `r` (id/level/classes) to `t` after occurs-check. -/
def bindMVar (r : IO.Ref MVar) (id : Nat) (level : Nat) (_classes : List Class) (t : MTy) : InferM Unit := do
  if ← occursAndAdjust id level t then throw s!"occurs check failed (var {id})"
  -- NOTE: constraint (Num/Eq/Ord) propagation onto `t` happens in Task 4's
  -- constraint layer; here we just solve the equality.
  r.set (.link t)

partial def unify (a b : MTy) : InferM Unit := do
  let a ← repr a; let b ← repr b
  match a, b with
  | .mvar r1, .mvar r2 =>
    match ← r1.get, ← r2.get with
    | .unbound id1 _ _, .unbound id2 _ _ => if id1 == id2 then pure () else r1.set (.link b)
    | _, _ => unify a b  -- one was actually a link; re-repr (shouldn't happen post-repr)
  | .mvar r, _ => match ← r.get with | .unbound id lvl cs => bindMVar r id lvl cs b | .link t => unify t b
  | _, .mvar r => match ← r.get with | .unbound id lvl cs => bindMVar r id lvl cs a | .link t => unify a t
  | .con n1 a1, .con n2 a2 =>
    if n1 != n2 || a1.length != a2.length then throw s!"cannot unify {n1} with {n2}"
    else (a1.zip a2).forM (fun (x, y) => unify x y)
  | .arrow a1 b1, .arrow a2 b2 => unify a1 a2; unify b1 b2
  | .tuple t1, .tuple t2 =>
    if t1.length != t2.length then throw "tuple arity mismatch"
    else (t1.zip t2).forM (fun (x, y) => unify x y)
  | .record f1, .record f2 =>
    if f1.length != f2.length then throw "record width mismatch"
    else (f1.zip f2).forM (fun ((n1,x),(n2,y)) => if n1 != n2 then throw s!"record field {n1}≠{n2}" else unify x y)
  | .lin _ t1, .lin _ t2 => unify t1 t2       -- linearity qualifier not unified here (Linearity pass owns it)
  | .lin _ t1, t2 => unify t1 t2
  | t1, .lin _ t2 => unify t1 t2
  | .nat n1, .nat n2 => if n1 == n2 then pure () else throw "nat mismatch"
  | .natOp o1 a1 b1, .natOp o2 a2 b2 => if o1 != o2 then throw "natop mismatch" else (do unify a1 a2; unify b1 b2)
  | _, _ => throw "type mismatch"
```

(The `List Bool → any id`-style helpers above are shorthand; implement the occurs recursion so it returns `true` if ANY branch found the id. A simple `foldl (· || ·) false` over recursive calls is fine.)

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5`
Expected: clean; the tests print `int~int: true`, `int~bool: false`, `var-bind: true`, `occurs: false`.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Infer.lean
git commit -m "feat(infer): unify + occurs-check (A2 Task 3)"
```

---

## Task 4: `generalize` / `instantiate` + constraint solving & defaulting

**Files:**
- Modify: `MarchLean/Infer.lean`

**Interfaces:**
- Consumes: `MTy`, `unify`, `repr`, `zonk`, `Class`, `freshMVar`.
- Produces:
  - `Infer.Scheme := { vars : List Nat, classes : List (Nat × Class), body : MTy }` (a generalized type; `vars` are the quantified metavar ids, `classes` records each quantified var's constraints).
  - `Infer.generalize (level : Nat) (t : MTy) : InferM Scheme` — quantifies unbound mvars with `level > current`.
  - `Infer.instantiate (s : Supply) (level : Nat) (sch : Scheme) : InferM MTy` — freshens quantified vars.
  - `Infer.defaultResiduals : MTy → InferM Unit` — resolve leftover `Num`/`Ord` mvars to `Int`/etc. per march's policy.
  - `Infer.requireClass (c : Class) (t : MTy) : InferM Unit` — assert a primitive class holds (used by `infer` for `Num`/`Eq`/`Ord` on operators); solves against primitives, records the class on a residual mvar, or throws on a definite violation (e.g. `Num Bool`).

- [ ] **Step 1: Write the failing tests**

Append to `Infer.Test`: (1) generalize `a→a` (fresh `a` at an inner level, then leave level) yields a `Scheme` with one quantified var; two `instantiate`s produce independent mvars, so unifying one instance at `Int` doesn't force the other. (2) `requireClass num (Int)` ok; `requireClass num (Bool)` throws. (3) a residual `Num` mvar after `defaultResiduals` zonks to `Int`.

```lean
#eval do  -- polymorphic identity instantiated twice stays independent
  let s ← IO.mkRef 0
  let r ← (do
    let a ← freshMVar s 1
    let sch ← generalize 0 (MTy.arrow a a)          -- level 0 outer; a is level 1 > 0 ⇒ quantified
    let i1 ← instantiate s 0 sch
    let i2 ← instantiate s 0 sch
    -- unify i1's domain with Int; i2 must stay unconstrained
    match i1 with
    | .arrow d1 _ => unify d1 (MTy.con "Int" [])
    | _ => throw "not arrow"
    let z2 ← zonk i2
    pure (z2 matches MTy.arrow (MTy.mvar _) _)       -- i2 domain still a var
  ).run
  IO.println s!"poly-indep: {r == .ok true}"          -- true

#eval do IO.println s!"num-int: {← runU2 (requireClass Class.num (MTy.con \"Int\" []))}"   -- true
#eval do IO.println s!"num-bool: {← runU2 (requireClass Class.num (MTy.con \"Bool\" []))}" -- false
```

(`runU2 : InferM Unit → IO Bool` runs and reports ok/err — write it like `runU`.)

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Infer 2>&1 | head -20` — Expected: FAIL.

- [ ] **Step 3: Implement generalization, instantiation, constraints, defaulting**

Key algorithm points (implement in `MarchLean/Infer.lean`), modeled on march's `typecheck.ml` (levels, NO value restriction — any binder generalizes, purely level-gated; `Poly (ids, constraints, ty)`):

- **`generalize level t`**: walk `zonk t`; collect every `unbound id lvl cs` with `lvl > level` into `vars` (dedup), record `(id, c)` for each class `c ∈ cs` into `classes`; the `body` is the zonked `t` (quantified vars stay as their mvars — `instantiate` maps by id). Return `{ vars, classes, body }`.
- **`instantiate s level sch`**: make a fresh mvar per `sch.vars` id (carrying that var's recorded classes), build a substitution `id ↦ freshmvar`, and rebuild `sch.body` replacing each quantified mvar by its fresh copy (match by id via `repr`). Non-quantified mvars are shared (passed through).
- **`requireClass c t`**: `repr t`; if a primitive (`con "Int"`/`"Float"`/`"String"` per the class — Num: Int/Float, Ord: Int/Float/String, Eq: any primitive), succeed; if an unbound mvar, add `c` to its `classes` (re-set the ref); if a definite non-primitive `con`/`arrow`/… → `throw` (this is how e.g. `Num Bool` becomes a MISMATCH); if still a var, leave the class recorded.
- **`defaultResiduals t`**: `zonk t`; for each residual unbound mvar still carrying a `Num`/`Ord`/`Eq` class and otherwise unconstrained, `unify` it with the march default (`Num`/`Ord`/`Eq` → `Int`, matching march's defaulting) so the residual form matches march's. (Run this at module end, before comparison — see Task 6.)

(Write the actual recursion for each; the dedup in `generalize` and the id-keyed substitution in `instantiate` are the load-bearing parts. A `List (Nat × MTy)` substitution looked up by the quantified var's id during a structural rebuild of `body` is sufficient.)

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5`
Expected: clean; `poly-indep: true`, `num-int: true`, `num-bool: false`.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Infer.lean
git commit -m "feat(infer): generalize/instantiate + constraints + defaulting (A2 Task 4)"
```

---

## Task 5: `infer` over the fragment

**Files:**
- Modify: `MarchLean/Infer.lean`

**Interfaces:**
- Consumes: everything above; `Syntax.Term`/`Decl`/`Lit`/`Pattern`/`CtorSig`.
- Produces:
  - `Infer.Ctx` — the inference context: the `Supply`, current `level`, a term-var environment `List (String × Either Scheme MTy)` (let-bound vars carry a `Scheme`; lambda/pattern-bound vars carry a monotype `MTy`), and a datatype environment `List (String × CtorSig)` (constructor name → signature) + record/type-param info built from `DType` decls.
  - `Infer.inferModule' : Module → InferM (List (Span × MTy))` — infers every decl, returning a list of `(node-span, inferred-MTy)` pairs for the comparison in Task 6, or `throw`ing on an inference failure. (The public `inferModule : Module → CheckResult` wrapper lives in Task 6 / `Compare.lean`.)

- [ ] **Step 1: Write the failing tests**

Append to `Infer.Test`: infer hand-built terms and the decoded real accept samples. The core cases (all must infer WITHOUT throwing): identity lambda `λx.x`; application `(λx.x) 1 : Int`; let-poly `let id = λx.x in (id 1, id true)`; an ADT `match`; a record + field access. Plus: decode each real accept sample via `Elab.decodeModule` and assert `inferModule'` returns `.ok` (does not throw) for the in-fragment ones.

```lean
#eval do  -- the real accept samples must all INFER (not throw)
  for name in ["accept_literals","accept_poly","accept_if_ord","accept_adt","accept_record","accept_linear_let","accept_linear_param"] do
    let txt ← IO.FS.readFile s!".superpowers/sdd/samples/{name}.json"
    match Lean.Json.parse txt >>= MarchLean.Elab.decodeModule with
    | .error e => IO.println s!"{name}: DECODE-ERR {e}"
    | .ok m =>
      match ← (inferModule' m).run with
      | .ok _ => IO.println s!"{name}: infer-ok"
      | .error e => IO.println s!"{name}: INFER-FAIL {e}"
```

**NOTE (build-time file reads):** these `IO.FS.readFile` `#eval`s read the gitignored `samples/` dir, which breaks a fresh CI checkout (this is exactly the bug A1 #4 fixed). So put the sample-driven checks in a SEPARATE scratch file you do NOT commit (or behind a guard), OR run them once locally and delete before commit. The COMMITTED tests must be the hand-built-term `#eval`s only (no `readFile`). The corpus run (Task 9) is the real sample-level gate.

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Infer 2>&1 | head -20` — Expected: FAIL (`inferModule'`/`Ctx` undefined).

- [ ] **Step 3: Implement `infer`**

Implement `infer : Ctx → Term → InferM MTy` with an explicit arm per `Term` constructor (NO `| _ =>` wildcard — an unhandled constructor must be impossible; the skip gate in Task 6 removes `unsupported` before inference runs, but `infer` should still `throw s!"infer: unexpected {…}"` on `.unsupported` defensively rather than silently succeed). Arms:
- `lit`: `Int`/`Float`/`String`/`Bool`/unit → the primitive `con`.
- `var name`: look up in the env; a `Scheme` ⇒ `instantiate`; a monotype ⇒ return it; unbound ⇒ `throw` (this becomes a MISMATCH).
- `app fn args`: infer `fn`; infer each arg; build a fresh result mvar `ρ`; `unify (fn's type) (args-types ⇢ ρ)` (an arrow chain); return `ρ`.
- `lam params body`: fresh mvar per param, bind into env (monotype), infer body `β`; return `params-types ⇢ β`.
- `let_ name _ rhs body`: `enter level`; infer `rhs`; `leave level`; `generalize` it; bind the scheme; infer `body`.
- `letfn name param _ fnBody body`: bind `name`'s recursive monotype, infer the `param→fnBody` arrow at an inner level, generalize, rebind, infer `body` (mirror march's `ELetFn`; if `ELetFn` never decodes in practice — A1 found it doesn't — a faithful arm is still required, just untested).
- `ite c t e`: `unify c Bool`; infer `t`, `e`; `unify` them; return that type.
- `con name args`: look up the ctor sig in the datatype env; instantiate its type params fresh; `unify` each declared arg type against the inferred arg; return the (instantiated) result type.
- `tuple es`: `tuple` of inferred elem types.
- `record fs`: `record` of `(name, inferred)` in the emitted field order.
- `field r name`: infer `r`; it must `repr` to a `record` (or a named `con` expanded via the datatype env) containing `name`; return that field's type; else `throw`.
- `match_ scrut arms`: infer `scrut`; for each arm, bind the pattern's variables (infer pattern types against the scrutinee type — a `Pattern.con` uses the ctor sig; `Pattern.var` binds a fresh monotype), infer the arm body, `unify` all arm bodies together; return that type.
- `unsupported`: `throw "infer: unsupported node (should have been skip-gated)"`.

For the operator classes (`+`, `<`, `==`): these appear as `var` callees whose scheme carries `Num`/`Ord`/`Eq`. Since A2 does its OWN inference, it needs primitive-operator signatures — build a small built-in environment mapping the primitive operator names march uses (verify the exact names from a decoded sample's `EVar` `name.txt` for `+`/`<`/`==`) to their schemes: `+ : ∀a. Num a ⇒ a→a→a`, `< : ∀a. Ord a ⇒ a→a→Bool`, `== : ∀a. Eq a ⇒ a→a→Bool`, etc. `requireClass` enforces the class at instantiation/use. (If an operator or stdlib name isn't in the built-in env and isn't a user binder, that's out of fragment ⇒ let it surface as an inference failure that Task 6 maps to skip, OR pre-gate it — see Task 6.)

`inferModule'` builds the datatype + built-in env from the module, then folds `infer` over each decl (a `dfn`/`dlet` binds its generalized type into the env for later decls), recording `(span, MTy)` for every expression node visited (thread a mutable `IO.Ref (List (Span × MTy))` accumulator, appending at each node with a span — `var`/`field` have their own span; other nodes: record under the node's position if available, else skip that node from the per-node compare). Call `defaultResiduals` on the recorded types at the end.

- [ ] **Step 4: Build + eval to verify it passes**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5` — clean; hand-built `#eval`s show the identity/app/let-poly/match/record cases infer without error. Then run the (uncommitted) sample check: all 7 accept samples print `infer-ok` (or a documented skip reason). If any prints `INFER-FAIL`, investigate before committing — it's either an engine gap (fix) or an out-of-fragment construct that Task 6's gate should catch first.

- [ ] **Step 5: Commit** (committed tests = hand-built terms only, no `readFile`)

```bash
git add MarchLean/Infer.lean
git commit -m "feat(infer): inference over the Core fragment (A2 Task 5)"
```

---

## Task 6: `Compare` (up-to-equivalence) + `inferModule`

**Files:**
- Create: `MarchLean/Compare.lean`
- Modify: `MarchLean.lean`

**Interfaces:**
- Consumes: `Infer.*`, `Result.*`, `Syntax.*`.
- Produces: `Compare.inferModule : Module → CheckResult` — the A2 replacement for A1's `Check.checkModule`, consumed by `MarchLeanCheck` (Task 7).

- [ ] **Step 1: Write the failing tests**

At the bottom of `MarchLean/Compare.lean`, add `#eval` synthetic cases (committed, no file reads): a module that infers and whose inferred types match `resolved_ty` up-to-renaming → `.ok`; a module whose one node's `resolved_ty` structurally contradicts the inferred type → `.reject`; a module with an `unsupported` decl → `.skip`; a module march accepted that fails inference (hand-build one that can't type) → `.reject`.

```lean
namespace MarchLean.Compare.Test
open MarchLean.Syntax MarchLean.Result MarchLean.Compare
-- (build small Module values; assert inferModule m matches .ok / .reject / .skip)
#eval ...  -- ok case
#eval ...  -- reject (type disagreement) case
#eval ...  -- skip (unsupported) case
end MarchLean.Compare.Test
```

- [ ] **Step 2: Run build to verify it fails**

Run: `lake build MarchLean.Compare 2>&1 | head -20` — Expected: FAIL.

- [ ] **Step 3: Implement the comparison + `inferModule`**

`MarchLean/Compare.lean`:
- **`eqvTy`** — the up-to-equivalence comparison of a zonked `Infer.MTy` against a decoded `Syntax.Ty`, threading a bijection state `IO.Ref (List (Nat × Int))` (Lean-mvar-id ↔ march-`TVar`-id): structural on `con`/`arrow`/`tuple`/`record`/`lin`/`nat`/`natOp`; a residual Lean `mvar id` vs a march `Ty.var mid` binds/consults the bijection (consistent ⇒ equal; conflict ⇒ not equal); apply `Result.canon` to the march side first (named-record expansion). A Lean `con "Foo"` vs march structural `record` (or vice versa) is reconciled by expanding the named record via the datatype env before comparing. A march `resolved_ty` of `Ty.unsupported`/`null`-decoded-as-`unsupported` on a node means "no cross-check target" ⇒ treat as equal (skip that node's compare; the verdict-level success already covers it).
- **`inferModule m`**:
  1. skip gate: `if m.decls.any Decl.hasUnsupported then return .skip …` (reuse Task-1 logic / `Decl.hasUnsupported`). Also skip if any scheme carries a non-`Num`/`Eq`/`Ord` `CInterface` (as A1).
  2. run `Infer.inferModule' m` in `IO`; on `throw` ⇒ `.reject s!"MISMATCH (infer): {e}"`.
  3. for each recorded `(span, mty)`, find the module node with that span and its `resolved_ty`; `eqvTy (← zonk mty) resolvedTy`; on disagreement ⇒ `.reject s!"MISMATCH (type) at {span}"`.
  4. `.ok`.
  (Linearity is run separately by `MarchLeanCheck` main, exactly as in A1 — not here.)

Because `Infer` runs in `ExceptT String IO` and `inferModule` must return a pure-ish `CheckResult`, `inferModule` itself is `IO CheckResult` (or `InferM CheckResult`); `MarchLeanCheck.run` is already `IO`, so this composes. State this signature choice in the report.

Add `import MarchLean.Compare` to `MarchLean.lean`.

- [ ] **Step 4: Build + eval**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5` — clean; the synthetic ok/reject/skip `#eval`s match.

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Compare.lean MarchLean.lean
git commit -m "feat(compare): up-to-equivalence cross-check + inferModule (A2 Task 6)"
```

---

## Task 7: Rewire `MarchLeanCheck` to `inferModule`; retire `Check`

**Files:**
- Modify: `MarchLeanCheck.lean`, `MarchLean.lean`
- Delete: `MarchLean/Check.lean`

**Interfaces:**
- Consumes: `Compare.inferModule`, `Linearity.checkLinearity`.

- [ ] **Step 1: Rewire `main`**

In `MarchLeanCheck.lean`, replace the `MarchLean.Check.checkModule m` call with `MarchLean.Compare.inferModule m` (now `IO CheckResult`, so `match ← MarchLean.Compare.inferModule m with …`). Keep the exact same result handling: `.skip r` ⇒ eprintln + `pure 2`; `.reject r` ⇒ eprintln + `pure 1`; `.ok` ⇒ run `Linearity.checkLinearity` then `.ok`⇒`pure 0` / `.skip`⇒`pure 2` / `.reject`⇒`pure 1`. Update imports (`import MarchLean.Compare`; drop `import MarchLean.Check`).

- [ ] **Step 2: Delete `Check.lean` and drop it from the aggregator**

```bash
git rm MarchLean/Check.lean
```
Remove `import MarchLean.Check` from `MarchLean.lean`. (Everything shared was moved to `Result.lean` in Task 1; nothing else should reference `Check`.) Grep to confirm: `grep -rn "MarchLean.Check\b" MarchLean* | grep -v Compare` → no hits.

- [ ] **Step 3: Build**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5` — Expected: clean (no dangling `Check` references).

- [ ] **Step 4: Verify exit codes on the real samples**

```bash
export PATH="$PATH:/Users/80197052/.elan/bin"
B=./.lake/build/bin/march-lean-check
for s in accept_literals accept_poly accept_if_ord accept_adt accept_record accept_linear_let accept_linear_param reject_int_str; do
  cat .superpowers/sdd/samples/$s.json | $B; echo " $s=$?"
done
printf 'not json' | $B; echo " malformed=$?"
printf '{"format_version":1,"verdict":"accept","module":{"decls":[]},"schemes":[],"instantiations":[]}' | $B; echo " v1=$?"
```
Expected: the 7 accept samples exit `0` (or a documented `2` skip if the engine legitimately can't model one — investigate any that do), `reject_int_str=2`, `malformed=3`, `v1=3`. Any accept sample exiting `1` (MISMATCH) must be triaged — it's the A2 signal (engine gap vs march quirk).

- [ ] **Step 5: Commit**

```bash
git add MarchLeanCheck.lean MarchLean.lean
git commit -m "feat(marchlean): route checker through the A2 inference oracle; retire Check (A2 Task 7)"
```

---

## Task 8: Corpus run, skip-ledger regen, forced-relaxation

**Files:**
- Modify: `scripts/expected-skips.txt` (regenerate for A2)
- (Harness `conformance-harness.sh` + `conformance.yml` reused unchanged.)

**Prerequisite:** march v2 binary built (present at the path in File Structure); `march-lean-check` built.

- [ ] **Step 1: Run the full corpus, record the A2 landscape**

```bash
cd /Users/80197052/code/march-lean/.claude/worktrees/<a2-worktree>
export PATH="$PATH:/Users/80197052/.elan/bin"
MARCH_BIN=/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/_build/default/bin/main.exe \
CORPUS_DIR=/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/specs/lang/types \
MARCH_LEAN_CHECK_BIN=./.lake/build/bin/march-lean-check \
  scripts/conformance-harness.sh || true
```
Record MATCH / MISMATCH / ERROR / SKIP counts. **This is the exploratory run** (design §5): a nonzero MISMATCH count is expected initial work, not a blocker.

- [ ] **Step 2: Triage every MISMATCH (the core of this task)**

For each accept file the checker MISMATCHes: pipe it through `march --emit-core-ast … | march-lean-check` and read the stderr message. Classify:
- **Spurious (representational):** the inferred and march types are equivalent but the comparison rejected them (defaulting not mirrored, metavar-renaming too strict, record not canonicalized). ⇒ fix `Infer.defaultResiduals`/`Compare.eqvTy` (a small engine/compare change + its own commit), re-run.
- **Engine gap:** Lean's `infer` genuinely can't type a construct march accepts (a fragment corner not modeled). ⇒ either extend `infer` (if in-fragment) or move the file to the skip-ledger with a recorded reason (if it relies on an out-of-fragment feature the whole-file gate should have caught — tighten the gate).
- **Genuine march quirk / bug:** inferred and march types really differ in a meaningful way. ⇒ record it as a finding in the task report (do NOT silence it); if it's a known-acceptable divergence, skip-ledger it with the reason.
Iterate until MISMATCH = 0 (every remaining divergence is either fixed or converted to a documented skip). Report the final disposition of each.

- [ ] **Step 3: Regenerate `scripts/expected-skips.txt` for A2**

From the final all-green run's observed accept-side skip set, regenerate `scripts/expected-skips.txt` (A2's skip set will differ from A1's — independent inference skips a different set than the annotation checker). One relative path per line + `# reason` comment. Confirm the harness's ledger check passes (observed == expected).

- [ ] **Step 4: Forced-relaxation acceptance test**

Prove the oracle can fail: temporarily break the engine or comparison so a currently-`ok` accept file MISMATCHes — e.g. in `unify`, make `con "Int"` unify with `con "Bool"` (delete the name check), OR in `eqvTy` make the metavar bijection always-equal. Rebuild `march-lean-check`, rerun the harness, confirm ≥1 MISMATCH + nonzero exit. Then revert (confirm `git diff` clean on the engine sources), rebuild, rerun, confirm all-green. Paste both summaries in the report. Do NOT commit the break.

- [ ] **Step 5: Commit**

```bash
git add scripts/expected-skips.txt
git commit -m "test(a2): regenerate skip-ledger + forced-relaxation for the inference oracle (A2 Task 8)"
```

---

## Done criteria (A2)

- `lake build MarchLean march-lean-check` green; committed `#eval`/tests pass (unify/generalize/instantiate/infer hand-built cases; compare synthetic ok/reject/skip). No committed test does `IO.FS.readFile` on the gitignored `samples/` dir.
- The checker runs its OWN inference (ignores `resolved_ty`/witnesses as inputs) and cross-checks against `resolved_ty` up-to-equivalence; `Check.lean` deleted.
- Full corpus: 0 MISMATCH / 0 ERROR over modeled accepts; every divergence surfaced by the exploratory run is either fixed or converted to a documented skip-ledger entry with a recorded reason.
- Forced-relaxation flips ≥1 accept to MISMATCH and reverts to green (evidence in the report).
- Exit contract unchanged (accept/agree→0, MISMATCH→1, skip→2, error→3); CI unchanged (pinned to march `733e7a0b`).
- Any genuine march divergences found during triage are recorded as findings in the final report.
