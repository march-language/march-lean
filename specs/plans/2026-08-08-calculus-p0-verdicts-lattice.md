# Calculus P0 — Verdict Algebra + Lattice Metatheory Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land phases P0a + P0b of `specs/plans/2026-08-08-calculus-proof-capabilities-design.md`: kernel-checked theorems for the verdict algebra (`CapResult.andThen`, `DivVerdict.join`) and the capability lattice (parameterized over an abstract table, with march's 20-entry table discharged by `decide`).

**Architecture:** Three new files — `MarchLean/Calculus/Verdicts.lean` (verdict algebra, purely additive), `MarchLean/Calculus/Lattice.lean` (abstract table defs + metatheory), `MarchLean/Calculus/Concrete.lean` (`WellFormedB hierarchy` by `decide` + shipping-name corollaries). One API-preserving refactor: `MarchLean/CapLattice.lean`'s five defs become specializations of the abstract ones. One CI edit: a sorry/admit grep.

**Tech Stack:** Lean 4 (toolchain `leanprover/lean4:v4.29.0`, pinned in `lean-toolchain`), no dependencies (no mathlib — core `List.Perm`/`List.IsSuffix`/`List.Nodup` are available and sufficient; verified against this toolchain). Build: `lake build` with `lake` at `~/.elan/bin/lake` (not in default PATH — every shell snippet below exports it). Conformance: `scripts/conformance-harness.sh` with local `march` 0.2.0 (`~/.opam/march/bin/march`) and corpus `~/code/march/specs/lang/types` (122 accept + 120 reject).

## Global Constraints

- **No mathlib, no new dependencies.** `lake-manifest.json` stays `"packages": []`.
- **API preservation (design §2):** `capParent`, `capAncestorsFuel`, `capAncestors`, `capSubsumes`, `normalize`, `hierarchy` keep their exact names, signatures, and results. No call site outside `CapLattice.lean` changes.
- **No `sorry`/`admit` in committed code.** Intermediate build checks may use `sorry` to validate statements elaborate; every commit is sorry-free.
- **Theorem-statement fidelity:** later plans (P2) consume these exact names — do not rename while proving. If a statement turns out false as written, STOP and report (that is a design finding, not a proof obstacle to engineer around).
- **Repo proof idiom:** theorems and their `example` smoke tests live in the same file they concern (matches existing inline-`#eval`/`example` convention). No separate test directory exists or is created.
- **Build command everywhere:** `export PATH="$HOME/.elan/bin:$PATH" && lake build` from the repo root. A clean build with zero warnings on new files is the pass criterion (`sorry` is a *warning* in Lean — read the output, don't trust exit 0 alone).

## Baseline (already verified in this worktree, 2026-08-08)

- `lake build march-lean-check` — green, 22 jobs.
- Kernel `decide` proves the 20-entry `WellFormedB hierarchy` probe in ~0.5s — plain `decide` is viable for Task 7; `native_decide` fallback should NOT be needed.
- Core has `List.Perm` (with decidable instances), `List.IsSuffix` (`<:+`), `List.Nodup`, `List.filter_subset`. Core does NOT have `List.isSuffix_iff` or `List.mem_of_mem_filter` under those names — use `List.mem_filter` and manual suffix reasoning.

---

### Task 1: Corpus baseline + `Calculus/Verdicts.lean` — `CapResult` algebra

**Files:**
- Create: `MarchLean/Calculus/Verdicts.lean`
- Modify: `MarchLean.lean` (add `import MarchLean.Calculus.Verdicts` at the end)

**Interfaces:**
- Consumes: `MarchLean.CapCheck.CapResult` (`ok | violation (msg) | skip (reason)`), `CapResult.andThen` (`MarchLean/CapCheck.lean:39-62`, namespace `MarchLean.CapCheck`).
- Produces (P2 depends on these exact names, all in namespace `MarchLean.Calculus`):
  - `inductive Tier | ok | skip | violation` (`DecidableEq, Repr`)
  - `Tier.max : Tier → Tier → Tier`
  - `tierOf : CapResult → Tier`
  - `theorem ok_andThen (r : CapResult) : CapResult.ok.andThen r = r`
  - `theorem andThen_ok (r : CapResult) : r.andThen .ok = r`
  - `theorem violation_andThen (m : String) (r : CapResult) : (CapResult.violation m).andThen r = .violation m`
  - `theorem andThen_assoc (a b c : CapResult) : (a.andThen b).andThen c = a.andThen (b.andThen c)`
  - `theorem Tier.max_comm / max_assoc / max_idem / ok_max / max_ok`
  - `theorem tierOf_andThen (a b : CapResult) : tierOf (a.andThen b) = (tierOf a).max (tierOf b)`
  - `theorem tierOf_andThen_comm (a b : CapResult) : tierOf (a.andThen b) = tierOf (b.andThen a)`

- [ ] **Step 1: Record the conformance baseline (pre-change, one time for the whole plan)**

```bash
export PATH="$HOME/.elan/bin:$PATH" && cd "$(git rev-parse --show-toplevel)" && \
lake build march-lean-check && \
MARCH_BIN="$HOME/.opam/march/bin/march" \
CORPUS_DIR="$HOME/code/march/specs/lang/types" \
MARCH_LEAN_CHECK_BIN=.lake/build/bin/march-lean-check \
scripts/conformance-harness.sh > /tmp/p0-corpus-baseline.txt 2>&1; \
echo "exit=$?" >> /tmp/p0-corpus-baseline.txt; tail -20 /tmp/p0-corpus-baseline.txt
```

Note: the local `march` may not be at CI's pinned SHA, so the ledger check may fail here — that is fine. **The invariant this plan enforces is that this output is byte-identical before and after every shipping-code change**, not that the local run is green.

- [ ] **Step 2: Write the failing statements**

Create `MarchLean/Calculus/Verdicts.lean` with every theorem stated and proved by `sorry`:

```lean
/-!
# Verdict algebra

Kernel-checked laws for the two verdict-combination operators the capability
checker folds with: `CapResult.andThen` (`CapCheck.lean`) and
`DivVerdict.join`. What is proved and what is deliberately NOT:

- `andThen` is associative with identity `ok`; `violation` left-absorbs. It
  is NOT commutative — messages are leftmost-wins by design — but the tier
  projection (`tierOf`) IS: `tierOf` is a homomorphism onto `Tier.max`, so
  which verdict *tier* a fold produces never depends on fold order, only
  which *message*. P2's order-independence theorem builds on exactly this.
-/
import MarchLean.CapCheck

namespace MarchLean.Calculus
open MarchLean.CapCheck

/-- Verdict severity, forgetting messages: `ok < skip < violation`. -/
inductive Tier where
  | ok | skip | violation
  deriving DecidableEq, Repr

/-- Max in the severity order (violation absorbs, ok is identity). -/
def Tier.max : Tier → Tier → Tier
  | .violation, _ => .violation
  | _, .violation => .violation
  | .skip, _      => .skip
  | _, .skip      => .skip
  | .ok, .ok      => .ok

/-- The tier of a verdict (forget the message). -/
def tierOf : CapResult → Tier
  | .ok          => .ok
  | .skip _      => .skip
  | .violation _ => .violation

theorem ok_andThen (r : CapResult) : CapResult.ok.andThen r = r := sorry
theorem andThen_ok (r : CapResult) : r.andThen .ok = r := sorry
theorem violation_andThen (m : String) (r : CapResult) :
    (CapResult.violation m).andThen r = .violation m := sorry
theorem andThen_assoc (a b c : CapResult) :
    (a.andThen b).andThen c = a.andThen (b.andThen c) := sorry

theorem Tier.max_comm (a b : Tier) : a.max b = b.max a := sorry
theorem Tier.max_assoc (a b c : Tier) : (a.max b).max c = a.max (b.max c) := sorry
theorem Tier.max_idem (a : Tier) : a.max a = a := sorry
theorem Tier.ok_max (a : Tier) : Tier.ok.max a = a := sorry
theorem Tier.max_ok (a : Tier) : a.max .ok = a := sorry

/-- `tierOf` is a monoid homomorphism `(CapResult, andThen, ok) → (Tier, max, ok)`. -/
theorem tierOf_andThen (a b : CapResult) :
    tierOf (a.andThen b) = (tierOf a).max (tierOf b) := sorry

/-- Tiers are fold-order-independent even though messages are not. -/
theorem tierOf_andThen_comm (a b : CapResult) :
    tierOf (a.andThen b) = tierOf (b.andThen a) := sorry

end MarchLean.Calculus
```

Append to `MarchLean.lean`: `import MarchLean.Calculus.Verdicts`

- [ ] **Step 3: Build — verify statements elaborate and each `sorry` warns**

Run: `export PATH="$HOME/.elan/bin:$PATH" && lake build 2>&1 | grep -c "declaration uses 'sorry'"`
Expected: `11`. If instead there are *errors*, a statement doesn't elaborate (wrong name/namespace) — fix the statement, not the definitions.

- [ ] **Step 4: Prove**

Every proof here is exhaustive case analysis; message arguments are variables the `andThen` arms never inspect, so each case closes by `rfl`:

```lean
theorem ok_andThen (r : CapResult) : CapResult.ok.andThen r = r := by cases r <;> rfl
theorem andThen_ok (r : CapResult) : r.andThen .ok = r := by cases r <;> rfl
theorem violation_andThen (m : String) (r : CapResult) :
    (CapResult.violation m).andThen r = .violation m := rfl
theorem andThen_assoc (a b c : CapResult) :
    (a.andThen b).andThen c = a.andThen (b.andThen c) := by
  cases a <;> cases b <;> cases c <;> rfl
```

Same shape (`cases … <;> rfl`) for the five `Tier` laws and `tierOf_andThen`. Then:

```lean
theorem tierOf_andThen_comm (a b : CapResult) :
    tierOf (a.andThen b) = tierOf (b.andThen a) := by
  rw [tierOf_andThen, tierOf_andThen, Tier.max_comm]
```

- [ ] **Step 5: Build — verify clean**

Run: `export PATH="$HOME/.elan/bin:$PATH" && lake build 2>&1 | tail -3` and `lake build 2>&1 | grep -c sorry`
Expected: "Build completed successfully", grep count `0`.

- [ ] **Step 6: Commit**

```bash
git add MarchLean/Calculus/Verdicts.lean MarchLean.lean
git commit -m "feat(calculus): CapResult verdict algebra — andThen monoid, tier homomorphism (P0a)"
```

---

### Task 2: `DivVerdict` semilattice + `joinAll` permutation invariance

**Files:**
- Modify: `MarchLean/Calculus/Verdicts.lean` (append)

**Interfaces:**
- Consumes: `MarchLean.CapCheck.DivVerdict` (`safe | unknown | divZero`, `DecidableEq`), `DivVerdict.join`, `DivVerdict.joinAll` (`CapCheck.lean:638-659`; `joinAll vs = vs.foldl join .safe`).
- Produces (namespace `MarchLean.Calculus`):
  - `theorem join_comm / join_assoc / join_idem (on DivVerdict)`
  - `theorem safe_join (a) : DivVerdict.safe.join a = a` and `join_safe (a) : a.join .safe = a`
  - `theorem divZero_join (a) : DivVerdict.divZero.join a = .divZero`
  - `theorem foldl_join_shift (l : List DivVerdict) (a : DivVerdict) : l.foldl DivVerdict.join a = a.join (DivVerdict.joinAll l)`
  - `theorem joinAll_perm {l₁ l₂ : List DivVerdict} (h : l₁.Perm l₂) : DivVerdict.joinAll l₁ = DivVerdict.joinAll l₂`

- [ ] **Step 1: Append the statements with `sorry`, build, expect exactly the new sorry-warnings**

```lean
theorem join_comm (a b : DivVerdict) : a.join b = b.join a := sorry
theorem join_assoc (a b c : DivVerdict) : (a.join b).join c = a.join (b.join c) := sorry
theorem join_idem (a : DivVerdict) : a.join a = a := sorry
theorem safe_join (a : DivVerdict) : DivVerdict.safe.join a = a := sorry
theorem join_safe (a : DivVerdict) : a.join .safe = a := sorry
theorem divZero_join (a : DivVerdict) : DivVerdict.divZero.join a = .divZero := sorry

/-- Fold with any accumulator = accumulator joined onto the fold from `safe`.
The bridge that lets `joinAll` be reasoned about pointwise. -/
theorem foldl_join_shift (l : List DivVerdict) (a : DivVerdict) :
    l.foldl DivVerdict.join a = a.join (DivVerdict.joinAll l) := sorry

/-- `joinAll` is permutation-invariant: division-site verdict joins do not
depend on traversal order. P2's order-independence theorem consumes this. -/
theorem joinAll_perm {l₁ l₂ : List DivVerdict} (h : l₁.Perm l₂) :
    DivVerdict.joinAll l₁ = DivVerdict.joinAll l₂ := sorry
```

Run: `lake build 2>&1 | grep -c "declaration uses 'sorry'"` — expected `8`.

- [ ] **Step 2: Prove the pointwise laws** — all six are `by cases … <;> rfl` (or `rfl` for `divZero_join`).

- [ ] **Step 3: Prove `foldl_join_shift`** — induction on `l` generalizing the accumulator:

```lean
theorem foldl_join_shift (l : List DivVerdict) (a : DivVerdict) :
    l.foldl DivVerdict.join a = a.join (DivVerdict.joinAll l) := by
  induction l generalizing a with
  | nil => simp [DivVerdict.joinAll, List.foldl, join_safe]
  | cons x xs ih =>
      simp only [DivVerdict.joinAll, List.foldl] at *
      rw [ih (a.join x), ih (DivVerdict.safe.join x), safe_join, join_assoc]
```

If the `simp only` set doesn't reduce `joinAll (x :: xs)` to `(xs.foldl join (safe.join x))`, unfold `DivVerdict.joinAll` explicitly first (`show` or `unfold`). Iterate until green — the statement is fixed, the script is not.

- [ ] **Step 4: Prove `joinAll_perm`** — induction on the `Perm` derivation; `foldl_join_shift` collapses each case:

```lean
theorem joinAll_perm {l₁ l₂ : List DivVerdict} (h : l₁.Perm l₂) :
    DivVerdict.joinAll l₁ = DivVerdict.joinAll l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
      simp only [DivVerdict.joinAll, List.foldl]
      rw [foldl_join_shift, foldl_join_shift]
      exact congrArg _ ih   -- both sides are (safe.join x).join (joinAll tail)
  | swap x y l =>
      simp only [DivVerdict.joinAll, List.foldl]
      rw [foldl_join_shift, foldl_join_shift]
      congr 1
      cases x <;> cases y <;> rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
```

The `ih` shapes in `cons`/`swap` may need massaging (`DivVerdict.joinAll` unfolding, `congrArg` target); iterate until green.

- [ ] **Step 5: Build clean, then commit**

Run: `lake build 2>&1 | tail -3` + sorry-grep `0`.

```bash
git add MarchLean/Calculus/Verdicts.lean
git commit -m "feat(calculus): DivVerdict join semilattice + joinAll permutation invariance (P0a)"
```

---

### Task 3: `Calculus/Lattice.lean` abstract defs + `CapLattice.lean` specialization refactor

**Files:**
- Create: `MarchLean/Calculus/Lattice.lean` (defs only in this task; theorems come in Tasks 4-6)
- Modify: `MarchLean/CapLattice.lean` (five defs become specializations; `hierarchy`, docstrings, and all `#eval` pins unchanged)
- Modify: `MarchLean.lean` (add `import MarchLean.Calculus.Lattice` BEFORE `import MarchLean.CapLattice`)

**Interfaces:**
- Consumes: nothing (leaf file).
- Produces (namespace `MarchLean.Calculus`; Tasks 4-7 and P2 depend on these exact names):
  - `abbrev Table := List (String × Option String)`
  - `def parentIn (T : Table) (c : String) : Option String`
  - `def ancestorsInFuel (T : Table) : Nat → String → List String`
  - `def ancestorsIn (T : Table) (c : String) : List String`
  - `def subsumesIn (T : Table) (parent child : String) : Bool`
  - `def normalizeIn (T : Table) (caps : List String) : List String`
  - `def coveredIn (T : Table) (declared : List String) (used : String) : Bool`
  - And in `MarchLean.CapLattice`, unchanged signatures: `hierarchy : Table`, `capParent`, `capAncestorsFuel`, `capAncestors`, `capSubsumes`, `normalize`.

- [ ] **Step 1: Create `MarchLean/Calculus/Lattice.lean`**

Bodies are copied verbatim from today's `CapLattice.lean` with the table made a parameter — definitional equality with the shipping code is the point:

```lean
/-!
# Abstract capability-lattice theory

`CapLattice.lean`'s five operations, parameterized over the `(name, parent)`
table so their metatheory is proved once for ANY well-formed table and
march's concrete 20-entry `hierarchy` is discharged by `decide`
(`Calculus/Concrete.lean`). The shipping `CapLattice` API is the
specialization of these to `hierarchy`, definition for definition — bodies
here are copied verbatim from the pre-P0 `CapLattice.lean`, table made a
parameter, nothing else changed.
-/
namespace MarchLean.Calculus

/-- A capability table: `(cap_path, parent_path)` rows. -/
abbrev Table := List (String × Option String)

/-- The parent of a capability in `T`, or `none` for a root or an unknown
(FFI) name. -/
def parentIn (T : Table) (c : String) : Option String :=
  match T.find? (fun (n, _) => n == c) with
  | some (_, p) => p
  | none        => none

/-- Fuel-bounded ancestor chain: `c` followed by every ancestor up to the
root, most-specific first. A name absent from `T` returns just itself (the
FFI-cap base case). -/
def ancestorsInFuel (T : Table) : Nat → String → List String
  | 0,        c => [c]
  | fuel + 1, c =>
      match parentIn T c with
      | some p => c :: ancestorsInFuel T fuel p
      | none   => [c]

/-- `ancestorsIn T c` with fuel `T.length` — adequate for any well-formed
table (proved below: `ancestorsIn_fuel_adequate`). -/
def ancestorsIn (T : Table) (c : String) : List String :=
  ancestorsInFuel T T.length c

/-- Is `parent` an ancestor of, or equal to, `child` in `T`? -/
def subsumesIn (T : Table) (parent child : String) : Bool :=
  (ancestorsIn T child).contains parent

/-- Drop any cap subsumed by another cap present, preserving relative order
of survivors. -/
def normalizeIn (T : Table) (caps : List String) : List String :=
  caps.filter (fun c => !caps.any (fun other => other != c && subsumesIn T other c))

/-- Is `used` covered by some declared cap, via subsumption? The abstract
form of `CapCheck.covered` (bridged in P2). -/
def coveredIn (T : Table) (declared : List String) (used : String) : Bool :=
  declared.any (fun need => subsumesIn T need used)

end MarchLean.Calculus
```

- [ ] **Step 2: Refactor `MarchLean/CapLattice.lean`**

Add `import MarchLean.Calculus.Lattice` at the top (before the module docstring's `/-!` block — imports must precede it). Keep the module docstring and `hierarchy` (retyped as `Table`, same literal). Replace the four operation bodies with specializations, keeping every existing docstring:

```lean
def hierarchy : MarchLean.Calculus.Table :=
  [ ("IO", none), ... ]   -- the existing 20-entry literal, character for character

def capParent (c : String) : Option String :=
  MarchLean.Calculus.parentIn hierarchy c

def capAncestorsFuel (fuel : Nat) (c : String) : List String :=
  MarchLean.Calculus.ancestorsInFuel hierarchy fuel c

def capAncestors (c : String) : List String :=
  MarchLean.Calculus.ancestorsIn hierarchy c

def capSubsumes (parent child : String) : Bool :=
  MarchLean.Calculus.subsumesIn hierarchy parent child

def normalize (caps : List String) : List String :=
  MarchLean.Calculus.normalizeIn hierarchy caps
```

Signature care: today's `capAncestorsFuel` is `Nat → String → List String` by pattern-matching equations; the specialization above has the same type. `capAncestors` must remain `ancestorsInFuel` at fuel `hierarchy.length` — `ancestorsIn hierarchy` is exactly that. Leave the `#eval` pin block at the bottom of the file untouched.

- [ ] **Step 3: Wire the import and build**

`MarchLean.lean`: add `import MarchLean.Calculus.Lattice` (before `import MarchLean.CapLattice`, matching dependency order).
Run: `export PATH="$HOME/.elan/bin:$PATH" && lake build 2>&1 | tail -3`
Expected: clean build. The `#eval` pins in `CapLattice.lean` print during elaboration — eyeball that the printed values still match their `-- expect` comments (reflexivity true, siblings false, `capAncestors "LibC" = ["LibC"]`, etc.).

- [ ] **Step 4: Behavior-preservation check — corpus re-run must be byte-identical to baseline**

```bash
export PATH="$HOME/.elan/bin:$PATH" && cd "$(git rev-parse --show-toplevel)" && \
lake build march-lean-check && \
MARCH_BIN="$HOME/.opam/march/bin/march" \
CORPUS_DIR="$HOME/code/march/specs/lang/types" \
MARCH_LEAN_CHECK_BIN=.lake/build/bin/march-lean-check \
scripts/conformance-harness.sh > /tmp/p0-corpus-after-task3.txt 2>&1; \
echo "exit=$?" >> /tmp/p0-corpus-after-task3.txt; \
diff /tmp/p0-corpus-baseline.txt /tmp/p0-corpus-after-task3.txt && echo IDENTICAL
```

Expected: `IDENTICAL`. Any diff at all = the refactor changed behavior — STOP, find the divergence (it is a bug in the refactor or a genuine finding; do not proceed with a diff).

- [ ] **Step 5: Commit**

```bash
git add MarchLean/Calculus/Lattice.lean MarchLean/CapLattice.lean MarchLean.lean
git commit -m "refactor(calculus): parameterize the cap lattice over an abstract table (P0b)

API-preserving: capParent/capAncestorsFuel/capAncestors/capSubsumes/
normalize become specializations of Calculus.parentIn/ancestorsInFuel/
ancestorsIn/subsumesIn/normalizeIn at the unchanged 20-entry hierarchy.
Conformance output verified byte-identical against the local corpus."
```

---

### Task 4: Well-formedness + fuel adequacy + chain shape

**Files:**
- Modify: `MarchLean/Calculus/Lattice.lean` (append defs + theorems)

**Interfaces:**
- Consumes: Task 3's defs.
- Produces (namespace `MarchLean.Calculus`):
  - `def namesOf (T : Table) : List String` (= `T.map (·.1)`)
  - `def nodupNamesB : Table → Bool`
  - `def parentClosedB (T : Table) : Bool`
  - `def reachesRoot (T : Table) : Nat → String → Bool`
  - `def WellFormedB (T : Table) : Bool` (conjunction of the three)
  - `theorem ancestorsInFuel_head (T fuel c) : (ancestorsInFuel T fuel c).head? = some c`
  - `theorem self_mem_ancestorsIn (T c) : c ∈ ancestorsIn T c`
  - `theorem subsumesIn_refl (T c) : subsumesIn T c c = true`
  - `theorem parentIn_eq_none_of_not_mem {T c} (h : c ∉ namesOf T) : parentIn T c = none`
  - `theorem reachesRoot_mono {T c fuel fuel'} (h : fuel ≤ fuel') : reachesRoot T fuel c = true → reachesRoot T fuel' c = true`
  - `theorem ancestorsInFuel_stable {T c fuel} (h : reachesRoot T fuel c = true) {f} (hf : fuel ≤ f) : ancestorsInFuel T f c = ancestorsInFuel T fuel c`
  - `theorem wf_reachesRoot {T} (wf : WellFormedB T = true) (c : String) : reachesRoot T T.length c = true`
  - `theorem ancestorsIn_fuel_adequate {T} (wf : WellFormedB T = true) {f} (hf : T.length ≤ f) (c) : ancestorsInFuel T f c = ancestorsIn T c`
  - `theorem ancestorsIn_root {T c} (h : parentIn T c = none) : ancestorsIn T c = [c]`
  - `theorem ancestorsIn_cons {T} (wf : WellFormedB T = true) {c p} (h : parentIn T c = some p) : ancestorsIn T c = c :: ancestorsIn T p`

- [ ] **Step 1: Append the defs**

```lean
/-- The names (first components) of a table. -/
def namesOf (T : Table) : List String := T.map (·.1)

/-- No two rows share a name (Boolean, so `decide` can discharge it). -/
def nodupNamesB : Table → Bool
  | [] => true
  | (n, _) :: rest => !rest.any (fun (m, _) => m == n) && nodupNamesB rest

/-- Every parent value that occurs is itself a row's name. march's real
table satisfies this; FFI caps are absent from the table entirely, never
dangling parents. -/
def parentClosedB (T : Table) : Bool :=
  T.all (fun (_, p?) => match p? with
    | none => true
    | some p => T.any (fun (n, _) => n == p))

/-- Does the parent chain from `c` reach a parentless node within `fuel`
steps? The acyclicity witness: in a well-formed table every name does so
within `T.length` steps. -/
def reachesRoot (T : Table) : Nat → String → Bool
  | 0, c => (parentIn T c).isNone
  | fuel + 1, c =>
      match parentIn T c with
      | none => true
      | some p => reachesRoot T fuel p

/-- Well-formed table: unique names, closed parents, acyclic. This is what
`CapLattice.lean`'s old prose comment ("the table is a finite forest with no
cycles, so `hierarchy.length` is a safe fuel bound") asserted; here it is a
decidable proposition, discharged for the real table in `Concrete.lean`. -/
def WellFormedB (T : Table) : Bool :=
  nodupNamesB T && parentClosedB T && T.all (fun (n, _) => reachesRoot T T.length n)
```

- [ ] **Step 2: State all ten theorems with `sorry`, build, count warnings = 10**

Statements exactly as in the Interfaces block above.

- [ ] **Step 3: Prove, easiest first**

- `ancestorsInFuel_head`: `cases fuel` then `simp [ancestorsInFuel]`; in the successor case `cases h : parentIn T c <;> simp [h]`.
- `self_mem_ancestorsIn` / `subsumesIn_refl`: from `head?` = some via `List.head?_eq_some`-style reasoning (`ancestorsIn` is nonempty with head `c`; `List.contains` of the head is true — `simp [subsumesIn, List.contains]` plus `self_mem_ancestorsIn`).
- `parentIn_eq_none_of_not_mem`: `parentIn` is a `find?`; if it returned `some`, `List.find?_some`/`List.mem_of_find?_eq_some` puts a row with name `c` in `T` (the predicate is `n == c`), contradicting `h` via `namesOf` membership.
- `reachesRoot_mono`: induction on `fuel` generalizing `c` and `fuel'`; case on `parentIn T c`. Note the base case needs `parentIn = none → reachesRoot _ anything = true` — split out as a private helper if the induction gets awkward.
- `ancestorsInFuel_stable`: induction on `fuel` generalizing `c f`; base `fuel = 0` has `(parentIn T c).isNone = true`, so every fuel value returns `[c]`; successor case: if `parentIn T c = none` both sides are `[c]`; if `some p`, peel one constructor off both sides (`f = f' + 1` exists since `f ≥ fuel + 1 ≥ 1`) and apply the IH at `p`.
- `wf_reachesRoot`: split `wf` into its three conjuncts (`Bool.and_eq_true`). Case on `c ∈ namesOf T`: if absent, `parentIn_eq_none_of_not_mem` makes `reachesRoot` true at any fuel (case on `T.length`); if present, `List.mem_map` gives a row `(c, p?) ∈ T` and the third conjunct (`List.all_eq_true`) applied to that row is exactly the goal.
- `ancestorsIn_fuel_adequate`: `ancestorsInFuel_stable` with `wf_reachesRoot`.
- `ancestorsIn_root`: unfold `ancestorsIn`; `cases T.length <;> simp [ancestorsInFuel, h]`.
- `ancestorsIn_cons`: from `h`, `c` is a row name so `T ≠ []`, hence `T.length = k + 1`; unfold one `ancestorsInFuel` step to get `c :: ancestorsInFuel T k p`; `wf_reachesRoot c` at fuel `k + 1` reduces through `h` to `reachesRoot T k p`; `ancestorsInFuel_stable` (with `k ≤ T.length`) rewrites `ancestorsInFuel T k p` to `ancestorsIn T p`.

Iterate each until green before starting the next — later proofs in this task use earlier lemmas.

- [ ] **Step 4: Build clean (0 sorries), commit**

```bash
git add MarchLean/Calculus/Lattice.lean
git commit -m "feat(calculus): table well-formedness, fuel adequacy, ancestor chain shape (P0b)

WellFormedB (nodup names + closed parents + acyclic) is decidable; fuel
hierarchy.length is proved adequate — the old 'safe bound' prose comment
is now the theorem ancestorsIn_fuel_adequate."
```

---

### Task 5: Order theorems — suffix, transitivity, antisymmetry, siblings, FFI isolation

**Files:**
- Modify: `MarchLean/Calculus/Lattice.lean` (append)

**Interfaces:**
- Consumes: Task 4's lemmas (esp. `ancestorsIn_cons`, `ancestorsIn_root`, `self_mem_ancestorsIn`, `wf_reachesRoot`).
- Produces (namespace `MarchLean.Calculus`):
  - `theorem mem_ancestorsIn_suffix {T} (wf : WellFormedB T = true) {p c} (h : p ∈ ancestorsIn T c) : ancestorsIn T p <:+ ancestorsIn T c`
  - `theorem subsumesIn_trans {T} (wf : WellFormedB T = true) {a b c} : subsumesIn T a b = true → subsumesIn T b c = true → subsumesIn T a c = true`
  - `theorem subsumesIn_antisymm {T} (wf : WellFormedB T = true) {p c} : subsumesIn T p c = true → subsumesIn T c p = true → p = c`
  - `theorem no_self_parent {T} (wf : WellFormedB T = true) {p} : parentIn T p ≠ some p`
  - `theorem siblings_incomparable {T} (wf : WellFormedB T = true) {p c q} (hp : parentIn T p = some q) (hc : parentIn T c = some q) (hne : p ≠ c) : subsumesIn T p c = false`
  - `theorem subsumesIn_of_absent {T c p} (h : parentIn T c = none) : subsumesIn T p c = true ↔ p = c`
  - `theorem mem_ancestorsIn_names {T} (wf : WellFormedB T = true) {a x} (h : a ∈ ancestorsIn T x) : a = x ∨ a ∈ namesOf T`
  - `theorem absent_subsumesIn {T} (wf : WellFormedB T = true) {c x} (hc : c ∉ namesOf T) (h : subsumesIn T c x = true) : x = c`

- [ ] **Step 1: State all eight with `sorry`; build; count = 8**

- [ ] **Step 2: Prove `mem_ancestorsIn_suffix`** — the workhorse. Strong induction on `(ancestorsIn T c).length`, unfolding the chain with Task 4's shape lemmas:

Skeleton (iterate until green; the structure is the contract, the tactic details are not):

```lean
theorem mem_ancestorsIn_suffix {T} (wf : WellFormedB T = true) {p c}
    (h : p ∈ ancestorsIn T c) : ancestorsIn T p <:+ ancestorsIn T c := by
  induction hn : (ancestorsIn T c).length using Nat.strong_induction_on
    generalizing c with
  | _ n ih =>
  by_cases hpc : p = c
  · subst hpc; exact List.suffix_refl _
  · cases hpar : parentIn T c with
    | none =>
        rw [ancestorsIn_root hpar] at h
        simp at h; exact absurd h hpc
    | some q =>
        rw [ancestorsIn_cons wf hpar] at h ⊢
        rcases List.mem_cons.mp h with rfl | hq
        · exact absurd rfl hpc
        · exact (ih _ (by rw [ancestorsIn_cons wf hpar, hn ▸ rfl] ...) hq rfl).trans
            (List.suffix_cons _ _)
```

The measure argument: `ancestorsIn_cons` makes `(ancestorsIn T q).length = n - 1 < n`. Wire the `<` fact through however `Nat.strong_induction_on`'s motive wants it (an explicit `have hlt : (ancestorsIn T q).length < n` from `hn` and the cons equation, then `ih _ hlt`). If `Nat.strong_induction_on` fights, an equivalent formulation is a `termination_by`-measured recursive theorem or well-founded `induction … using` variant — any of these is acceptable; the statement may not change.

- [ ] **Step 3: Prove the consequences**

- `subsumesIn_trans`: `subsumesIn x y = true ↔ x ∈ ancestorsIn T y` (a `simp [subsumesIn, List.contains]`-style bridge — extract it as a private lemma `subsumesIn_iff_mem`, it gets used everywhere). Then `mem_ancestorsIn_suffix wf h₂` is a suffix, and `(·.subset)` (`List.IsSuffix.subset`) maps `a ∈ ancestorsIn T b` into `ancestorsIn T c`'s membership.
- `subsumesIn_antisymm`: two applications of `mem_ancestorsIn_suffix` give mutual suffixes; `List.IsSuffix.length_le` both ways + `Nat.le_antisymm` give equal lengths; a mutual suffix of equal length forces list equality (prove inline: `l₁ <:+ l₂` means `∃ t, t ++ l₁ = l₂`; equal lengths force `t = []` by `List.length_append` arithmetic); equal lists have equal `head?`, and `ancestorsInFuel_head` turns `some p = some c` into `p = c`.
- `no_self_parent`: intro `hp : parentIn T p = some p`. Private helper: `reachesRoot T f p = false` for every `f` by induction on `f` (base: `hp` makes `isNone` false; step: `hp` reduces to the IH). Contradict `wf_reachesRoot wf p`.
- `siblings_incomparable`: by contradiction from `subsumesIn T p c = true`: `ancestorsIn_cons wf hc` puts `p ∈ c :: ancestorsIn T q`; `p ≠ c` leaves `p ∈ ancestorsIn T q`, which by `subsumesIn_iff_mem` (direction: `x ∈ ancestorsIn T y ↔ subsumesIn T x y = true` — x is the *subsumer*) is `subsumesIn T p q = true`. Symmetrically, `ancestorsIn_cons wf hp` plus `self_mem_ancestorsIn T q` puts `q ∈ ancestorsIn T p`, i.e. `subsumesIn T q p = true`. Antisymmetry on the pair gives `p = q`; rewriting `hp` yields `parentIn T p = some p`; contradict `no_self_parent`.
- `subsumesIn_of_absent`: rewrite with `ancestorsIn_root h`; membership in `[c]` is equality.
- `mem_ancestorsIn_names`: same strong-induction skeleton as `mem_ancestorsIn_suffix` (chain unfold via `ancestorsIn_cons`); in the `some q` case, `q ∈ namesOf T` comes from `parentClosedB` (the second `wf` conjunct: the row that made `parentIn T x = some q` has parent value `q`, and closure finds a row named `q`). Extract `parentIn_some_mem_names {T} (wf) : parentIn T x = some q → q ∈ namesOf T` as a private helper.
- `absent_subsumesIn`: `subsumesIn_iff_mem` + `mem_ancestorsIn_names wf`; the `∈ namesOf` disjunct contradicts `hc`, leaving `c = x`.

- [ ] **Step 4: Build clean, commit**

```bash
git add MarchLean/Calculus/Lattice.lean
git commit -m "feat(calculus): subsumption is a partial order — suffix lemma, trans, antisymm, sibling incomparability, FFI isolation (P0b)"
```

---

### Task 6: `coveredIn` / `normalizeIn` theorems

**Files:**
- Modify: `MarchLean/Calculus/Lattice.lean` (append)

**Interfaces:**
- Consumes: Tasks 4-5 (esp. `subsumesIn_trans`, `subsumesIn_antisymm`, `mem_ancestorsIn_suffix`, `subsumesIn_iff_mem`).
- Produces (namespace `MarchLean.Calculus`; P2's normalize-stability and monotonicity theorems consume the last three):
  - `theorem coveredIn_mono {T L L' c} (hsub : ∀ x ∈ L, x ∈ L') (h : coveredIn T L c = true) : coveredIn T L' c = true`
  - `theorem coveredIn_of_subsumes {T p c} (h : subsumesIn T p c = true) : coveredIn T [p] c = true`
  - `theorem normalizeIn_subset (T : Table) (L : List String) : ∀ x ∈ normalizeIn T L, x ∈ L`
  - `theorem ancestors_length_lt {T} (wf : WellFormedB T = true) {p c} (hmem : p ∈ ancestorsIn T c) (hne : p ≠ c) : (ancestorsIn T p).length < (ancestorsIn T c).length`
  - `theorem exists_survivor {T} (wf : WellFormedB T = true) {L need} (hmem : need ∈ L) : ∃ m ∈ normalizeIn T L, subsumesIn T m need = true`
  - `theorem coveredIn_normalizeIn {T} (wf : WellFormedB T = true) (L : List String) (c : String) : coveredIn T (normalizeIn T L) c = coveredIn T L c`
  - `theorem normalizeIn_idem (T : Table) (L : List String) : normalizeIn T (normalizeIn T L) = normalizeIn T L`

- [ ] **Step 1: State all seven with `sorry`; build; count = 7**

- [ ] **Step 2: Prove the easy four**

- `coveredIn_mono`: `coveredIn` is `List.any`; `List.any_eq_true` both ways, move the witness through `hsub`.
- `coveredIn_of_subsumes`: `simp [coveredIn, h]`.
- `normalizeIn_subset`: `normalizeIn` is a `filter`; `List.mem_filter.mp`.
- `ancestors_length_lt`: `mem_ancestorsIn_suffix wf hmem` gives `≤` via `List.IsSuffix.length_le`; if lengths were equal the suffix is the whole list (same inline argument as in `subsumesIn_antisymm` — if it was extracted as a private lemma there, reuse it), so heads give `p = c` contradicting `hne`; hence strict.

- [ ] **Step 3: Prove `exists_survivor`** — the descent argument. Strong induction on `(ancestorsIn T need).length`:

If `need ∈ normalizeIn T L`: witness `need`, `subsumesIn_refl`. Otherwise `List.mem_filter` says the filter predicate was false: `¬¬(L.any (fun other => other != need && subsumesIn T other need))`, i.e. some `other ∈ L`, `other ≠ need`, `subsumesIn T other need = true`. Then `other ∈ ancestorsIn T need` (`subsumesIn_iff_mem`) and `ancestors_length_lt wf … hne'` (with `hne' : other ≠ need`) gives the measure drop; the IH at `other` yields `m ∈ normalizeIn T L` with `subsumesIn T m other`; `subsumesIn_trans wf` composes it to `need`. Beware Bool/Prop plumbing on the filter predicate (`Bool.not_eq_true`, `bne_iff_ne`, `List.any_eq_true`) — mechanical, iterate until green.

- [ ] **Step 4: Prove the two headline theorems**

- `coveredIn_normalizeIn`: prove Bool equality by `Bool.eq_iff_iff`-style case split or two implications: (←, i.e. `coveredIn T L c → coveredIn T (normalizeIn T L) c`): from the covering witness `need ∈ L`, `exists_survivor` gives `m` surviving with `subsumesIn T m need`; `subsumesIn_trans` reaches `c`; `List.any_eq_true` re-packages. (→): `coveredIn_mono (normalizeIn_subset T L)`.
- `normalizeIn_idem`: show the second filter keeps every survivor: for `s ∈ normalizeIn T L`, a dropper `other ∈ normalizeIn T L` with `other ≠ s ∧ subsumesIn T other s` would, via `normalizeIn_subset`, be a dropper in the FIRST round, contradicting `s`'s survival. Implement as `List.filter_eq_self`-style (if that core lemma name doesn't resolve, prove by `List.filter` induction inline). Note this needs no `wf`.

- [ ] **Step 5: Build clean, commit**

```bash
git add MarchLean/Calculus/Lattice.lean
git commit -m "feat(calculus): normalize is idempotent and coverage-preserving; covered is monotone (P0b)"
```

---

### Task 7: `Calculus/Concrete.lean` — the 20-entry table discharged, shipping-name corollaries

**Files:**
- Create: `MarchLean/Calculus/Concrete.lean`
- Modify: `MarchLean.lean` (add `import MarchLean.Calculus.Concrete` after the CapLattice import)

**Interfaces:**
- Consumes: everything from Tasks 3-6; `MarchLean.CapLattice` (`hierarchy`, `capParent`, `capAncestors`, `capAncestorsFuel`, `capSubsumes`, `normalize`).
- Produces (namespace `MarchLean.Calculus.Concrete`; P2 consumes these):
  - `theorem hierarchy_wellFormed : WellFormedB hierarchy = true`
  - `theorem capSubsumes_refl (c : String) : capSubsumes c c = true`
  - `theorem capSubsumes_trans {a b c} : capSubsumes a b = true → capSubsumes b c = true → capSubsumes a c = true`
  - `theorem capSubsumes_antisymm {p c} : capSubsumes p c = true → capSubsumes c p = true → p = c`
  - `theorem capSiblings_incomparable {p c q} : capParent p = some q → capParent c = some q → p ≠ c → capSubsumes p c = false`
  - `theorem capAncestors_fuel_adequate {f} (hf : hierarchy.length ≤ f) (c) : capAncestorsFuel f c = capAncestors c`
  - `theorem normalize_covered (L c) : coveredIn hierarchy (normalize L) c = coveredIn hierarchy L c`
  - `theorem normalize_idem (L) : normalize (normalize L) = normalize L`

- [ ] **Step 1: Create the file**

```lean
/-!
# The shipping lattice, discharged

`WellFormedB hierarchy` by kernel `decide` (measured ~0.5s on this
toolchain), then every abstract theorem instantiated at the shipping names.
If march ever adds a duplicate name, a dangling parent, or a cycle to
`cap_lattice.ml` and the port follows, THE `decide` BELOW is what fails —
loudly, at build time. That failure mode is the point of this file.
-/
import MarchLean.CapLattice

namespace MarchLean.Calculus.Concrete
open MarchLean.Calculus MarchLean.CapLattice

theorem hierarchy_wellFormed : WellFormedB hierarchy = true := by decide

theorem capSubsumes_refl (c : String) : capSubsumes c c = true :=
  subsumesIn_refl hierarchy c

theorem capSubsumes_trans {a b c : String}
    (h₁ : capSubsumes a b = true) (h₂ : capSubsumes b c = true) :
    capSubsumes a c = true :=
  subsumesIn_trans hierarchy_wellFormed h₁ h₂

theorem capSubsumes_antisymm {p c : String}
    (h₁ : capSubsumes p c = true) (h₂ : capSubsumes c p = true) : p = c :=
  subsumesIn_antisymm hierarchy_wellFormed h₁ h₂

theorem capSiblings_incomparable {p c q : String}
    (hp : capParent p = some q) (hc : capParent c = some q) (hne : p ≠ c) :
    capSubsumes p c = false :=
  siblings_incomparable hierarchy_wellFormed hp hc hne

theorem capAncestors_fuel_adequate {f : Nat} (hf : hierarchy.length ≤ f)
    (c : String) : capAncestorsFuel f c = capAncestors c :=
  ancestorsIn_fuel_adequate hierarchy_wellFormed hf c

theorem normalize_covered (L : List String) (c : String) :
    coveredIn hierarchy (normalize L) c = coveredIn hierarchy L c :=
  coveredIn_normalizeIn hierarchy_wellFormed L c

theorem normalize_idem (L : List String) : normalize (normalize L) = normalize L :=
  normalizeIn_idem hierarchy L

-- The FFI base case, now consequences of theorems rather than #eval pins:
example : capSubsumes "LibC" "LibC" = true := capSubsumes_refl _
example (p : String) : capSubsumes p "LibC" = true ↔ p = "LibC" :=
  subsumesIn_of_absent (by decide)
example : capSubsumes "IO" "LibC" = false := by decide

end MarchLean.Calculus.Concrete
```

Term-mode friction note: `capSubsumes` etc. are *definitionally* `subsumesIn hierarchy` etc. (Task 3 made them so), so the abstract theorems apply directly. If the elaborator balks, `show subsumesIn hierarchy …` or `unfold capSubsumes` first. If `decide` on `hierarchy_wellFormed` exceeds heartbeats (unlikely — probe measured ~0.5s), add `set_option maxHeartbeats 1000000 in`; do NOT switch to `native_decide` without trying that.

- [ ] **Step 2: Build clean** (`lake build`, 0 sorries, no warnings).

- [ ] **Step 3: Negative control — verify the discharge actually guards.** Temporarily add a cycle row `("X.Cycle", some "X.Cycle")` to `hierarchy`, run `lake build`, and confirm `hierarchy_wellFormed`'s `decide` FAILS. Revert the row, rebuild green. (Analogue of the repo's forced-relaxation tests: proves the guard is load-bearing, not vacuous.) Do not commit the broken state.

- [ ] **Step 4: Commit**

```bash
git add MarchLean/Calculus/Concrete.lean MarchLean.lean
git commit -m "feat(calculus): WellFormedB hierarchy by decide; lattice metatheory instantiated at shipping names (P0b)

Negative control verified: a self-parent row added to hierarchy fails the
decide at build time, then reverted."
```

---

### Task 8: CI sorry-guard + final verification

**Files:**
- Modify: `.github/workflows/` conformance workflow (the single YAML in that directory — add one step after the Lean build step)

**Interfaces:**
- Consumes: all prior tasks.
- Produces: CI fails on any committed `sorry`/`admit`; P0 done.

- [ ] **Step 1: Add the guard step** (after the `leanprover/lean-action` build step, before the harness run):

```yaml
      # Lean treats `sorry` as a WARNING, not an error, so `lake build`
      # alone would pass with unproven theorems. The Calculus/ proof layer
      # (P0, specs/plans/2026-08-08-calculus-proof-capabilities-design.md)
      # is only evidence if this gate holds. Source-level grep (rather than
      # build-log parsing) so the failure names the offending file:line.
      - name: Forbid sorry/admit in Lean sources
        run: |
          if grep -rnE '\b(sorry|admit)\b' --include='*.lean' MarchLean/ MarchLean.lean MarchLeanCheck.lean; then
            echo "::error::sorry/admit found in Lean sources (see matches above)"; exit 1
          fi
```

- [ ] **Step 2: Verify the guard logic locally**

Run the same grep in the repo — expected: no matches, exit 1 from grep (so the `if` takes the else path). Then `echo 'example : True := by sorry' >> /tmp/guardcheck.lean` is NOT needed — instead verify positively: `grep -rnE '\b(sorry|admit)\b' --include='*.lean' MarchLean/ MarchLean.lean MarchLeanCheck.lean; echo "grep_exit=$?"` — expected `grep_exit=1` (no matches).

- [ ] **Step 3: Final full verification**

```bash
export PATH="$HOME/.elan/bin:$PATH" && cd "$(git rev-parse --show-toplevel)" && \
lake build && lake build march-lean-check && \
MARCH_BIN="$HOME/.opam/march/bin/march" \
CORPUS_DIR="$HOME/code/march/specs/lang/types" \
MARCH_LEAN_CHECK_BIN=.lake/build/bin/march-lean-check \
scripts/conformance-harness.sh > /tmp/p0-corpus-final.txt 2>&1; \
echo "exit=$?" >> /tmp/p0-corpus-final.txt; \
diff /tmp/p0-corpus-baseline.txt /tmp/p0-corpus-final.txt && echo IDENTICAL
```

Expected: clean build, `IDENTICAL`.

- [ ] **Step 4: Commit**

```bash
git add .github/workflows/
git commit -m "ci: fail on sorry/admit in Lean sources — the proof layer is only evidence if this gate holds (P0)"
```

---

## Out of scope for this plan (later plans)

- **P1** (de-partialize the 18 walks in `Syntax.lean`/`CapCheck.lean` with legacy-equivalence pins) — planned after P0 lands, against the then-current definitions.
- **P2** (whole-checker theorem/counterexample pairs; bridges `CapCheck.covered` to `coveredIn hierarchy`) — requires P1.
- Migrating existing `native_decide` pins to `decide` — a P1 concern (it needs the de-partialized definitions).
