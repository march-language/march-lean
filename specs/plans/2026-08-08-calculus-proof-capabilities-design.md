# Proof calculus for the capability checker (design)

> Parent design docs: `specs/plans/2026-07-23-a3-capability-lattice-design.md`
> (the checker this calculus is about), and transitively the A1/A2 docs it
> cites.
>
> This is a **design doc**, not an implementation plan. Implementation plans
> follow via `writing-plans`, one per phase (§6).
>
> Authoritative sources for every claim about current behavior:
> `MarchLean/CapLattice.lean`, `MarchLean/CapCheck.lean`,
> `MarchLean/Syntax.lean`, at the SHA this doc is committed at.

## 0. What this is

`march-lean` currently contains **zero theorems**. Validation is three-layered
— 112 `native_decide` pins, `#eval` expectations, and the 242-file
conformance corpus — and all three are *testing*: they check points, not
properties. The project's own findings log shows why that matters: every
major defect found so far hid behind a plausible comment asserting a property
nobody checked ("safe to ignore", "safe bound", "read by").

This milestone adds a **proof layer**: machine-checked theorems about the
capability checker's algebraic core, proved in the same Lean codebase and
kernel-checked by the same `lake build` CI already runs. Scope decision,
stated up front: this is **metatheory of what exists** — properties of the
checker's own definitions — not an operational semantics for march programs,
not a soundness theorem about march, and not a spec-vs-implementation
refinement argument. Those are possible later stages; none is prerequisite
for this one and none is smuggled in.

## 1. Design decisions

1. **Metatheory of the shipping code, not a shadow model.** The theorems are
   about the very definitions `march-lean-check` executes. A clean-room model
   would be easier to prove things about, but its theorems would attach to
   the model, and the gap between model and shipping code is exactly the kind
   of untested "surely equivalent" claim this project exists to distrust.

2. **No mathlib.** Everything proved here lives in `List String`, `Bool`, and
   small inductives. The repo is a zero-dependency oracle whose CI builds
   from a cold toolchain on every push; mathlib would dominate that build for
   lemmas (`List.Perm`, `foldl` algebra) that are cheap to state and prove
   directly.

3. **Parameterize the lattice over an abstract table.** `capParent` /
   `capAncestors` / `capSubsumes` / `normalize` generalize over a
   `(name, parent)` table argument; the shipping `CapLattice` API is the
   specialization to `hierarchy`, signature-for-signature. The metatheory is
   proved once for **any well-formed table** and the concrete table's
   well-formedness is discharged by `decide`. Consequences: (a) when march
   adds a capability, only the `decide` re-runs — no theorem is touched;
   (b) if march ever ships a cycle or a duplicate name, the build fails at
   the discharge, loudly — converting `CapLattice.lean:54`'s prose claim
   ("the table is a finite forest with no cycles") into a checked invariant;
   (c) transitivity/antisymmetry are structural inductions over the ancestor
   chain instead of a large kernel computation over concrete strings.

4. **De-partialization is a prerequisite, done with a runtime safety net.**
   Lean gives `partial def` no equation lemmas: the 18 `partial def` tree
   walks can be neither inducted on nor `decide`d (which is precisely why the
   112 existing pins say `native_decide`). All 18 become total. A
   `partial ≡ total` equivalence is not provable (the partial side is opaque
   to the kernel), but both sides *run*: each conversion keeps the old body
   as `…Legacy`, pins `legacy x = total x` by `native_decide` across every
   existing fixture, passes the full 242-file corpus, and deletes the legacy
   in the same PR. Any divergence the pins catch is a finding about the walk,
   per the project's standing rule that green corpus runs are weak evidence.

5. **Theorem-driven, bottom-up sequencing.** Work is ordered by theorem; each
   theorem names the definitions it needs, and only those are converted in
   that slice. Proof value lands from the first phase; every shipping-code
   change is separately corpus-validated; no big-bang diff.

6. **Boundary failures are stated, not hand-waved.** All three whole-checker
   properties chosen for this milestone are **false for the full checker and
   true for its subsumption-coverage core** (§5) — the boundary is the
   behavioral-cap layer every time. Each lands as a *pair*: a theorem scoped
   to the coverage core, plus a machine-checked counterexample (`example :
   … := by native_decide` or `decide`) pinning exactly where and why the full
   checker breaks the law. The counterexamples are first-class deliverables:
   they turn "behavioral caps are different" from a comment into checked
   statements of *how*.

## 2. Shape

Four new files under `MarchLean/Calculus/`, imported from `MarchLean.lean` so
the existing CI `lake build` kernel-checks every theorem on every push. One
caveat: `sorry` is a *warning* in Lean, not an error, so a bare `lake build`
would pass with unproven theorems. The one CI edit in this milestone is a
line grepping the build output for `declaration uses 'sorry'` and failing on
a hit.

```
MarchLean/Calculus/Lattice.lean   -- abstract hierarchy theory (any well-formed table)
MarchLean/Calculus/Concrete.lean  -- march's 20-entry table discharged by decide
MarchLean/Calculus/Verdicts.lean  -- CapResult / DivVerdict algebra
MarchLean/Calculus/CheckCaps.lean -- whole-checker theorem/counterexample pairs
```

Shipping behavior is unchanged throughout: every refactor is API-preserving
(same names, same signatures, same results), and every phase that touches
shipping code re-runs the full conformance harness.

## 3. The abstract lattice (phase P0b)

`Calculus/Lattice.lean` defines, over a table `T : List (String × Option
String)`:

- `parentIn T c`, `ancestorsIn T c` (fuel-bounded as today), `subsumesIn T`,
  `normalizeIn T`, `coveredIn T` — the generalizations. `CapLattice`'s
  public names become `def capParent := parentIn hierarchy` etc.; every
  call site and `#eval` pin compiles unchanged.
- `WellFormed T : Prop` — (i) no duplicate names; (ii) acyclic, stated as a
  strictly-decreasing depth measure on parent chains (equivalently: every
  chain reaches a root in ≤ `T.length` steps, which is also exactly the fuel
  adequacy claim).

Theorems, for any `T` with `WellFormed T`:

| theorem | content | replaces |
|---|---|---|
| `ancestors_head` | `ancestorsIn T c` begins with `c` | reflexivity pins |
| `ancestors_chain` | each element's successor is its parent | prose at `CapLattice.lean:46-56` |
| `ancestors_fuel_adequate` | fuel `T.length` never truncates | prose "safe bound" claim |
| `subsumes_refl` / `subsumes_trans` / `subsumes_antisymm` | partial order | sibling/directionality pins |
| `siblings_incomparable` | distinct children of one parent never subsume each other | reject/t38-shaped pins |
| `absent_name_isolated` | a name ∉ T subsumes and is subsumed by only itself | FFI/LibC pins |
| `normalize_idempotent` | `normalizeIn T (normalizeIn T L) = normalizeIn T L` | — (new) |
| `normalize_covered` | `coveredIn T L c ↔ coveredIn T (normalizeIn T L) c` | — (new; **the** lemma licensing `normalize`, and the one that dies without antisymmetry) |
| `covered_mono` | `L ⊆ L' → coveredIn T L c → coveredIn T L' c` | — (new; feeds §5 monotonicity) |
| `covered_upward` | `subsumesIn T p c → coveredIn T [p] c` | root-covers-child pins |

`Calculus/Concrete.lean` proves `WellFormed hierarchy` by `decide` and
instantiates the table above for the shipping lattice. The existing `#eval`
pins in `CapLattice.lean` stay (they are documentation-by-example and cost
nothing); the theorems supersede them as evidence.

## 4. Verdict algebra (phase P0a) and de-partialization (phase P1)

**P0a — `Calculus/Verdicts.lean`, purely additive, lands first.**
`CapResult.andThen`: associative; `ok` two-sided identity; `violation`
left-absorbing; and the tier projection `tier : CapResult → Tier` (`ok <
skip < violation`) is a homomorphism onto max — i.e. messages depend on
order (leftmost-wins, by design), tiers never do. `DivVerdict.join`:
commutative, associative, idempotent, `safe` identity, `divZero` absorbing;
hence `joinAll` is permutation-invariant (needed by §5's order-independence).

**P1 — all 18 `partial def` walks in the two capability files become
total.** They are `partial` only because Lean's structural-recursion checker
doesn't see descent through `List.any`/`List.map`/`flatMap`; the conversions
are the standard nested-recursion idiom (or `termination_by` on term size) —
no well-founded measure beyond structural size is expected anywhere.
Inventory: `Syntax.lean` — `Ty.hasUnsupported`, `Ty.beq`,
`Pattern.hasUnsupported`, `Term.hasUnsupported`, `Decl.hasUnsupported`,
`flattenDecls` (6); `CapCheck.lean` — `capsInTy`, `bodyCalls`,
`bodyAllocates`, `patBinderNames`, `termMentionsAny`, `divisionVerdict`,
`orExpansionSize`, `isCatchAllPattern`, `isModeledArmPattern`,
`patCoveredCtors`, `matchesIn`, `checkDecls` (12). The `partial def`s in
`Elab`/`Infer`/`Compare`/`Result`/`Linearity` are **out of scope**: they
serve inference, which this milestone proves nothing about, so converting
them buys no theorem.

Migration per function (or tight function group): add total definition →
rename old to `…Legacy` → `native_decide` pins `legacy = total` on every
existing fixture in the repo → full corpus run → delete legacy, same PR.

Secondary payoff: existing `native_decide` tests over converted functions
migrate to `decide`/`rfl` where kernel reduction is acceptably fast, closing
the trusted-native-evaluator hole for those sites; where `brecOn` reduction
is too slow, the pin stays `native_decide` with a one-line note. No theorem
depends on this migration.

## 5. Whole-checker theorems (phase P2)

Pressure-testing the candidate properties against the code shows all three
are **false for the full checker, true for its coverage core** — the
boundary is behavioral caps in every case. Each therefore lands as a
theorem/counterexample pair. "Coverage core" means the subsumption-coverage
checks (Check 1 signatures, Check 4 transitive use, Check 5 extern) — the
part of `checkOneModule` whose only cap reasoning is `covered declared c`.

1. **Tier order-independence.** Full permutation invariance is *known false
   by design*: behavioral-cap inheritance into nested modules is positional
   (commit `a647ad1`, march-faithful — a `dopts` before vs. after a nested
   `dmod` means different inherited caps). Pair:
   - theorem: `tier (checkCaps m)` is invariant under permutations of each
     module's decl list that preserve the relative order of `dopts` and
     `dmod` declarations (message may change; tier may not);
   - counterexample: a two-decl module (`dopts` + `dmod`) whose permutation
     flips the tier.
   Risk flag (deliberate): the restriction may need further narrowing once
   proved against the real `checkDecls`; every narrowing found is documented
   in the theorem statement as a discovered semantic dependency, never
   absorbed silently. If a narrowing is needed that is *not* march-faithful,
   that is a finding and goes to `specs/march-findings.md` instead.

2. **Normalize-stability.** Pair:
   - theorem: replacing `needs L` with `needs (normalize L)` preserves the
     verdict of the coverage core (direct corollary of `normalize_covered`
     threaded through `checkOneModule`'s Check 1/4/5 arms);
   - counterexample: `normalize ["IO", "IO.Foreign"] = ["IO"]` flips
     `hasForeignNeed`, so under `opts no_extern` the un-normalized module
     violates and the normalized one does not (`CapCheck.lean`'s
     `noExternWithForeignNeed` fixture shape). Normalization is **not** a
     verdict-preserving operation on full modules, and nothing in the
     checker may ever apply it as if it were.

3. **IO-cap monotonicity.** Pair:
   - theorem: adding a cap to `needs` never flips the coverage core from
     accept to reject (corollary of `covered_mono`);
   - counterexample: adding `needs IO.Foreign` under `opts no_extern` *is*
     the violation — declaring a capability is itself observable behavior at
     the behavioral layer.

Determinism and totality of `checkCaps` come free once P1 lands (a Lean
`def` is total and deterministic by construction) — recorded as one-line
remarks in `Calculus/CheckCaps.lean`, not padded into theorems.

## 6. Sequencing, validation, deliverables

| phase | content | shipping-code risk | gate |
|---|---|---|---|
| P0a | verdict algebra | none (additive) | `lake build` |
| P0b | lattice parameterization + metatheory + `decide` discharge | API-preserving refactor of `CapLattice.lean` | build + full corpus |
| P1 | de-partialize the 18 walks, legacy-equivalence pins | largest — `Syntax.lean` + `CapCheck.lean` | build + corpus per function group |
| P2 | three theorem/counterexample pairs | none (additive) | build |

Each phase is one PR. P0a and P0b are independent of P1 and land first; P2
requires P1. Implementation plans (via `writing-plans`): one per phase, P0a
and P0b possibly combined if the lattice refactor stays as small as
expected.

The march repo is untouched; no emitter change, no CI-pin dance. The one CI
edit is the `sorry`-grep line (§2).

## 7. Risks

- **A P1 conversion could be subtly non-equivalent.** Mitigated by the
  legacy pins + corpus; a caught divergence is a finding about the walk, not
  a nuisance. Residual risk: both legacy and total agree on all fixtures and
  corpus but differ on unexercised shapes — accepted; this is still strictly
  better evidence than today (where there is one implementation and zero
  cross-checks), and P2's theorems then constrain the total version directly.
- **Kernel reduction through `brecOn` may be too slow** for some
  `decide`/`rfl` migrations and possibly for `WellFormed hierarchy` by
  `decide`. Fallbacks, in order: `simp`-normalization first, `Nat`-indexed
  restatement, or `native_decide` for the concrete discharge only (the
  abstract theorems are unaffected). No theorem depends on which fallback is
  used.
- **The order-independence restriction may narrow further** (§5.1's risk
  flag). Handled by documentation-or-finding, never silent absorption.
- **Refactor churn vs. in-flight work.** P0b/P1 touch the two files every
  other capability slice also touches; phases are kept small and
  fast-merging to limit conflict windows.

## 8. Explicit non-goals

- No operational semantics for march programs; no soundness/completeness
  theorem relating the checker to program behavior.
- No spec-vs-implementation refinement against march's OCaml.
- No proofs about `Infer`/`Compare`/`Linearity` (their `partial def`s are
  not even converted).
- No claim that a proved checker is a *correct* oracle of march — the
  warning-tier fidelity gap (A3 design §1.3) is inherited unchanged and
  sits outside every theorem here.
