# Capability closure and grant proofs — 2026-11-06

**Follow-up:** [Task 3 and latest main validation](2026-11-07-scoped-authority.md).

Plan: `specs/plans/2026-11-06-future-theory.md`, Task 2.

## Result

The executable capability checker now uses a finite closure algorithm with
kernel-checked soundness, completeness, fuel adequacy and least-fixed-point
proofs. Its actual `checkGrant` function accepts exactly when every reachable
IO effect is covered by a grant. Rejections include a valid, deterministic call
path, for example:

```text
main's capability grant does not cover reachable `IO.Console`
(call path: main → first → second → third)
```

This is a theorem about the finite effect graph extracted by the checker,
**not** a source-level soundness theorem for March or the OCaml exporter.

## Definitions and main theorems

| File | Role |
| --- | --- |
| `MarchLean/EffectGraph.lean` | Executed table lookup, propagation step, tail-recursive closure, cached witness search |
| `MarchLean/GrantCheck.lean` | Executed uncovered-capability search and acceptance predicate |
| `MarchLean/Calculus/Reachability.lean` | Declarative reachability, concrete paths, closure/fuel/least-fixed-point and witness proofs |
| `MarchLean/Calculus/Grants.lean` | Grant equivalence, monotonicity, rejection witnesses and CLI bridges |
| `MarchLean/EffectGraphTests.lean` | Finite graph and binder regression examples |
| `scripts/check-closure-axioms.lean` | CI-enforced dependency audit of ten public results |

The graph is the existing list-of-rows representation, with **first-match
lookup**. Its vertex domain is the initial row names. The results do not assume
unique keys or that every edge target has a row: duplicate keys retain the
actual first-match semantics and dangling names acquire no effects.

- `step_inflationary`, `step_monotone`, `rounds_mono_fuel`,
  `rounds_monotone`: propagation grows effect sets and respects inclusion on a fixed row domain.
- `simple_path`, `bounded_simple_path`: every inductively reachable effect has
  a duplicate-free call path contained in the finite vertex domain. Cutting at
  a repeated vertex removes cycles; its length is at most the row count.
- `closeRows_eq_rounds`: the original tail-recursive executable equals the
  induction-friendly synchronous iteration.
- `inferReach_sound`, `inferReach_complete`, `inferReach_iff`, `fuel_adequate`:
  the actual row-count fuel computes exactly declarative reachability. Every
  larger fuel gives the same effect membership, including the empty graph.
- `inferReach_contains_initial`, `inferReach_closed`, `inferReach_least`,
  `inferReach_fixed`: the result is the least closed superset of the seed
  effects. Equality is extensional effect-set equality, not row order.
- `history_succ`, `buildHistory_current`, `findPath_succ`: cached witness
  traversal satisfies the original decreasing-fuel recurrence, including its
  deterministic edge-order choices.
- `findPath_sound`, `findPath_complete`, `inferReach_witness`: the executable
  search produces a valid finite call path for every reported effect. It is
  not claimed to return the shortest or a duplicate-free path; the simple-path
  existence theorem establishes the fuel bound independently.
- `grant_accept_iff`, `grant_accept_iff_subsumes`: acceptance is precisely
  coverage of all reachable IO effects by declared grants and lattice
  subsumption. Non-IO proof/FFI roots are outside this grant judgment.
- `grant_mono`: adding grants preserves acceptance for this judgment; it says
  nothing about behavioral checks such as `no_extern`.
- `checkGrant_ok_iff`: the theorem applies to the `CapResult`-returning function
  actually called by `CapabilityReach.check`, not merely a parallel predicate.
- `executable_bridge`, `effectGraph_vertices`: the graph entry point agrees
  with the prior `closeRows fs.length` call.
- `grant_reject_witness`: an uncovered capability is IO, is not covered, and
  has the executable call-path witness used in the diagnostic.

## Trust boundary

The public theorems depend only on Lean’s standard `propext`, `Classical.choice`
and `Quot.sound` (some need fewer). No new axioms, proof placeholders or native
computation axioms occur in their transitive dependencies. The CI audit fails
on any additional axiom, including an oracle axiom hidden behind a helper.
Finite `native_decide` binder tests remain tests and are not premises of these
theorems.

The following are **not proved here**: source name resolution, builtin effect
table correctness, completeness of exported source obligations, the partial
AST reference/extraction walks, or operational effects of a March execution.
The existing skip boundaries remain. Graph edges and direct effects are inputs
to this theorem layer, not facts magically certified by it.

## Verification

- `lake build`: 42 jobs, library/proofs/tests and executable successful.
- `lake env lean scripts/check-closure-axioms.lean`: ten public theorems pass
  the standard-axiom allowlist. A temporary custom-axiom mutation fails the
  same gate, naming the injected dependency.
- Four-vertex chain mutation: changing its required three propagation rounds
  to two makes its `decide` regression fail. The unmodified test passes.
- Graph regressions cover chains, cycles, diamonds, deterministic tie-breaking,
  disconnected functions, missing vertices, duplicate rows, empty graphs,
  union/root grants, non-IO roots and shadowed/captured names.
- 17 real-source sync probes pass, including verdict/diagnostic mutations. New
  probes verify closure-body charging, an unreachable effectful helper and a
  transitive rejection’s call-path text against March `977e04e1d`.
- Existing 22 tail-call probes pass.
- The 601-file conformance gate uses the same pinned compiler captures as the
  main-sync audit and freshly executes the checker; it passes with
  108 matches, 492 explicit skips and one export limitation.

## Review and execution rulings

1. **Graph layer first:** use the actual finite tables rather than wait for
   Task 1’s proposed `ResolvedModule` interface. The public theorems state the
   graph-level boundary explicitly. Cost: source/export correctness remains a
   separate task; these results must not be advertised as full March soundness.
2. **Fuel mutation:** the executable uses `n` rounds, while a simple path over
   `n > 0` vertices needs at most `n - 1` edges. Merely changing `n` to `n - 1`
   is therefore not a meaningful negative test. Mutate the four-node chain’s
   tight three-round check to two instead. The implementation retains its
   original conservative bound.
3. **Performance review fixed:** the first witness implementation recomputed
   closure at every hop. A reviewer identified the extra factor in path
   length. `buildHistory` now computes each row table once; `findPath_succ`
   proves preservation of the original choice rule. A cached-history regression
   failed before this API existed and passes afterward. A 101-function chain
   measured 6,563 ms before and 143 ms after, with the same 101-node witness,
   on the same local machine. These measurements are evidence for this case,
   not a timing threshold or a general benchmark guarantee. Retaining the
   round history trades memory for avoiding repeated propagation.

The independent review found no correctness defects in the closure, grant or
witness statements. Its performance finding was fixed with the proof and tests
above. The prior main-sync changes and these proof changes are included in the
Task 2–3 delivery branch.
