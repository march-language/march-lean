# March Lean: executable soundness theory implementation plan

> **For agentic workers:** Use `superpowers:executing-plans` to implement this plan task by task. Completed milestones are marked below; unchecked tasks remain future work.

**Goal:** Turn the checker’s useful finite examples into general theorems about capability authority and linear ownership, with an explicit bridge to the code the executable runs.

**Architecture:** Keep the executable oracle and its proof layer together. Totalize only definitions needed for the next theorem, prove their relationship to a small declarative specification, and preserve the real March conformance tests. An unsupported feature must remain an explicit skip rather than be erased into an acceptance.

**Tech stack:** Lean `leanprover/lean4:v4.29.0`, Lean core libraries, the existing zero-package Lake project, and March’s format-version-3 core-AST export.

**Spec:** This document defines the proposed theory scope, extending `2026-08-08-calculus-proof-capabilities-design.md`; `2026-11-06-march-main-resync.md` records the concrete baseline.

## Why this direction

The existing `Calculus` files already prove finite-hierarchy well-formedness, reflexivity/transitivity/antisymmetry of subsumption, coverage preservation and idempotence of the abstract normalizer, verdict algebra, and structural-walk equations. They also exhibit counterexamples to lifting coverage monotonicity and normalization invariance to the entire behavioral checker. Those are useful results; the old design’s statement that the repository has “zero theorems” is historical.

What is missing is the bridge from those algebraic laws to a judgment about a program. A green differential run is not such a bridge: most current fixtures skip, and important errors have needed hand-built witnesses. Nor does a finite `native_decide` example establish a universally quantified soundness theorem. The proposed next result is therefore **reachability soundness for the actual capability checker**, followed by **ownership preservation for a precisely delimited linear core**.

Three attractive directions were considered:

| Direction | Value | Decision |
| --- | --- | --- |
| Capability reach and grants | Directly strengthens the new checker, exercises finite fixpoints, exposes authority leaks | First |
| Linear ownership and moves | Explains the newly fixed rebinding hole and existing branch/capture limitations | Second, after foundational scope work |
| Full actor/session/distributed semantics | High eventual value, but emitter omissions and runtime assumptions currently dominate the proof | Later, after a small typed core and explicit protocol export |

## Global constraints

- Keep Lean pinned at `leanprover/lean4:v4.29.0`; no Mathlib dependency in these first milestones.
- No `sorry`, `admit`, or new axioms. Record the axioms of public soundness theorems with `#print axioms`; distinguish native evaluation pins from general kernel proofs.
- Import every proof module from `MarchLean.lean`; `lake build` must check it.
- Never consult March’s verdict or diagnostics to decide acceptance/rejection. Mutation tests must continue to demonstrate independence.
- State a `Supported` predicate and all environment assumptions in every program-level theorem. A skip proves nothing about the source program.
- Fix a discovered false theorem by narrowing its justified statement or adding a counterexample, never by weakening the implementation’s safety checks to fit the theorem.
- Each implementation PR reruns the pinned corpus and focused probes. A changed skip set requires a reasoned ledger diff.
- Theorems about a new abstract representation need a proved translation/commutation lemma to the shipping representation before being described as checker guarantees.

## Review focus

1. Shadowing, file-qualified names, nested modules, and duplicate declarations must not create spurious effect edges (Tasks 1–2).
2. Recursive components, diamonds, unreachable functions, and effects hidden in closures must not defeat or overstate closure (Task 2).
3. `/etc` versus `/etcpasswd`, `..`, empty scope, and absolute versus relative roots must not broaden filesystem authority (Task 3).
4. A moved resource’s obligation must survive aliases, shadowing, and exclusive branches; panic/divergence assumptions must be explicit (Task 4).
5. Erased source obligations, malformed envelopes, and unsupported annotations must not become a source-soundness claim (Tasks 1 and 5).

## Task 1: Make the acceptance boundary a first-class judgment

**Files:** Create `MarchLean/Calculus/Fragment.lean` and `MarchLean/Calculus/Resolution.lean`; modify `Syntax.lean`, `Elab.lean`, `CapabilityReach.lean`, `MarchLeanCheck.lean`, and `MarchLean.lean`.

**Interfaces:** Define `SupportedModule : Syntax.Module → Prop` and a resolved finite function graph with unique identifiers. Define `resolveModule : Syntax.Module → Except UnsupportedReason ResolvedModule`. Keep unsupported and malformed inputs distinct.

- [ ] Specify exactly which terms, declarations, annotations, scopes and imported information support an acceptance. Include top-level values, externs, proof dictionaries, function `needs`, and type-level linearity in the boundary audit.
- [ ] Add failing counterexamples for lexical shadowing, nested/file-qualified aliases, duplicate declarations, and unsupported fields that the current exporter erases. For absent information, specify an exporter change rather than fabricate Lean evidence.
- [ ] Replace partial free-reference traversal with a total structural traversal over the modeled syntax. Prove `references_excludes_bound` and alpha-renaming invariance for fresh binder renaming.
- [ ] Prove `resolve_success_supported`: successful resolution supplies the graph’s uniqueness and scope invariants. Prove that resolving a bound local never yields a global builtin edge.
- [ ] Factor the executable verdict decision out of `IO` into a pure function and prove `accept_implies_supported`. This theorem is only about the declared fragment, not March source semantics.
- [ ] Validate with `lake build`, the conformance harness, and mutation probes that alter verdicts, diagnostics and unsupported annotations independently.

**Exit criterion:** Every future program-level proof can name one explicit support/resolution assumption, and the executable actually enforces it.

## Task 2: Prove capability closure and grant checking

**Implemented 2026-11-06:** See [proof results and trust boundary](../progress/2026-11-06-capability-closure-proofs.md).
The implementation uses the existing finite row tables as `EffectGraph.Graph`;
source resolution and the broader Task 1 export/support contract remain open.

**Files:** Create `MarchLean/Calculus/Reachability.lean` and `MarchLean/Calculus/Grants.lean`; modify `CapabilityReach.lean` and `MarchLean.lean`.

**Interfaces:** Over Task 1’s graph, define `DirectEffect : FnId → Cap → Prop`, `Calls : FnId → FnId → Prop`, and inductive `Reaches` with direct-effect and call-transitivity rules. Expose `inferReach : ResolvedModule → EffectRows` and `grantCovers : List Cap → List Cap → Bool`.

- [x] Add examples for a long chain, mutual recursion, a diamond, an unreachable effectful helper, a same-named local, and a captured callable. Pin whether closure creation or invocation contributes the effect by reference to the audited March rule; do not silently choose conventional effect semantics.
- [x] Prove each row iteration is inflationary and monotone under row inclusion.
- [x] Prove finite stabilization: with `n` graph vertices, `n` synchronous rounds cover every simple path; cycles add no new vertex on a shortest effect witness. Handle the empty graph explicitly.
- [x] Prove `inferReach_sound` and `inferReach_complete` against `Reaches`, plus the least-fixed-point property. These are about the modeled graph; imported summaries and builtin tables are explicit assumptions.
- [x] Prove `grant_accept_iff`: grant acceptance is equivalent to every reachable IO capability being subsumed by some declared grant. Derive that increasing grants preserves acceptance **for this grant judgment only**.
- [x] Prove a bridge from the list-based rows executed by `CapabilityReach.closeRows` to the finite graph specification. Either keep that implementation definitionally shared or replace it with the verified function.
- [x] Add a witness-producing reject result: a finite call path ending in the uncovered capability. Prove witness validity and test deterministic witness selection separately from verdict correctness.
- [x] Validate with `lake build`, focused grant/shadowing probes and the full pinned corpus. Deliberately remove one propagation round in a temporary mutation and require the chain test to fail.

**Exit criterion:** The CLI’s supported grant check executes a closure algorithm with kernel-checked termination adequacy and a proved specification. No claim about external code or full March execution yet.

## Task 3: Scoped authority and canonical normalization

**Implemented 2026-11-07:** See [scope results, current March environment rule, and export limits](../progress/2026-11-07-scoped-authority.md).

**Files:** Create `MarchLean/CapScope.lean` and `MarchLean/Calculus/Scopes.lean`; modify `CapLattice.lean`, `Calculus/Concrete.lean`, `Syntax.lean`, `Elab.lean`, `CapCheck.lean` and scope probes.

**Interfaces:** Define `Scope := unbounded | path (absolute : Bool) (segments : List String)` and `Authority := Cap × Scope`. `subsumesAuthority` combines capability ancestry with segment-prefix containment. Keep raw declared manifests separately for behavioral checks that inspect syntax.

- [x] Pin the OCaml scope examples: `/etc` contains `/etc/a` but not `/etcpasswd`; `/a/../etc` normalizes lexically; absolute and relative roots differ; unbounded subsumes bounded, never conversely. Distinguish the emitter’s empty-string sentinel from an actual path syntax decision.
- [x] Prove scope subsumption reflexive and transitive; prove antisymmetry on canonical scopes. Lift the existing capability order to the product authority order.
- [x] Bring concrete `CapLattice.normalize` into agreement with March’s deduplicate-first behavior, preserving survivor order. The existing abstract normalizer currently preserves duplicate entries; do not relabel its old theorem as proof of the new operation.
- [x] Prove duplicate-free output, idempotence and coverage preservation for the new concrete operation. Reprove all `Concrete` and `CheckCaps` bridges and retain the `no_extern` normalization counterexample.
- [x] Preserve scoped declarations in decoding and discharge the skip only after all scoped coverage checks use `Authority` rather than bare strings.
- [x] Validate both raw JSON and actual March source probes, plus full conformance.

**Exit criterion:** Lexical path restrictions survive the export/decode/check pipeline. Explicitly exclude filesystem symlink resolution, race freedom and OS sandbox enforcement; those require a runtime model.

## Task 4: Linear ownership, moves and branch joins

**Files:** Create `MarchLean/Calculus/Ownership.lean` and `MarchLean/Calculus/LinearCore.lean`; modify `Linearity.lean`, `Syntax.lean`, and linearity regression probes.

**Interfaces:** Define finite resource identities independently of variable names; `Owns Γ x r` records ownership. Define a judgment `Uses Γ term Γ'` for the supported core, distinguishing returning and non-returning paths. Aliasing transfers the identity rather than allocating a new resource.

- [ ] Start with let, variables, constructor components and conditionals. Exclude escaping closures, actor state and arbitrary recursive calls from the first theorem.
- [ ] Add counterexamples for rebind-and-drop, repeated rebinding, rebind-and-use-twice, shadowed aliases, one branch dropping a value, both branches consuming once, and a branch that terminates by panic. An affine value may be dropped; a linear one may not be dropped on a returning path.
- [ ] Prove move preservation: `let y = x` removes the old ownership binding and creates exactly one new binding for the same resource.
- [ ] Prove branch-join compatibility and no duplication for accepted expressions. Do not use a sum across mutually exclusive branches or a maximum to hide a zero-use branch.
- [ ] Introduce a small-step store semantics and prove one-step ownership preservation for this core. Derive “no duplicated live owner” and “no silently lost linear owner on normal return.”
- [ ] Prove the executable analysis sound for `Uses`, then wire it into `checkLinearity`. Keep unsupported closure cases explicit until a later usage/escape analysis is proved.
- [ ] Validate with `lake build`, both newly added move probes and the existing linearity corpus; mutation must catch removal of the transfer step.

**Exit criterion:** A resource safety theorem about an explicit small language, connected to the CLI’s admitted linear fragment. This is not yet a theorem about March’s reference-counting runtime.

## Task 5: A typed operational core and honest source bridge

**Files:** Create `MarchLean/Calculus/CoreTyping.lean`, `CoreStep.lean`, `TypeSafety.lean`, and `ExportContract.lean`; modify inference/decoder modules only as the bridge requires.

- [ ] Specify a monomorphic call-by-value core with literals, functions, let, conditionals, tuples and algebraic constructors. Extend to polymorphic let only after substitution/generalization invariants have been proved.
- [ ] Define declarative typing, values and reduction. Prove weakening, substitution, canonical forms, preservation and progress; make builtin typing and effect contracts explicit parameters.
- [ ] Prove the independent inferencer sound against that judgment for supported inputs, including occurs-check and substitutions. Partial inference must first acquire a justified total specification or a fuel/result theorem; a convenient unproved “inference is correct” premise is not completion.
- [ ] State a source-to-core export relation. Decide which obligations must survive elaboration as evidence; the existing erased `derive` errors show why core typing alone cannot imply source acceptance.
- [ ] Produce the combined theorem only with an explicit valid-export hypothesis. Keep OCaml exporter correctness in the trust boundary until separately proved or translation-validated.

**Exit criterion:** Preservation/progress for a real typed subset, and a precise statement of what connects that subset to March. Do not title this “March is sound.”

## Later research gates

**Sessions:** Begin with finite two-party protocols, duality and communication fidelity; extend to multiparty projection only after mergeability is modeled. Protocol annotations, role grants, recursion and crash branches must be exported before source-level claims. Prove neither global deadlock freedom nor eventual delivery without explicit fairness/transport assumptions.

**Actors and supervision:** Model one mailbox and one transition system first. Then study restart capability non-escalation and state migration preservation. Keep crash/restart interleavings and message duplication visible.

**Compiled resource safety:** A Perceus/TIR ownership simulation is a separate bridge after Task 4; prove individual transformation preservation before attempting end-to-end runtime memory safety.

## Recommended next implementation slice

Tasks 2 and 3 are implemented at the finite-graph and lexical-authority boundary. Next, complete Task 1’s resolution/total-reference and export-support contract, then Task 4’s ownership core. Preserve the executable bridges, counterexamples and corpus evidence in each milestone; full sessions and actors should not displace these foundations.
