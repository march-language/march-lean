# R6 — a capability-soundness theorem for the checker (design)

> Parent design docs: `specs/plans/2026-08-08-calculus-proof-capabilities-design.md`
> (the proof layer this builds on — currently in flight as march-lean PR #23,
> branch `claude/calculus-proof-capabilities-0a1127`), and transitively the A3
> capability-lattice doc it cites. Upstream framing:
> `specs/2026-08-04-provable-sandbox-design.md` §R6 in the **march** repo.
>
> This is a **design doc**, not an implementation plan. Implementation plans
> follow via `writing-plans`, one per phase (§6).
>
> Authoritative sources for every claim about current behavior:
> `MarchLean/Syntax.lean`, `MarchLean/CapCheck.lean`, `MarchLean/CapLattice.lean`,
> `MarchLean/Calculus/*.lean`, at the SHA this doc is committed at.

## 0. What this is, and the sentence that must travel with it

The proof layer landed by PR #23 is **77 theorems** across `MarchLean/Calculus/`
with zero `sorry`/`admit`: the capability lattice's partial order, fuel
adequacy, `normalizeIn` idempotence, `coveredIn` monotonicity, the `CapResult`
monoid and its tier homomorphism, the `DivVerdict` join semilattice, and three
whole-checker theorem/counterexample pairs.

That substrate is real and it already pays for itself. march's
`Typecheck.check_main_grant` and `check_fn_grants` lean informally on exactly
`subsumesIn` transitivity, antisymmetry, and `coveredIn_mono`; those are now
proved rather than assumed.

**It is not a soundness theorem, and the distance between the two is most of
the work.** Every artifact produced under this design says so. The substrate
is metatheory of the checker's *algebra*; a soundness theorem relates the
checker's verdict to what a program *does*, which requires an operational
semantics that exists in neither repo today.

This document specifies the smallest such semantics that still makes the
theorem mean something, the two theorems stated over it, and — at equal
prominence — the five things it will still not prove.

## 1. Why not the ladder's R6

The sandbox ladder states R6 as:

> **Theorem (capability safety).** If `⊢ p : τ ! ε` and `p` steps to a
> configuration performing IO action `a`, then `label(a) ∈ ε`, and every
> capability in `ε` is subsumed by one reachable from `main`'s argument.

**March has no such judgment, and R1 stage C deliberately did not create one.**
Stage C built effect rows *beside* the type system: `lib/caps/cap_rows.ml`
carries `{caps; deps; unknown}` per function, while `ty`, `unify`, `generalize`
and `pp_ty` are untouched and no printed type changed. The ladder's own stage-C
update says as much — R6 "would need either provenance tracking through data or
the in-`ty` formulation this deliberately deferred."

So targeting `⊢ p : τ ! ε` means (a) inventing the judgment, (b) proving
march's checker refines it, where (b) is an explicit non-goal of the parent
design doc for good reasons. The ladder itself warns against this exact move in
§4: *"a proof over a calculus that does not match the implemented language is
an academic artifact, not an assurance."*

The alternative is to state the theorem **about the checker that exists**:

> If `checkCaps m = ok` and `m` steps to a configuration performing IO action
> `a`, then `label(a)` is covered by `m`'s declared capabilities.

This attaches to `checkCaps : Module → CapResult` (`CapCheck.lean:2162`) — a
definition the oracle runs, that the conformance harness exercises, and that P1
will have made total and inductable. It honors the parent doc's standing
principle: metatheory of the shipping code, not a shadow model.

Two constraints found while pressure-testing it, both real and both reflected
below:

- **`checkCaps` runs on modules the fragment does not model.** `Term.opaque_`
  carries children whose *shape* is unmodelled, and it exists precisely because
  cap-checking runs *before* the fragment gate (`MarchLeanCheck.run` invokes
  `checkCaps` first, by design). A step relation cannot reduce an `opaque_`.
  The theorem's hypothesis is therefore `checkCaps m = ok` **and** `m`
  in-fragment — strictly fewer modules than the checker accepts. §5.3.
- **`checkCaps` is per-module and coverage-based; it has no grant.** The word
  `grant` occurs twice in `CapCheck.lean`, both inside R2's `root_cap`
  message. Grant soundness is a different theorem shape — whole-program
  reachability from a root, not per-module coverage — and is a follow-up.
  §5.2.

## 2. Design decisions

1. **State it over `checkCaps`, not over an invented judgment.** §1.

2. **No mathlib**, inherited unchanged from the parent doc. The step relation,
   its reflexive-transitive closure, and the trace algebra are hand-rolled
   inductives over `List String` and small `Prop`s. The zero-dependency
   cold-build property is worth more than the lemmas.

3. **Substitution-based semantics, not environments or closures.** A closure
   representation would introduce a second binding structure and a second set
   of lemmas about it. `subst : String → Term → Term → Term` is total,
   structural, and reuses the P1 de-partialization idiom already established.

4. **`Step` is an inductive `Prop`, not an executable function.** Preservation
   is proved by induction on the step derivation; an executable evaluator gives
   no induction principle worth having. An executable *fuel* evaluator is
   nevertheless built in S4, for a different purpose — differential testing
   against march (§5.6), not proof.

5. **The IO rule is nondeterministic in its result.** `app (var b) vs --[b]--> v`
   for **any** value `v`, where `b ∈ ioBuiltins` and `vs` are values. This is
   the move that lets the theorem quantify over every possible IO outcome
   without modelling a world, a heap, or a filesystem. Nothing in either
   theorem depends on what IO returns — only on which builtin was reached.

6. **δ-reduction is how the call graph enters the semantics.** `var f`, where
   `f` is a decl of `m`, unfolds to its body. This is the pivot of the whole
   design: `bodyCalls`' syntactic transitive closure is exactly the
   over-approximation of δ-reachability, which is what makes T1 provable at
   all and what makes its central lemma a *falsifiable* claim about the
   checker (§3.3).

7. **Trusted base is stated per theorem.** T1, T2 and every lemma are
   kernel-checked; `Step` is a `Prop` inductive, so no theorem in S0–S3 can
   use `native_decide` even in principle. Where a counterexample or a
   differential pin uses `native_decide` — S4 does, throughout — it is marked
   at the site, and the Lean compiler enters the trusted base for that pin
   only. The parent doc's rule stands: any theorem whose statement someone
   might quote says which it used.

8. **The `sorry`/`admit` CI gate stays**, and nothing lands behind it.

## 3. The semantics and the proof spine

### 3.1 `MarchLean/Calculus/Semantics.lean`

- **`Value : Term → Prop`** — `lit`, `lam`, and `con`/`tuple`/`record` whose
  components are values.
- **`subst : String → Term → Term → Term`** — total, structural, capture-free
  by the usual freshness side condition on `lam`/`let_`/`letfn`/`match_` arms.
- **`Step (m : Module) : Term → Option String → Term → Prop`** — silent
  (`none`) for β, δ, `ite`, `match_` arm selection, and `field` projection;
  labelled (`some b`) for exactly one rule, the builtin IO application of §2.5.
- **`Steps (m : Module) : Term → List String → Term → Prop`** — reflexive
  transitive closure accumulating the labels, in order.

The modelled fragment is the in-fragment `Term` constructors: `lit`, `var`,
`app`, `lam`, `let_`, `letfn`, `ite`, `con`, `tuple`, `record`, `field`,
`match_`. `opaque_` and `unsupported` are excluded by the `¬ hasUnsupported`
hypothesis, not by a missing rule — the difference matters, because the skip
ledger then gives a machine-checked account of what that hypothesis excludes
rather than a prose caveat.

### 3.2 T1 — capability safety, coverage core

> If `m`'s coverage core accepts, `m` is in-fragment, and a closed entry term
> drawn from a decl of `m` reduces with IO trace `tr`, then every builtin in
> `tr` has its capability covered by `m`'s declared `needs`.

"Coverage core" carries the parent doc's meaning exactly: the
subsumption-coverage checks (Check 1 signatures, Check 4 transitive use,
Check 5 extern) — the part of `checkOneModule` whose only cap reasoning is
`coveredIn hierarchy declared c`.

**Entry is closed.** The theorem quantifies over a closed entry term, not over
a decl applied to arbitrary arguments. This is not a convenience: if a caller
may supply a *function value*, that closure can contain any builtin at all and
no per-module analysis bounds it. That is precisely the case R1 stage C
**refuses** rather than types ("a function value laundered through a data
structure is REFUSED under a narrow grant"). Closing the entry closes the hole
by construction instead of assuming it away. §5.4 states what that costs.

### 3.3 The invariant, and where it can find a bug

Define `callNames m t` — builtin names semantically reachable from `t` via
subterms plus δ-unfolding within `m`. Three lemmas carry T1:

1. **Substitution.** `callNames m (subst x v t) ⊆ callNames m t ∪ callNames m v`
2. **Preservation.** `Step m t l t' → callNames m t' ⊆ callNames m t`, and
   `l = some b → b ∈ callNames m t`
3. **Bridge.** `callNames m d.body ⊆` the transitive closure `bodyCalls` /
   Check 4 actually computes.

Lemma 3 is load-bearing and is the reason this milestone is worth doing at all.
It is a *checkable* claim that march's syntactic transitive closure
over-approximates real δ-reachability. **If it does not go through, the failure
is a candidate false-accept in the checker** — a finding for
`specs/march-findings.md` with a reproducer and both exit codes, filed
upstream, not a weakened theorem. This is the same discipline the parent doc
applies to P2's order-independence narrowing.

The standing rule applies here too: a green corpus run would not have found
this. The corpus finds nothing; the lemma either goes through or names a bug.

### 3.4 T2 — `no_panic` soundness

> If `m` is accepted under `cap no_panic`, no reduction from an entry term
> reaches a panic configuration.

T2 is nearly free once §3.1 exists, and it is of genuinely different character
from T1 — a stuck-configuration property rather than a trace property. The two
panic configurations in the modelled fragment are division by zero and
non-exhaustive `match`, which are exactly what `divisionVerdict` and
`matchExhaustive` already compute. No new semantic notion is introduced.

The other behavioral caps are **not** covered: `no_alloc` needs an allocation
model, `deterministic` needs a two-run relation, `pure` needs both. Each is a
separate semantic notion and none is in this milestone. This is the same
boundary the parent doc's §5 found empirically — the behavioral-cap layer is
where every algebraic law breaks, and it is where soundness stops too.

## 4. Shape

```
MarchLean/Calculus/Semantics.lean   -- values, subst, Step/Steps, basic lemmas
MarchLean/Calculus/Reachable.lean   -- callNames, substitution + preservation
MarchLean/Calculus/Soundness.lean   -- T1, the §3.3 bridge, T2
MarchLean/Calculus/Eval.lean        -- S4 only: fuel evaluator + differential pins
```

Imported from `MarchLean.lean` so the existing CI `lake build` kernel-checks
every theorem on every push, and the `sorry`-grep gate covers them.

Shipping behavior is unchanged throughout: S0–S3 are purely additive. S4 adds
an evaluator that nothing in the oracle's verdict path calls.

## 5. What this will NOT prove

Stated here, and restated in every artifact, README line, or claim derived from
this work.

1. **Nothing about march's OCaml.** All of this is metatheory of the Lean
   re-implementation. `CapLattice.lean`'s table mirrors
   `lib/caps/cap_lattice.ml` by hand, and `Concrete.lean`'s `decide` protects
   the *Lean* table's well-formedness — a divergence between the two tables is
   precisely what no theorem here can see. The conformance harness is the only
   thing that covers it, which is one more reason the R1 resync matters
   independently of this milestone.

2. **Nothing about `main`'s grant.** T1 says *covered by declared `needs`*. A
   module whose `needs` is truthful but wildly excessive satisfies T1
   completely. The grant is R1, it is not modelled in `CapCheck.lean` at all
   today, and grant soundness is a follow-up theorem of a different shape
   (whole-program reachability from a root).

3. **Nothing about out-of-fragment modules.** `opaque_` and `unsupported` are
   excluded by hypothesis. The skip ledger makes that exclusion
   machine-checked and enumerable rather than a caveat — but it is still an
   exclusion, and it is not small.

4. **Nothing about open entry.** Caller-supplied function values are outside
   T1 (§3.2). The theorem is about whole-module entry, so it says nothing about
   a library function invoked by an application the analysis never saw. That
   is the compositional claim stage C makes informally, and T1 does not
   discharge it.

5. **No actors, `spawn`/`send`, FFI, or console egress.** The ladder's own
   note stands: no stage closes console egress, and this one does not either.

6. **The semantics is invented here and is not march's.** This is the sharpest
   risk in the document. A semantics nobody cross-checked can be internally
   consistent and simply wrong about the language, in which case T1 is a true
   theorem about a fiction. S4 is the mitigation — an executable fuel
   evaluator differential-pinned against march's own evaluator across the
   corpus, in exactly the spirit of the existing A2 oracle. **Without S4,
   "for the modelled fragment" also means "for a semantics we asserted."**

## 6. Sequencing, validation, deliverables

| phase | content | shipping-code risk | gate | blocked by |
|---|---|---|---|---|
| S0 | `Semantics.lean` — values, `subst`, `Step`/`Steps`, basic lemmas (values don't step; labels come only from the IO rule) | none (additive) | `lake build` + sorry gate | — |
| S1 | `Reachable.lean` — `callNames`, substitution + preservation | none (additive) | build | S0 |
| S2 | **T1** and the §3.3 bridge | none (additive) | build + full corpus | S1, **P1** |
| S3 | **T2** (`no_panic`) | none (additive) | build | S1 |
| S4 | `Eval.lean` — fuel evaluator, differential pins vs. march's evaluator on the corpus | none (not on the verdict path) | build + corpus + differential run | S0 |

Each phase is one PR. Implementation plans via `writing-plans`, one per phase.

**S2's prerequisite is concrete, not notional.** `bodyCalls`
(`CapCheck.lean:560`) and `checkDecls` (`:2120`) are still `partial def`, so
Lean gives them no equation lemmas: they can be neither inducted on nor
`decide`d. P1 de-partialization is a hard prerequisite for T1 specifically —
S0, S1, S3 and S4 are not blocked on it.

Note that the parent doc scopes P1 to the 18 walks in `Syntax.lean` and
`CapCheck.lean` only, and explicitly rules the `Elab`/`Infer`/`Compare`/
`Result`/`Linearity` walks out of scope as buying no theorem. Nothing in this
design changes that: none of S0–S4 needs them either.

## 7. Risks

- **Lemma 3.3 does not go through.** Treated as the *success* case for finding
  a bug, not as a project risk: it becomes a march finding with a reproducer.
  The genuine risk is the third outcome — it goes through only under a
  narrowing that is not march-faithful. Per the parent doc's rule, that is a
  finding, never a silently weakened theorem.
- **Substitution capture handling balloons.** The standard failure mode of a
  first mechanization. Mitigation: the modelled fragment's binders are all
  simple (`lam` params, `let_`, `letfn`, `match_` arm binders). Note that
  shadowing is *not* a rare shape in this repo — `scripts/tailcall-probes/`
  carries six deliberate shadowing probes (`shadow_let`, `shadow_letfn`,
  `shadow_match`, and three `shadow_edge_*`), so capture-avoidance must be
  done properly rather than assumed away. If it proves expensive, a
  Barendregt-convention side condition on the entry term is the fallback, and
  it is documented as a hypothesis rather than absorbed.
- **S4 finds the semantics is wrong.** Also a success case, and the reason S4
  exists. It roughly doubles the milestone and is worth it: it is the only
  phase that produces evidence about the semantics rather than from it.
- **Refactor churn vs. in-flight work.** `MarchLean/Calculus/` is also being
  edited by the P1/P2 work on `claude/calculus-proof-capabilities-0a1127`.
  S0–S4 add new files and touch `MarchLean.lean` only, to limit the conflict
  window.

## 8. Explicit non-goals

- No spec-vs-implementation refinement against march's OCaml (inherited from
  the parent doc, unchanged).
- No grant (R1) soundness theorem — §5.2.
- No behavioral caps beyond `no_panic` — §3.4.
- No claim that a proved checker is a *correct* oracle of march: the
  warning-tier fidelity gap (A3 design §1.3) is inherited unchanged and sits
  outside every theorem here.
- **No claim that R6 is reached.** Two theorems over an asserted semantics for
  a modelled fragment of one module, without the grant, is not "provably
  capability-safe." The ladder's stage 4 requires R6 *and* R7, and R7 — the
  bridge from the theorem to the shipping OCaml — is untouched by this
  document.
