# Stage A3 — IO capability lattice conformance (design)

> Parent design docs: `specs/plans/2026-07-18-lean-conformance-bridge-stage-a.md`,
> `specs/plans/2026-07-22-a2-inference-oracle-design.md` (A2 accept side),
> `specs/plans/2026-07-22-a2-reject-oracle-design.md` (A2-reject, two-sided
> verdict; merged as march-lean #6).
>
> This is a **design doc**, not an implementation plan. It fixes the shape of
> A3. Two implementation plans follow (via `writing-plans`): one in `march`
> (the `format_version` 3 emitter change), one in `march-lean` (the checker).
>
> Authoritative source for every claim about march's behavior below:
> `march:specs/lang/core-march-types.md` §2.8 (~1,200 lines), plus the cited
> `cap_lattice.ml` / `typecheck.ml` line numbers.

## 0. What A3 is

A2-reject made `march-lean-check` a two-sided independent oracle over a Core
HM + linearity fragment. Capabilities are entirely outside that fragment: the
decoder maps an applied `Cap(perm)` to `unsupported`, so all 33 capability
corpus files skip.

**A3 brings march's IO capability lattice into the modeled fragment**, so
capability-using files are independently judged instead of skipped.

Capabilities are not one feature. §2.8 decomposes into five separable
subsystems; **A3 is scoped to the first only**:

| slice | what it checks | corpus files | status |
|---|---|---:|---|
| **a. IO cap lattice + `needs` coverage** (Checks 1, 4, 5) | `Cap(X)` signature coverage, transitive `use`, extern caps | 11 | **this milestone** |
| b. `cap_narrow` / `root_cap` threading (Checks 7, 8) | cap coercion, realtime exclusion, migrate-state IO-freedom | ~4 | later |
| c. Behavioral caps (`no_panic`/`no_alloc`/`no_extern`/`pure`/`deterministic`) | body behavior analysis | ~12 | later |
| d. Proof caps (mint / forge / unforgeability) | capability provenance | ~6 | later |
| e. Warning-tier checks (1b, 1c) | body-scanned builtins, extern-implies-`IO.Foreign` | — | **never** (see §3) |

Slice (a) was chosen because its semantic core is a pure, finite,
total lattice walk — no inference, no unification — making it the closest
this project comes to a provably-equivalent model of march.

## 1. Design decisions

1. **Scope to slice (a).** Rationale: it is self-contained, all three of its
   checks are ERROR-level (so directly verdict-relevant on both sides), and it
   is a prerequisite for slice (c) — behavioral `pure`/`deterministic` are
   defined against the same IO effect notion.

2. **Ask march to emit the cross-module cap table** (`format_version` 3),
   rather than hardcoding a stdlib cap table in the checker or skip-ledgering
   the cross-file cases. Rationale: Check 4 is inherently cross-module; a
   hardcoded stdlib table would silently rot as march's stdlib changes, and
   skip-ledgering would forfeit the transitive-`use` reject files. The
   emitter already builds the exact structure needed (§2.2), so this surfaces
   an existing value rather than computing anything new.

> **SUPERSEDED (2026-08-10).** march main `6867c783` promoted Check 1b from
> WARNING to ERROR (`typecheck.ml:9098`, `Err.error_with_fix`). Decision 3
> below was correct against the march of its time and is now obsolete: not
> implementing 1b is no longer "inheriting march's weaker guarantee", it is a
> live false-ACCEPT divergence. See `specs/march-findings.md` §5.

3. **Do NOT implement Checks 1b/1c.** They are WARNING-only in march. §2.8.6
   calls this three-tier reality "the single most consequential fact for
   anyone relying on `needs` as a soundness guarantee." A checker that
   rejected on them would manufacture false MISMATCHes against a march that
   accepts. Consequence, stated plainly: **the oracle inherits march's weaker
   guarantee here** — it will not catch a program that uses a builtin
   requiring an undeclared cap in a function body. This is a deliberate
   fidelity choice, not an oversight.

4. **Cap checks run BEFORE the skip gate** (§4). Rationale: they are purely
   declaration-level and need no inference, so a module with an
   out-of-fragment *body* but a malformed `needs` manifest can still be
   judged. This is a coverage win the obvious placement (after inference)
   would forfeit.

## 2. The model

### 2.1 The lattice (march-lean)

A faithful port of `cap_lattice.ml:39-59`. The 18-entry hierarchy becomes a
total `capParent : String → Option String`; on top of it:

- `capAncestors c` — `c` itself followed by every ancestor up to the root,
  most-specific first. A name **absent** from the table returns just itself
  (the FFI-cap base case — `go`'s `| _ -> acc'` arm). This case is
  load-bearing and must be preserved.
- `capSubsumes p c = p ∈ capAncestors c` — **reflexive** (`capSubsumes X X`
  always holds) and **directional** (a broader declared cap covers a narrower
  used one, never the reverse). Siblings never subsume each other.
- `normalize caps` — drop any cap subsumed by another cap present,
  preserving relative order of survivors.

That is the entire semantic core: pure, finite, total.

### 2.2 Emitter change (march, `format_version` 3)

Emit the typechecker's existing `env.module_caps : (string * string list) list`
— the `(module_name, that_module's_declared_needs)` association list built
incrementally at `typecheck.ml:7081` — into the envelope. This is precisely
what Check 4 consumes (`typecheck.ml:5681-5703`).

Already emitted by `lib/dump/ast_json.ml`, requiring no change: `DNeeds`
(with cap `paths`), `DUse` (with `path`), `DExtern` (with `cap_ty`). The
emitter handles every `decl` constructor, so `module_caps` is the sole
addition.

Version handling follows the A1 precedent: the checker requires the new
version exactly and exits 3 otherwise. Sequencing is therefore **march PR
first**, then march-lean pins its CI to that SHA and moves to v3.

### 2.3 The three checks (march-lean)

- **Check 1** (`typecheck.ml:5578-5607`) — every `Cap(X)` appearing in a
  module's *signatures* is covered by some declared `needs Y` where
  `capSubsumes Y X`.
- **Check 4** (`typecheck.ml:5681-5703`) — for each `use M`, every cap in
  `M`'s declared needs is covered by the importing module's own declared
  needs, via the same subsumption.
- **Check 5** (`typecheck.ml:5704-5723`) — an `extern` block's `ext_cap_ty`
  is covered by declared needs.

All three are ERROR-level and share one subsumption relation, so all of
§2.8.2's directionality rules apply identically to each.

## 3. Verdict integration

A capability violation is a **reject** — exit 1, the same class as a
linearity violation. The A2-reject exit-code contract (0/1/2/3/4) is
unchanged, and the harness needs no change beyond the CI pin bump.

## 4. Pipeline placement

Current order: decode → skip gate → inference → linearity → per-node
cross-check.

A3 inserts cap checks **first**:

1. **cap checks** — a violation ⇒ **reject (exit 1) immediately**, even if
   the body is out of fragment.
2. no violation ⇒ existing skip gate → inference → linearity → cross-check,
   unchanged.

The ordering matters: a module whose body uses unmodeled constructs but whose
`needs` manifest is wrong is judgeable under this order and skipped under the
naive one. Absence of a cap violation never *licenses* an accept on its own —
an out-of-fragment body still skips at the existing gate.

## 5. Skip-gate change

The A2-reject decoder maps applied `Cap(perm)` to `Ty.unsupported` (so cap
files skip). A3 removes that mapping and makes `Cap(X)` a first-class modeled
type.

**The 10-of-18 asymmetry.** Only 10 of the 18 hierarchy entries are
registered in `builtin_types` (`typecheck.ml:1858-1861`), though all 18 are
valid `needs` targets — flagged as a "finding" in `accept/t48`'s own comment
and in §2.8.3. Working assumption: this needs **no special handling**, because
a `Cap(X)` naming an unregistered cap does not elaborate to a valid type in
march at all, so it arrives as `TError`/`unsupported` and the existing gate
catches it. **This assumption must be verified during implementation, not
presumed.** If it proves false, the discrepancy is a genuine finding and is
escalated rather than papered over.

## 6. Testing

- **Unit (`#eval`, self-contained — no `IO.FS.readFile` of samples):** the
  lattice pinned on every shape the corpus exercises — root-covers-child,
  mid-tier subsumption, sibling non-coverage, reflexivity, absent-name
  (FFI) base case, and `normalize`'s absorption.
- **Check-level units:** hand-built modules for each of Checks 1/4/5, in both
  a covered (accept) and uncovered (reject) configuration.
- **Corpus:** the following **11** files move SKIP → MATCH. All 11 exist and
  are currently in `scripts/expected-skips.txt`; the milestone is complete
  when each has been removed from the ledger and reports MATCH.

  | file | check exercised |
  |---|---|
  | `accept/t45_cap_bare_covered` | Check 1, exact match |
  | `accept/t46_cap_broad_needs_covers_narrow` | Check 1, root covers child |
  | `accept/t47_cap_sibling_independence` | Check 1, both siblings declared |
  | `accept/t48_cap_midtier_subsumption` | Check 1, mid-tier covers descendant |
  | `accept/t49_transitive_use_covered` | Check 4, covered |
  | `accept/t50_extern_cap_and_foreign_covered` | Check 5, covered |
  | `accept/t57_cap_all_hierarchy_args` | Check 1, every valid `Cap(X)` arg |
  | `reject/t36_cap_sig_uncovered` | Check 1, uncovered |
  | `reject/t37_cap_narrow_does_not_cover_broad` | Check 1, directionality |
  | `reject/t38_cap_sibling_does_not_cover_sibling` | Check 1, sibling non-coverage |
  | `reject/t39_transitive_use_missing_cap` | Check 4, uncovered (cross-file) |

  Note `accept/t49` and `accept/t50` do not carry `cap` in their filenames;
  they are slice-(a) files nonetheless. Conversely `t44`/`t56_cap_no_extern*`
  are `no_extern` **behavioral** caps (slice c) and `t56_mint_cap_external_module`
  is a proof cap (slice d) — all three are out of scope despite matching a
  naive `cap` filename filter.

  Both the skip-ledger and known-limitations remain enforced in both
  directions throughout.
- **Forced relaxation (load-bearing-signal proof):** break `capSubsumes` so
  siblings cover each other, rebuild, and confirm at least one reject file
  flips MATCH → MISMATCH; then revert to green. Analogue of A2's `eqvTy`
  break and A2-reject's permissive-`unify` break.

## 7. Risks

- **Emitter change reopens march-side work**, with the two-repo sequencing
  and CI-pin dance A1 already exercised. Contained, but it is the main cost
  of decision 1.2.
- **Warning-tier fidelity (decision 1.3)** encodes march's weaker guarantee
  into the oracle. Documented, not hidden.
- **The 10-of-18 asymmetry** (§5) may require handling the design does not
  anticipate; treated as a finding if so.
- **`reject/t62_linear_closure_capture`** is filename-bucketed under
  capabilities but is an existing closure-capture skip. It will not move and
  is excluded from the 11.
- **A3 does not make "capabilities" a covered feature.** Of the 33
  capability-bucketed files, slice (a) claims 10; `accept/t49` is the 11th and
  comes from outside that bucket (its filename lacks `cap`). The other **23**
  cap files — slices (b) 4, (c) 12, (d) 6, plus `reject/t62` — stay skipped.
  So A3 shrinks the ledger by 11 (138 → 127); slices (b)–(d) are what finish
  the job. This is a shrinking tracker, not a claim of coverage.

## 8. Deliverables

Two implementation plans (written next, via `writing-plans`):

1. **march** — `format_version` 3: emit `module_caps`; update golden fixtures.
2. **march-lean** — the cap lattice, Checks 1/4/5, pipeline placement, skip-gate
   change, unit + corpus tests, forced relaxation, CI pin bump to the march SHA
   from (1).

`Infer` / `Compare` / the harness's exit-code mapping are unchanged.
