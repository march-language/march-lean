# Stage A2-reject — two-sided verdict oracle (design)

> Parent design docs: `specs/plans/2026-07-18-lean-conformance-bridge-stage-a.md`,
> `specs/plans/2026-07-22-a2-inference-oracle-design.md` (A2 accept-side, merged
> as march-lean #5).
>
> This is a **design doc**, not an implementation plan. It fixes the shape of
> A2-reject. One implementation plan follows (via `writing-plans`), in the
> `march-lean` repo. **The march emitter is unchanged** — A2-reject consumes the
> existing `format_version` 2 output.

## 0. What A2-reject is

A2 (accept side) made `march-lean-check` an independent Hindley–Milner checker
for accept-verdict programs, but it **skips every reject-verdict file** at the
verdict gate — it never confirms that march was *right* to reject.

**A2-reject removes that skip and makes the checker render its own accept/reject
verdict on every in-fragment file, ignoring march's verdict entirely.** The
accept/reject *comparison* moves out of `march-lean-check` and into the harness:
the checker answers only "is this program well-typed, by my own inference +
linearity?", and the harness compares that answer to march's. This is the
concrete meaning of the two design decisions:

1. **Verdict-level agreement** — a reject file is a MATCH iff A2 *also* rejects
   it (A2's inference or linearity finds it ill-typed). A2 accepting a
   march-rejected program is a MISMATCH. We do NOT compare *why* they reject —
   only that they do.
2. **Pure-independent code** — `march-lean-check` never reads march's `verdict`
   or `diagnostics`. It judges the program on its own and emits its own verdict;
   the harness owns the differential comparison. Scoping (which reject files A2
   is responsible for) is done structurally (the whole-file skip gate) plus a
   triage-driven skip-ledger, never by consulting march's stated reason.

Same HM engine, same Core+linearity fragment as A2. The reject files simply stop
being skipped and start being judged. The march emitter is untouched.

### The value, honestly

The reject corpus (82 files) is entirely *genuinely ill-typed* programs (it is
march's own reject test suite). So on this corpus, A2-reject:
- **Confirms** the in-fragment rejections are independently reproducible (a
  second HM implementation also finds them ill-typed) — differential confidence,
  and a CI tripwire against future march completeness regressions.
- **Forces A2 to model enough** to catch them (or honestly skip-ledger what it
  can't) — a completeness-forcing exercise.

It will NOT find march *over-rejecting* (wrongly rejecting a valid program) on
this corpus, because every file here is supposed to be rejected. That
bug-catching payoff — march wrongly rejecting real code — comes from running the
now-two-sided oracle on programs *outside* the curated corpus. A2-reject is the
capability; the curated corpus is its test bed.

## 1. Design decisions

1. **Verdict-level, reject side** (the semantics decision). Both must reject; a
   reject-reason mismatch is not flagged. Rationale: verdict agreement is the
   meaningful differential signal; matching error *reasons* between two
   implementations is a rabbit hole of spurious reason-mismatches for little
   added assurance.

2. **Pure-independent code** (the scoping decision). `march-lean-check` reads
   neither march's `verdict` nor `diagnostics`; it renders its own verdict and
   the harness compares. Rationale: keeps the independence story pristine (the
   checker's judgment owes nothing to march's answer), consistent with A2's
   accept side. The cost — reject files whose error A2 doesn't model surface as
   MISMATCH and need triage — is accepted and handled by the skip-ledger loop
   (§4), exactly as the A2 accept-side exploratory run was.

3. **Exit-code contract change: split verdict from type-divergence.** Today's
   `march-lean-check` overloads exit `1` as "MISMATCH". A2-reject must
   distinguish "A2's *verdict* is reject" from "A2 accepts but its per-node
   *types* differ from `resolved_ty`" — collapsing them would hide a real
   disagreement (a reject file where A2 thinks the program is fine would be
   mis-read as agreement). So the exit codes are redefined (§2), and the
   accept/reject comparison moves to the harness. Rationale: the two signals are
   genuinely different and only the harness has both verdicts to compare.

## 2. `march-lean-check`: independent verdict + exit codes

The checker no longer reads `verdict`. Flow:

1. parse JSON; malformed / `format_version ≠ 2` ⇒ **exit 3** (error).
2. decode `module`. `module: null` (a parse-reject) or a decode error ⇒
   **exit 2** (skip — no AST to judge).
3. whole-file skip gate: any `unsupported` construct / out-of-fragment
   annotation / non-`Num`/`Eq`/`Ord` `CInterface` scheme ⇒ **exit 2** (skip).
4. run **inference** (`Infer.inferModule'`). If it fails (unification / occurs /
   unbound-var-or-ctor that is a genuine type error, not an unmodeled-name skip)
   ⇒ A2's verdict is **reject** ⇒ **exit 1**. (An unmodeled-name/ctor failure
   still routes to **exit 2** skip, per A2's `SKIP:`-marker classification —
   unchanged.)
5. inference succeeds ⇒ run **linearity**. A linearity violation ⇒ **reject** ⇒
   **exit 1**.
6. inference + linearity both pass ⇒ A2's verdict is **accept**. Now run the
   per-node cross-check against `resolved_ty`:
   - types agree ⇒ **exit 0** (accept, types match).
   - types disagree ⇒ **exit 4** (accept, but types differ from march's
     `resolved_ty`).

Redefined exit-code contract:

| exit | meaning |
|------|---------|
| **0** | A2 accepts (inference + linearity pass) AND per-node types agree with `resolved_ty` |
| **1** | A2 rejects (inference OR linearity found it ill-typed) |
| **2** | skip (out-of-fragment / no module / unmodeled name) |
| **3** | error (malformed JSON / wrong `format_version`) |
| **4** | A2 accepts BUT per-node types disagree with `resolved_ty` |

The per-node cross-check runs **only after** inference+linearity pass (step 6),
so on a reject file inference fails first (exit 1) and the cross-check — whose
target `resolved_ty` is error-y on a rejected program — never runs. This is what
keeps "A2 rejects" (1) cleanly separate from "types differ" (4).

`stderr` still carries a human-readable reason; stdout stays empty.

## 3. Harness: compare two verdicts

The harness already obtains march's verdict (from the corpus `accept/`|`reject/`
directory and/or `march --check`). It maps `(march_verdict, lean_exit)`:

| | lean 0 (accept, match) | lean 4 (accept, types differ) | lean 1 (A2 reject) | lean 2 (skip) | lean 3 (error) |
|---|---|---|---|---|---|
| **march accept** | MATCH | MISMATCH | MISMATCH | SKIP | ERROR |
| **march reject** | MISMATCH | MISMATCH | **MATCH** | SKIP | ERROR |

- The **(reject, lean-1)** = MATCH cell is A2-reject's new contribution: both
  reject ⇒ agreement.
- **(accept, lean-1)** = MISMATCH — A2 false-rejecting a valid program — is now
  catchable (was impossible when reject files skipped and the accept side folded
  reject into "MISMATCH").
- **(reject, lean-0/4)** = MISMATCH — A2 accepting a march-rejected program (A2
  too permissive, or march over-rejected).
- MISMATCH / ERROR / CORPUS_VIOLATION stay hard failures; SKIP is normal and
  ledger-enforced (both accept-side and, now, reject-side skip sets).

## 4. Triage & expected corpus outcome

Pure-independent code means a reject file whose error A2 doesn't model
(non-exhaustive match, `let?`/Result misuse, refinement, capability) will have
A2 *accept* it ⇒ MISMATCH. These are triaged exactly like the A2 accept-side
exploratory run — for each: **model the check** if cheap and in-fragment (e.g.
match-exhaustiveness may be worth adding), else **skip-ledger** the file with a
recorded reason ("march rejects on non-exhaustive match; A2 doesn't model
exhaustiveness").

Rough expected split over the 82 reject files (refine during the run — this is
exploratory, not a fixed target):
- **~28 become genuine MATCHES**: ~15 core type-error rejects (A2's independent
  inference hits the same error) + ~13 linearity/affine rejects (A2's linearity
  pass catches them).
- **out-of-fragment rejects skip structurally** (cap, impl/typeclass,
  refinement, actor/session, module — the whole-file gate fires): ~40.
- **~10-12 need triage**: in-fragment structurally but rejected for a reason A2
  doesn't yet model (exhaustiveness, `let?`, subtler constraints) ⇒ model-or-
  skip-ledger.

The **reject-side skip-ledger** is new. Like the accept-side ledger, it is
enforced both directions (a newly-skipping reject file, or a no-longer-skipping
one, fails the run) and is a shrinking coverage tracker.

## 5. Testing & forced-relaxation

- **Unit** (hand-built modules, no `IO.FS.readFile` of samples in committed
  tests): an ill-typed module (a type error) ⇒ the checker exits 1; a
  linearity-violating module ⇒ exit 1; a well-typed module ⇒ exit 0; a
  type-annotation contradiction ⇒ exit 1.
- **Harness comparison** unit-tested via the mapping table (a reject file the
  checker rejects ⇒ MATCH; a reject file the checker accepts ⇒ MISMATCH).
- **Forced-relaxation — new reject-side dimension:** break the engine so it
  *accepts* an ill-typed program (e.g. make `unify` permissive so `Int`
  unifies with `String`), rebuild, rerun the harness, and confirm at least one
  **reject** file flips MATCH→MISMATCH (A2 wrongly accepting a march-reject).
  Then revert to green. This proves the reject-side signal is load-bearing — the
  analogue of A2's accept-side `eqvTy` break. (Keep the accept-side forced-
  relaxation too.)
- **Corpus run:** green = zero MISMATCH/ERROR over the modeled accept+reject
  subset; observed skips (both sides) == ledgers.

CI (`conformance.yml`) is unchanged in shape (still pinned to the v2-emitter
march `main`); A2-reject just rebuilds `march-lean-check` and the harness gains
the reject-side comparison + ledger.

## 6. Risks & mitigations

- **A2 incompleteness ⇒ false mismatches** (the main risk): A2 is more permissive
  than march on some reject reasons, so those reject files' MISMATCH is a *false*
  mismatch (an A2 gap, not a march bug). Mitigated by the triage → model-or-skip-
  ledger loop (§4). This is expected exploratory work, budgeted like the A2
  accept-side run — a nonzero initial reject-side mismatch count is work, not a
  blocker.
- **Exit-code contract change ripples** to the harness and any other consumer of
  `march-lean-check`'s exit codes. Contained (the harness is the only consumer),
  but must land in lockstep — the harness's exit→verdict mapping and the
  checker's new codes are one change.
- **`resolved_ty` on reject files is error-y / `TError`-laden** — never used for
  the verdict (only the accept-side per-node cross-check, which runs only after
  inference+linearity pass, i.e. never on a rejected program), so it cannot
  contaminate the reject-side judgment.
- **Distinguishing genuine type-error inference-failures from unmodeled-name
  skips** stays correct: A2's existing `SKIP:`-marker classification (an unbound
  *stdlib/cross-module* name or unknown ctor ⇒ skip; a genuine unification/
  arity/occurs failure ⇒ reject) already draws this line and is reused verbatim —
  a reject file that fails inference on an unmodeled name skips, one that fails
  on a real type error rejects.

## 7. Deliverables

One implementation plan (written next, via `writing-plans`), in the `march-lean`
repo:

**A2-reject two-sided oracle** — redefine `march-lean-check`'s exit codes (0/1/2/
3/4), remove the verdict gate so it renders an independent verdict, run the
per-node cross-check only on an A2-accept; update the harness's exit→verdict
mapping (the §3 table) and add reject-side skip-ledger enforcement; exploratory
corpus run with reject-side mismatch triage (model-or-skip-ledger); the new
reject-side forced-relaxation acceptance test. `Infer`/`Compare`/`Linearity`/
`Syntax`/`Elab` and the march emitter are unchanged except where the
verdict/exit plumbing touches `Compare.inferModule` / `MarchLeanCheck`.
