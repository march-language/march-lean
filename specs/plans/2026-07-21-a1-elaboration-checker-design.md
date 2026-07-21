# Stage A1 — elaboration checker (design)

> Parent design doc: `specs/plans/2026-07-18-lean-conformance-bridge-stage-a.md`.
> Predecessor: `specs/plans/2026-07-20-a0-plumbing.md` (A0 — verdict
> pass-through, shipped & merged as march-lean PR #2; march-side
> `--emit-core-ast` shipped as march PR #55, on march `main` at/after
> `04d3960d`).
>
> This is a **design doc**, not an implementation plan. It fixes the shape of
> A1 and the decisions behind it. Two implementation plans follow from it
> (via `writing-plans`), one per repo:
> - **march side** — extend `--emit-core-ast` to `format_version` 2: inline
>   type annotations on the AST + two HM witness tables. (march repo,
>   `specs/plans/`.)
> - **march-lean side** — the elaboration checker that consumes it. (this
>   repo, `specs/plans/`.)

## 0. What A1 is (and is not)

A0 proved the pipe: march emits a JSON verdict + AST, Lean echoes the verdict,
a harness diffs the two over the `specs/lang/types/{accept,reject}` corpus.
The Lean side did **not** look at the AST — it could not disagree with march,
so it caught nothing but plumbing breakage.

**A1 makes the Lean side an independent checker for a scoped fragment of the
language.** For an *accept* program in that fragment, Lean re-derives that the
program is well-typed — checking march's elaborated types and HM
generalization/instantiation witnesses, and independently re-deriving
linearity use-counts — and either agrees (accept) or disagrees (a MISMATCH,
which is a real finding: a march bug or a Lean-model gap). Anything outside
the fragment is an **honest skip**, loudly counted, never laundered into
agreement.

**A1 is not A2.** A1 does **not** run Hindley–Milner inference or unification,
and does **not** check the *reject* side (it does not confirm march was right
to reject). A1 is a forward, syntax-directed, annotation- and
witness-*checking* pass. Re-deriving types from scratch (unification,
reject-side reasoning) is A2. Concretely, A1 avoids all "backward
reconstruction": every place where march's typechecker solved something by
unification, march hands Lean the answer as an annotation or witness, and Lean
verifies it by substitution + equality only.

### The fragment (A1 scope)

In scope — the "simple core" plus linearity:

- **Core** (~corpus `t01`–`t22`): literals; lambda / application;
  let-polymorphism (incl. `letfn` recursion & generalization); `if` / `cond`;
  ADTs + `match` (incl. guards, non-exhaustiveness as a *reject* reason we
  skip); tuples; records + update; atoms; type annotations; `Num`/`Eq`/`Ord`
  constraint discharge on primitives.
- **Linearity / affinity** (~corpus `t64`–`t68`, `t80`–`t82`): `linear`/`affine`
  binders & params, single-use / at-most-once / must-consume enforcement,
  linear field arithmetic, linear-consuming `send`, `always_linear` types.
  This is the milestone's headline: linearity is the one area where march
  hands Lean **no** certificate (see §3), so Lean genuinely re-derives it.

Out of scope for A1 — deferred to a skip-ledger, checked in later milestones:
interfaces / typeclasses (`t23`–`t30`), modules / visibility (`t31`–`t38`),
actors / protocols / session types (`t39`–`t44`, `t79`, `t87`),
capabilities (`t45`–`t63`), `let?`/`Result` (`t70`–`t73`), refinement types
(`t75`–`t78`).

## 1. Design decisions (with rationale)

These were settled during brainstorming; recording them so the plans don't
relitigate them.

1. **Seam = annotated AST, not a separate type side-channel.** march joins its
   `type_map` onto the emitted `module` AST nodes inline (a `"ty"` field per
   node), rather than shipping a parallel span→type table the Lean side must
   re-join. Rationale: the span-keyed join is march's to do (it has the
   authoritative `type_map` and the exact `desugared` value it was built
   from); making Lean re-join by span would duplicate that logic and inherit
   its lossiness (dummy/duplicate spans — see §5 caveat). One tree, one
   contract.

2. **Keep full per-node annotations AND add poly witnesses** (the witness-scope
   decision). march dumps the full per-node type table *and* adds
   generalization/instantiation witnesses. It does **not** emit
   capability/refinement/RC witnesses. Rationale: full annotations are already
   computed (free to serialize) and keep the Lean checker simple and
   divergence-free (Lean verifies march's answer rather than replicating
   march's forward synthesis, so numeric-defaulting / overload corners can't
   produce spurious diffs). The poly witnesses are the *only* net-new
   emission, and they are exactly the things annotations alone cannot express
   (which vars are ∀-quantified; what a use site instantiated them to). This
   is the "limit witness emission to what's necessary to avoid reconstructing
   types backwards" principle, under the full-annotation baseline.

3. **Reject side = honest skip.** A1 does not model *why* march rejects. Every
   reject-corpus file is a skip (exit 2), counted in the ledger, never counted
   as agreement. Rationale: confirming a rejection requires reject-side
   reasoning (that's A2); pretending otherwise would let a broken Lean checker
   "agree" with every rejection for free.

4. **Retire the POC proofs.** The existing `MarchLean` Perceus/FBIP
   metatheory modules (`LinearContext`, `Heap`, `Defun`, the 28 idealized
   theorems) were proof-of-concept; they are not reused by the checker and are
   removed, not carried forward. Rationale: the checker is executable Lean
   over the real march AST, not the idealized calculus those proofs model;
   keeping them would imply a connection that doesn't exist.

5. **Named variables + executable usage-state linearity.** The Lean syntax uses
   named variables (not de Bruijn) to match march's named AST 1:1 and keep
   MISMATCH diagnostics legible. Linearity is checked by an executable
   use-counting pass (exactly-once / at-most-once / must-consume state per
   binder), not a proof-carrying representation. Rationale: this is a
   differential *tester*, not a certified compiler; legibility and directness
   beat proof elegance here.

## 2. The seam: `format_version` 2

A0's envelope (`format_version` 1):

```json
{"format_version":1,"verdict":"accept"|"reject","diagnostics":[...],"module":{...}}
```

A1 bumps to `format_version` 2 and adds three things. **The envelope keys are
unchanged; `module`'s node objects gain a `"ty"` field, and two new top-level
witness tables appear.**

```json
{
  "format_version": 2,
  "verdict": "accept"|"reject",
  "diagnostics": [...],
  "module": { ...nodes now carry "ty"... },
  "schemes": [ {"binder_span": <span>, "ids": [<int>...], "body": <ty-json>} ... ],
  "instantiations": [ {"use_span": <span>, "ids": [<int>...], "args": [<ty-json>...]} ... ]
}
```

- **`"ty"` on `module` nodes.** Each expression node (and binder/param/pattern
  node that carries a type) gains `"ty": <ty-json>` — the resolved type from
  `type_map`, or `null` where none was recorded. Uses a **new
  `ty → JSON` encoder** (there is no existing internal-`ty` → surface-`Ast.ty`
  reifier to reuse; `pp_ty` is lossy display, `surface_ty` goes the wrong
  direction). The encoder must **deep-`repr`** recursively — top-level `repr`
  only compresses one chain, nested `TCon`/`TArrow`/etc. args each need their
  own resolution — and must pick an explicit encoding for **surviving
  metavariables** (unbound `TVar`, e.g. polymorphic code whose binding scheme
  is the real answer). It must handle the full internal `ty`: `TCon`, `TArrow`,
  `TTuple`, `TVar`, `TLin`, `TNat`/`TNatOp`, `TChan(session_ty)`, `TRefine`,
  `TError` sentinel. Out-of-fragment type constructors (sessions, refinements)
  may serialize to an `{"kind":"unsupported", ...}` marker rather than a full
  encoding — the Lean side treats any `unsupported` type as a skip trigger
  (§4), so a faithful-but-opaque marker is enough.

- **`"schemes"` table** — one entry per generalization site. `binder_span`
  keys it to the binder in `module`; `ids` is the ∀-quantified variable list
  (march's `Poly (int list * constraint_ list * ty)` — the id list is
  **already materialized** as `Poly`'s first field, no traversal); `body` is
  the scheme body type. Feasibility confirmed: recorded via a `type_map`-style
  `Hashtbl` at the generalize chokepoint, ~3–6 call sites (let-`PatVar`,
  `letfn`, top-level `DFn`, plus interface/impl/module sites for completeness —
  though those are out-of-fragment). Non-`PatVar` lets stay `Mono` and never
  enter the table (no scheme), which is correct.

- **`"instantiations"` table** — one entry per polymorphic use site. `use_span`
  keys it to the `EVar`/`EField` node; `ids` is the scheme's id list (the
  **join key** back to `"schemes"` — id-list equality); `args` is the
  type-argument vector, positionally aligned to `ids`. Feasibility confirmed:
  `instantiate` builds `subst = List.map (fun id -> (id, fresh_var level)) ids`;
  the fresh vars are ordinary unification vars that resolve through `repr`
  after solving (same round-trip as `type_map`). Emit by threading a
  `?use_span` param into `instantiate` and recording `(ids, map snd subst)` at
  the ~5 `EVar`/`EField` call sites, resolving args via `repr` at module end.

**Explicitly NOT emitted** (honoring decision #2): constructor instantiations
(`ECon` uses a separate `instantiate_ctor` path; A1 doesn't need a witness —
the node's result-type annotation plus the datatype's `DType` decl in `module`
pin the instantiation, so Lean checks it forward), capability subsumption,
refinement obligations, reuse/RC decisions.

**march-side cost** (from feasibility investigation): 2 new `Hashtbl` fields on
`env`, ~8–10 `Hashtbl.replace` calls at existing chokepoints, one optional
param on `instantiate`, one new `ty → JSON` encoder, and the inline-join at the
emit branch (`bin/main.ml`, where `type_map` is already in scope but currently
unused). **No inference restructuring.**

## 3. What march does NOT hand Lean (Lean re-derives)

Three things are computed transiently inside march and never surface as
checkable artifacts — Lean must model them independently (or skip):

- **Linearity use-counts** — `env.lin` with `le_used : bool ref` is mutated
  during checking and discarded; only pass/fail diagnostics survive. **This is
  A1's headline work:** Lean re-derives use-counts from the AST + the linearity
  *qualifiers* (which ARE serialized: `param_lin`/`bind_lin`/`fld_lin`,
  `TyLinear`, `TLin`). Lean gets the *declarations* but not march's *verdict*
  on where each linear/affine binder was consumed — so it genuinely
  re-computes, making linearity the strongest independent signal in A1.
- **Capability subsumption** — enforced by bespoke passes, not HM; out of
  fragment → skip.
- **Refinement obligations** — discharged by a separate Z3-backed
  `lib/refinecheck` walk; `repr` strips `TRefine` to base so they're invisible
  in the type annotations anyway; out of fragment → skip.

## 4. march-lean checker structure

Remove the POC proof modules (decision #4). New structure:

- **`Syntax/Ty.lean`, `Syntax/Term.lean`, `Syntax/Pattern.lean`** — executable
  inductive types mirroring march's AST for the fragment, **named variables**.
  Each includes an `unsupported`/`other` escape constructor so decoding an
  out-of-fragment node is representable (and triggers a skip) rather than a
  decode error.
- **`Elab/Json.lean`** — decoder from the `format_version` 2 envelope into the
  `Syntax` types + the two witness tables. Rejects `format_version` ≠ 2 as an
  error (exit 3), consistent with A0's format-version discipline. (A0's
  `MarchLean/Json.lean` verdict parser is updated to accept version 2.)
- **`Typing/Check.lean`** — bidirectional, syntax-directed check over the
  annotated AST. Verifies: each node's `"ty"` is consistent with its
  subterms' annotations and the datatype/decl environment; each `EVar`/`EField`
  use with an `instantiations` entry is a valid instantiation of its
  `schemes` entry **by substitution + equality only** (substitute `args` for
  `ids` in `body`, check it equals the use-site annotation — no unification, no
  matching). Any `unsupported` node/type ⇒ skip.
- **`Typing/Linearity.lean`** — independent executable use-counting:
  exactly-once (linear), at-most-once (affine), must-consume-before-scope-close,
  field-level tracking. Re-derived purely from qualifiers + term structure.
- **`MarchLeanCheck` main** — control flow:
  1. parse envelope; malformed ⇒ exit 3.
  2. `verdict == "reject"` ⇒ exit 2 (skip; A1 doesn't model reject).
  3. `verdict == "accept"` ⇒ decode `module` + witnesses.
  4. any `unsupported` construct encountered (decode or check) ⇒ exit 2 (skip).
  5. run `Typing/Check` + `Typing/Linearity`; all pass ⇒ exit 0; a modeled
     check fails ⇒ exit 1 (this is the MISMATCH the harness catches).

Exit-code contract is unchanged from A0 (0 accept / 1 reject / 2 skip /
3 error) — A1 simply makes 1 and 2 reachable for the first time.

## 5. Harness & CI changes

A0's harness failed the run on *any* non-MATCH, including SKIP (correct then:
skip was structurally impossible). A1 makes skip **expected and frequent**
(every reject file + every out-of-fragment accept). Changes:

- **Skip is normal.** Stop failing on SKIP. Instead maintain an **enumerated,
  shrinking skip-ledger**: the run records which corpus files skipped and why
  (reject-side / which unmodeled construct). CI asserts the ledger matches a
  checked-in expected set (so a *newly* skipping file — a regression in
  coverage — is caught), and the ledger is expected to shrink as later
  milestones land.
- **Failure conditions:** MISMATCH (a *modeled* accept — in-fragment, not
  skipped — where Lean exits 1) or ERROR (exit 3). Keep A0's `CORPUS_VIOLATION`
  check (file's own march verdict vs. its `accept/`/`reject/` directory).
- **Definition of green:** zero MISMATCH/ERROR over the modeled-accept subset,
  plus the skip-ledger matching expected. A **forced Lean-rule relaxation**
  (deliberately break a `Typing/Check` or `Typing/Linearity` rule) must turn at
  least one modeled accept red — the A1 analogue of A0's forced-mismatch
  acceptance test, proving the checker can actually fail.
- **Repin** the workflow's march checkout to a `main` SHA that includes the
  `format_version` 2 emitter (superseding the current `ef18e6d8` pin).

## 6. Risks & how this design retires them

- **Polymorphism / backward reconstruction** *(retired)* — the scheme +
  instantiation witnesses make let-polymorphism a decidable substitution-check;
  Lean never reconstructs quantifiers or runs unification. Feasibility of
  emitting both witnesses is confirmed cheap (§2).
- **Span-join lossiness** *(contained)* — march does the join inline (decision
  #1), so Lean never joins by span. Where march's own join is lossy
  (dummy/duplicate spans from desugaring), the affected node carries
  `"ty": null` and Lean treats a needed-but-absent annotation as a skip, not a
  false accept.
- **Metavariables survive in annotations** *(handled)* — the `ty → JSON`
  encoder deep-`repr`s and emits an explicit encoding for unbound `TVar`; the
  binding's scheme witness is the authoritative answer for polymorphic nodes.
- **Linearity has no certificate** *(by design)* — Lean re-derives it; that's
  the point of the milestone, not a gap.
- **Spurious mismatches from Lean-model gaps** *(acknowledged)* — a MISMATCH is
  "march bug OR Lean-model gap," not automatically a march bug. The
  keep-full-annotations choice (decision #2) minimizes this by having Lean
  verify march's types rather than re-synthesize them; remaining mismatches are
  triaged, and a genuine model gap either gets fixed in the Lean rules or the
  construct moves to the skip-ledger with a recorded reason.

## 7. Deliverables

Two implementation plans (written next, via `writing-plans`):

1. **march `format_version` 2 emitter** — `ty → JSON` encoder; inline `"ty"`
   annotations; `schemes` + `instantiations` tables; golden-test update.
2. **march-lean A1 checker** — remove POC proofs; `Syntax`/`Elab`/`Typing`
   modules; `MarchLeanCheck` control flow; `Json.lean` version bump; harness
   skip-ledger + forced-relaxation test; CI repin.

Each plan carries its own task breakdown, per-task briefs, and review gates,
following the A0 plans' structure.
