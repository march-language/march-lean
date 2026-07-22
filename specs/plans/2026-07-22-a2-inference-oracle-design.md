# Stage A2 — independent inference oracle (design)

> Parent design doc: `specs/plans/2026-07-18-lean-conformance-bridge-stage-a.md`.
> Predecessors: A0 (`specs/plans/2026-07-20-a0-plumbing.md`, verdict
> pass-through — merged), A1 (`specs/plans/2026-07-21-a1-elaboration-checker-design.md`,
> elaboration checker — merged as march-lean #3, follow-up #4).
>
> This is a **design doc**, not an implementation plan. It fixes the shape of
> Stage A2. One implementation plan follows (via `writing-plans`), in the
> `march-lean` repo. **The march emitter is unchanged** — A2 consumes the
> existing `format_version` 2 output.

## 0. What A2 is (and is not)

A1 made the Lean side *verify march's own elaboration*: it read march's
per-node `resolved_ty` and HM witness tables (`schemes`/`instantiations`) and
confirmed, by substitution + equality, that they were internally consistent.
Its signal is real but bounded — it checks that march's answer is *coherent*,
not that it is *correct*, because it takes march's types as given.

**A2 replaces that with an independent Hindley–Milner inference engine.** For an
accept-side, in-fragment program, Lean re-derives the types itself from the
bare AST — running its own unification, generalization, instantiation, and
constraint solving — treating march's `resolved_ty` and witness tables **not
as inputs but only as a cross-check target**. Two comparisons per file:

1. **Verdict:** Lean's independent inference must *succeed* on a march-accepted
   in-fragment program. If Lean cannot type it (unification failure, unbound
   variable, occurs-check) ⇒ **MISMATCH** — either a march bug (it accepted
   something ill-typed) or a gap in Lean's engine.
2. **Per-node types:** Lean's inferred type at each node must agree with
   march's `resolved_ty` **up-to-equivalence** (metavariable renaming,
   defaulting, named-record canonicalization). A genuine structural
   disagreement ⇒ **MISMATCH** — Lean and march both accept but assign
   different types to the same node.

This is a strictly stronger check than A1: Lean no longer trusts march's types;
it derives its own and holds march to them.

**A2 is (still) not the full oracle.** Per the milestone decision, A2 is
**accept-side only** — it does not model the *reject* side (it does not
independently decide that march was *right* to reject; every reject-verdict
file still skips at the verdict gate). Modeling the reject side —
independently rendering a reject verdict and comparing on the reject corpus —
is a later stage. A2's ambition is the hard, valuable core: a genuine
inference engine in Lean, with the accept-side cross-check it enables.

### The fragment (unchanged from A1)

In scope: **Core** (literals; n-ary lambda / application; let-polymorphism incl.
`letfn`; `if`/`cond`; ADTs + `match`; tuples; records + update; atoms;
`Num`/`Eq`/`Ord` over primitives) **plus linearity** (`linear`/`affine`
binders, single-use / at-most-once). Everything else — interfaces/typeclasses,
modules, actors/sessions, capabilities, `let?`/Result, refinement types —
remains an honest, counted **skip**. A2 does **not** broaden the fragment; it
deepens the check within it. (Growing the fragment is an orthogonal, later
effort.)

## 1. Design decisions (with rationale)

1. **Independent inference, accept side only** (the milestone decision). A2
   builds a real HM engine and re-derives accept-side types; it does not model
   the reject side. Rationale: the inference engine is the hard, high-value
   core; the reject-side modeling (independently deciding *reject*, matching on
   the reject corpus) is separable and can follow once the engine exists.

2. **Verdict + per-node cross-check** (the comparison decision). A2 compares
   both (a) inference-success vs march's accept verdict and (b) inferred type
   vs `resolved_ty` per node, up-to-equivalence. Rationale: the per-node check
   catches "both accept but disagree on a node's type" — a divergence class the
   verdict alone misses — which is exactly the subtle-bug surface an
   independent oracle exists to find. The cost (an up-to-equivalence comparison
   that tolerates benign representational differences) is accepted; see the
   spurious-diff risk (§6) and its mitigation (§4).

3. **`ST`-monad, mutable-ref, union-find engine** (Approach A — the engine
   implementation). Inference metavariables are `ST.Ref` cells solved
   destructively by union-find with path compression, mirroring how march's own
   OCaml typechecker works (`TVar of tvar ref`, `Link`/`Unbound`). Rationale:
   this is the standard, efficient HM implementation and the closest structural
   analogue to march's engine, which minimizes behavioral divergence (the thing
   that would produce spurious mismatches). The alternative — a pure,
   substitution-threading engine — is more "Lean-idiomatic" but further from
   march's behavior and more code; not worth it for a differential tester.

4. **Emitter unchanged; witnesses ignored; `resolved_ty` is the compare
   target.** A2 consumes the existing `format_version` 2 output. It reads the
   `module` AST structure and each node's `resolved_ty` (as comparison target
   only) and **ignores** the `schemes`/`instantiations` tables entirely (it
   does its own generalization/instantiation). Rationale: no producer change is
   needed, and using the witnesses as inputs would defeat the independence.

5. **Mirror march's defaulting inside the engine.** march defaults unresolved
   primitive constraints at generalization boundaries (e.g. an unconstrained
   `Num` metavar → `Int`). A2's engine applies the *same* defaulting policy
   during inference, so residual inferred types line up with march's rather
   than being reconciled only at comparison time. Rationale: doing it in the
   engine keeps the up-to-equivalence comparison simpler and reduces the
   spurious-diff surface at its source. (Comparison still tolerates metavar
   renaming and record canonicalization; defaulting is handled upstream.)

6. **Retire A1's `Check.lean`; salvage its reusable parts.** A1's
   annotation/witness *verification* is superseded by real inference and is
   removed. The reusable pieces — the `CheckResult` type, `canon` (named-record
   canonicalization), and the `CInterface "Num"/"Eq"/"Ord"` constraint-name
   handling — are salvaged into the new `Infer`/compare code. Rationale: keeping
   a superseded checker alongside the engine is two things to maintain and a
   larger spurious-diff surface (decision considered and rejected in
   brainstorming). `Linearity.lean` is **not** retired — it is already
   independent and stays as-is.

## 2. Architecture

**Reused unchanged:** `MarchLean/Syntax.lean` (AST + `unsupported`/`hasUnsupported`
gates), `MarchLean/Elab.lean` (v2 decoder — still decodes `resolved_ty` for the
cross-check, and still decodes the witness tables even though A2 ignores them),
`MarchLean/Linearity.lean` (independent use-counting), `MarchLean/Json.lean`,
`scripts/conformance-harness.sh` + `scripts/expected-skips.txt`,
`.github/workflows/conformance.yml`.

**New — `MarchLean/Infer.lean`, the HM engine (in `ST`):**
- **`MTy`** — inference types. Metavariables are `ST.Ref (MVar)` cells where
  `MVar := unbound (id : Nat) (level : Nat) (constraints : List Class) | link (t : MTy)`.
  Other constructors mirror `Syntax.Ty`: `con`, `arrow`, `tuple`, `record`,
  `lin`, `nat`, `natOp`. (`Class := num | eq | ord` for the modeled primitive
  classes.)
- **`repr`/zonk** — follow links + path-compress; deep-`zonk` resolves an `MTy`
  to its solved form for comparison.
- **`unify : MTy → MTy → EST …`** — union-find, occurs-check (with level
  lowering, as march does), structural for `con`/`arrow`/`tuple`/`record`; a
  failure is an `Except`-style error that becomes a MISMATCH upstream.
- **`generalize`/`instantiate`** — level-based (`enter`/`leave` level), yielding
  a scheme `∀ ids. constraints ⇒ MTy`; `instantiate` freshens.
- **constraint handling** — accumulate `Num`/`Eq`/`Ord` obligations; discharge
  against primitives; **default** unresolved ones per march's policy (§1.5) at
  generalization.
- **`infer : Ctx → Term → EST … MTy`** — syntax-directed over the fragment: lit,
  n-ary `app` (unify fn against an arrow chain built from the args), n-ary
  `lam` (fresh metavars for params), `let`/`letfn` (generalize the rhs), `if`
  (branches unify), `con`/`match` (from the datatype env), `tuple`, `record`,
  `field`, `atom`, `var` (instantiate its scheme). An out-of-fragment node is
  unreachable here — the whole-file skip gate (`hasUnsupported`) fires first.
- **datatype environment** — constructor signatures + record shapes built from
  the module's `DType` decls (as A1 did).

**New — the up-to-equivalence comparison** (`MarchLean/Compare.lean`, or a
section of `Infer`):
- After inference solves the module, walk each expression node in parallel with
  its decoded `resolved_ty`; zonk Lean's inferred `MTy` and structurally
  compare against march's `Ty`, modulo:
  - **(i)** a consistent **metavar ↔ `TVar`-id renaming bijection** threaded
    through the walk — a residual Lean metavar maps to at most one march `TVar`
    id and vice versa; a violation is a mismatch.
  - **(ii)** **defaulting already applied** in the engine (§1.5), so residuals
    align.
  - **(iii)** **named-record canonicalization** (reuse A1's `canon` + `DType`
    env; sorted fields).
- A genuine structural disagreement (different head constructor, arity, field
  set) ⇒ mismatch.

**Retired:** `MarchLean/Check.lean` (annotation/witness verification). Its
`CheckResult`, `canon`, and constraint-name logic move into `Infer`/`Compare`.

## 3. Checking flow (the new core)

`inferModule : Syntax.Module → CheckResult` (`| ok | reject msg | skip reason`),
replacing A1's `checkModule` in the `MarchLeanCheck` pipeline:

1. **Whole-file skip gate:** any `unsupported` node/type (or a
   non-`Num`/`Eq`/`Ord` `CInterface` in a scheme, as A1) ⇒ `skip`. (Reuse
   `Decl.hasUnsupported`.)
2. **Run inference** over the module in `ST`. If inference **fails**
   (unification error / unbound var / occurs-check) on this march-accepted
   file ⇒ `reject` ("MISMATCH (infer): …") — exit 1.
3. **Cross-check** each node's zonked inferred type against its decoded
   `resolved_ty` up-to-equivalence (§2). A structural disagreement ⇒ `reject`
   ("MISMATCH (type): …at span…") — exit 1.
4. **Linearity** (`Linearity.checkLinearity`, unchanged) ⇒ `reject` on
   violation.
5. All pass ⇒ `ok` — exit 0.

`MarchLeanCheck` main is otherwise unchanged: parse → verdict gate (reject ⇒
exit 2; malformed / `format_version ≠ 2` ⇒ exit 3) → decode (error ⇒ exit 3) →
`inferModule` → linearity. Exit contract unchanged: **0** accept/agree, **1**
MISMATCH, **2** skip, **3** error.

## 4. The up-to-equivalence comparison (the subtle part)

This is where A2's spurious-diff risk concentrates; the design pushes as much
reconciliation as possible *upstream* (into the engine) so the comparison is a
thin structural walk:

- **Metavar renaming.** HM leaves genuinely-polymorphic nodes with residual
  type variables; Lean's ids and march's `TVar` ids are unrelated integers.
  The comparison threads a bijection (`Lean-mvar-id ↔ march-TVar-id`), binding
  on first encounter and requiring consistency thereafter. So `∀a. a→a` vs
  `∀t. t→t` compares equal; `a→b` vs `t→t` does not (b↔t conflicts with a↔t).
- **Defaulting.** Handled in the engine (§1.5) — by comparison time, an
  unconstrained-`Num` residual is already `Int` on both sides, so no
  reconciliation is needed here. (If a residual class other than the modeled
  `Num`/`Eq`/`Ord` survives, that node is out of fragment and the file skipped
  earlier.)
- **Named records.** Expand named record `TCon("Foo",[])` to structural form via
  the `DType` env before comparing (reuse A1's `canon`); compare fields in
  march's sorted order.
- **Structural disagreement** (head constructor / arity / field set / `lin`
  qualifier) ⇒ mismatch. A `resolved_ty` of `null` on an in-fragment node that
  Lean *did* infer a type for is treated as "no cross-check available" for that
  node (Lean's inference stands on its own) rather than a mismatch — the
  verdict-level check (step 2) already covers well-typedness.

## 5. Harness, success criteria, and the honest caveat

Same skip-ledger discipline as A1 (`expected-skips.txt` enforced both
directions; MISMATCH/ERROR/CORPUS_VIOLATION hard-fail; SKIP normal). Two honest
differences from A1:

- **The first corpus run is genuinely exploratory.** For A1 I could pre-predict
  0 mismatch (it verified march's own answer). A2 derives its own answer, so
  the first run *may* surface divergences: representational spurious diffs (→
  refine the equivalence/defaulting, an engine/compare fix) or genuine march
  quirks (→ a finding; or move that file to the skip-ledger with a recorded
  reason). Surfacing these is the point of A2 — the plan must budget triage
  time for run 1 and treat a nonzero initial mismatch count as expected work,
  not a blocker.
- **The skip-ledger may shift.** Independent inference may newly *skip* files
  A1 checked (if the engine doesn't yet model a construct A1's shallow check
  tolerated) or newly *check* files A1 skipped. The ledger is regenerated for
  A2 and re-pinned; the accept-side checked count is a coverage metric to grow,
  not a fixed target.

**Green** = every in-fragment accept file: Lean infers successfully, per-node
types agree up-to-equivalence, linearity passes; 0 MISMATCH/ERROR; observed
skips == ledger. **Forced-relaxation acceptance test:** deliberately break the
engine or comparison (e.g. make `unify` wrongly succeed on `Int` vs `Bool`, or
the comparison wrongly strict on metavar renaming) and confirm ≥1 accept flips
to MISMATCH; revert → green. This proves the oracle can genuinely fail — more
load-bearing for A2 than A1, since A2's value *is* its ability to disagree.

CI (`conformance.yml`) is unchanged in shape (already pinned to march main
`733e7a0b`); A2 just rebuilds `march-lean-check`.

## 6. Risks & mitigations

- **Spurious mismatches from representational differences** *(the main A2
  risk)* — numeric defaulting, metavar naming, alias/record expansion. Mitigated
  by mirroring march's defaulting in the engine (§1.5), the metavar-renaming
  bijection and named-record canonicalization in the comparison (§4), and
  budgeting run-1 triage (§5). Residual cases are triaged: a benign difference
  hardens the equivalence; a real one is a finding.
- **Engine gaps** — Lean fails to infer a construct march accepts, surfacing as
  MISMATCH. Triage: extend the engine, or (if genuinely out of the modeled
  fragment) move the file to the skip-ledger with a recorded reason. Never
  paper over with a false accept.
- **Divergence from march's inference in the corners** — let-generalization
  timing, the value restriction (march has none — purely level-gated),
  constraint defaulting order, record-field inference. Mitigated by modeling the
  engine on march's actual algorithm (levels, no value restriction, same
  defaulting), verified against march's `typecheck.ml` during implementation.
- **`ST` plumbing complexity** — the engine threads `ST` + an error channel
  (`ExceptT String (ST …)` or equivalent). Contained by keeping `unify`/`infer`
  small and well-typed and unit-testing them before the corpus run.
- **Occurs-check / non-termination** — a cyclic unification must be caught
  (occurs-check) rather than loop; `zonk`/`repr` must handle already-solved
  cycles. Unit-tested explicitly.

## 7. Deliverables

One implementation plan (written next, via `writing-plans`), in the `march-lean`
repo:

**A2 inference oracle** — `MarchLean/Infer.lean` (`MTy` + union-find `unify` +
`generalize`/`instantiate` + constraint solving/defaulting + `infer` over the
fragment + datatype env); the up-to-equivalence `Compare`; retire
`Check.lean` (salvage `CheckResult`/`canon`/constraint-name); rewire
`MarchLeanCheck` to `inferModule`; regenerate the skip-ledger; forced-relaxation
acceptance test; corpus-run triage. `Elab`/`Linearity`/`Syntax`/harness reused.
The march emitter is untouched.
