# March main resynchronization — 2026-11-06

**Follow-up:** [Task 3 and the latest main validation](../progress/2026-11-07-scoped-authority.md) supersede the scoped-needs skip and original revision below.

## Baseline and target

- march-lean was fast-forwarded from `cecd8a7` to `751e10b` (its fetched main).
- Old CI March pin: `6867c783fbde7fb8ab58bae4b4fbe36703b626a1`.
- New CI March pin: `977e04e1d3075035720cb12edb00360423eefd4e`, fetched March main at the start of this audit.
- Lean remains `leanprover/lean4:v4.29.0`; emitter format remains 3.

The target compiler was built from a clean detached clone with
`dune build --root . bin/main.exe`. The existing sibling March checkout had
unrelated edits and was not modified. Main can advance after this snapshot;
the pin intentionally identifies the revision actually tested.

## Changes

1. **Build defaults:** bare `lake build` now builds both the proof library and
   executable. CI continues to name both targets explicitly.
2. **Nested recursion:** the tail-call checker follows module-relative and
   file-qualified names, recursively checks nested modules, and honors the
   current `lemma` exemption. The formerly clean nested-module probe now
   expects a real tail-call rejection. Every IO-performing probe main declares
   its grant, so grant errors cannot masquerade as recursion evidence.
3. **Capability extraction:** `Tagged` payloads are traversed, matching current
   `Cap_surface_ty.caps_in_ty`.
4. **Capability reach:** a scope-aware free-reference walk and finite function
   closure independently check builtin `needs` and main’s union of IO grants
   for supported declarations. This includes transitive helper calls. Ordinary
   Cap-parameter functions are not grant-discharge points: March removed that
   rule after the August finding. Body annotations still require module needs,
   but do not contribute to function effect rows.
5. **Import coverage:** whole imported manifests are no longer treated as
   demanded effects. The export lacks per-function import rows; an uncovered
   whole-module upper bound therefore defers instead of manufacturing a reject.
6. **Scoped declarations:** scopes are detected before semantic checking; a
   scoped manifest makes the decoded module unsupported. It is neither
   broadened to an unscoped grant nor dropped while neighboring checks run.
   The actual exporter uses an empty string for an unscoped entry.
7. **Top-level annotations:** module-level annotated lets are encoded through
   the existing annotated local-let rule, retaining their value. The checker
   now rejects the real annotation mismatch fixture.
8. **Linear rebinding:** lexical binding obligations transfer through plain
   `let alias = resource`, including alias chains. Explicit affine qualifiers
   retain their precedence. The real rebind-and-drop fixture now rejects and
   its consumed twin still accepts.
9. **Regression gates:** `SyncTests.lean` adds build-enforced examples and
   `scripts/sync-probes.py` runs real-source cases, then flips each compiler
   verdict and removes diagnostics to ensure the independent result is stable.

## Corpus audit

The checked revision contains 601 files across types accept/reject, grammar
parse/reject, and golden. The final observed result is:

| Result | Files |
| --- | ---: |
| Matching independent verdict | 108 |
| Explicit skip | 492 |
| Known export limitation | 1 |
| New mismatch, internal error, compiler/export inconsistency, corpus violation | 0 |

A skip is not a proof. The 492 skips consist of 431 unsupported-declaration
cases, 16 parse failures with no module to inspect, 43 unmodeled
names/constructors, one closure-capture case and one explicit capability-reach
boundary case. The fragment remains substantially smaller than March.

The skip ledger changes from 272 to 492 entries: 226 additions and six removals.
Three removed paths were replaced upstream (`accept/t77`, `reject/t164`,
`reject/t165`); three (`reject/t143`, `t147`, `t158`) now independently reject
because main lacks a needed IO grant. The added entries include new language features. Three existing previously
judged files now skip: `accept/t50_extern_cap_and_foreign_covered` because extern
reach cannot certify main’s grant; `reject/t39_transitive_use_missing_cap` because
whole-module manifests no longer justify demand-driven import rejection (and
`Vault.new` is unmodeled); and `grammar/parse/p22_capability_directives`, which now
references the unmodeled `int_wrapping_add`. Each ledger entry records the
actual skip reason; none reclassifies an unexplained mismatch.

`reject/t23_derive_unknown_interface` and
`reject/t144_cap_derive_json_variant_arg` were removed from the limitation
allowlist: the residual programs independently fail their main grant checks.
Their erased derive errors remain invisible. The remaining limitation is
`reject/t49_derive_unknown_type`, whose rejection is still erased before export.

## Verification procedure

- `lake build`: both targets, including all proof modules and native regression guards.
- Existing forbidden-proof-placeholder source check and `git diff --check`.
- Full conformance harness against the pinned compiler and all five directories.
- All 22 tail-call probes against the actual pinned compiler.
- All 13 main-sync probes against the actual pinned compiler, including verdict/diagnostic mutations.

For local iteration, the compiler’s stdout, stderr and exit status for both
`--check` and `--emit-core-ast` were captured from all 601 files in the immutable
clean snapshot. The final shell harness replays those exact compiler results
and runs the final Lean executable afresh. This avoids recompiling the same
unchanged March programs on each checker edit. CI runs the ordinary uncached
commands in the workflow; the temporary replay helper is not shipped.

Code review independently reproduced two false rejects in the first version
(body annotations treated as effects, and explicit affine weakening lost), both
fixed with real-source regressions before the final run.

## Remaining boundaries

- Full capability row inference, higher-order instantiation, extern effects,
  imported summaries and global initializer reach are not implemented. When
  the new pass cannot justify its answer it defers to skip; other independent
  passes may still establish a rejection.
- A user-defined entry-level `println`/`print` overlaps injected prelude
  function rows omitted from the export. A concrete `println(x : Int) = x`
  program is rejected by current March for console authority despite the
  modeled local call being pure. Such overlaps skip, pinned by the console
  shadow probe. Ordinary builtin shadowing (the `file_read` probe) remains
  supported. This boundary needs resolved symbol/export information, not a
  guessed builtin edge.
- Scoped manifests skip; the checker does not prove filesystem confinement.
- The concrete normalizer still uses the older duplicate-preserving abstract
  filter. It is not on the verdict path. The future scope/normalization task
  must implement March’s deduplicate-first operation and reprove the bridges.
- The linearity pass is not a general ownership soundness proof; branch
  accounting, captures and always-linear aggregate types need the dedicated
  theory and implementation work in the future plan.
- Format version 3 does not promise export completeness. Function effect
  bounds, proof dictionaries and other source obligations can be absent from
  the JSON. A source-level theorem requires an explicit valid-export contract.

See [the future theory plan](2026-11-06-future-theory.md) for the proposed
proof-driven implementation sequence. Historical findings remain in
`specs/march-findings.md`; their August status should be read with this audit.
