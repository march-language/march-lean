# march main capability resync (2026-08-08)

> Not a design doc and not a plan — a record of a slice that was discovered
> rather than planned. It began as "repin CI to march main" and turned into
> five verdict-changing fixes because the old pin was 71 commits stale and the
> local `march` used for ad-hoc checks was staler still (opam 0.2.0).
>
> Pin moved `7c1d701c` -> `6867c783`. Corpus 242 -> 277.

## 0. Why this exists

The A-series has bumped the march pin twice before and both times the drift
was inert: the emitter envelope was unchanged and no new ERROR-level check
landed inside the modeled fragment. That history made "bump the pin" feel
like bookkeeping. This bump was not inert. It surfaced **five** corpus-visible
divergences — four of them false ACCEPTS — plus four more that the corpus
cannot see at all.

The lesson worth keeping: the previous two bumps' inertness was a property of
those diffs, not of pin bumps. march's capability subsystem grew four new
modules (`cap_ceiling`, `cap_scope`, `cap_surface_ty`, `cap_symbols`) and
+1900 lines of `typecheck.ml` in this window.

Equally important: the local `march` on PATH was 0.2.0, which reported two
MISMATCHes and four CORPUS_VIOLATIONs — all artifacts. A stale binary does not
merely miss findings, it manufactures them.

## 1. Fixed (corpus-visible)

| file | direction | cause | fix |
|---|---|---|---|
| `reject/t149_cap_variant_arg_undeclared` | false accept | `capsInSignature` scanned only `DFn` params | scan `dtype` ctor `argTys` |
| `reject/t151_cap_body_annotation_undeclared` | false accept | Check 1 read signatures only | `capAnnotsInTerm`, mirroring `cap_annots_in_expr` |
| `reject/t152_root_cap_is_ambient_authority` | false accept | modeled the pre-R2 ambient `root_cap` | R2 gate, gated on full-fragment |
| `accept/t148_cap_narrow_chains` | false **reject** | modeled the pre-R4a `cap_narrow : Cap(IO) -> Cap(a)` | retype + `capNarrowViolation` sweep |
| `reject/t144_cap_derive_json_variant_arg` | false accept | rejection erased by the desugarer | known-limitations entry |

**The R4a fix is the one to re-read before touching any of this.** Retyping
`cap_narrow` alone would have traded one false reject for three false
accepts: `reject/t153`/`t154`/`t155` were rejecting only as a side effect of
the old argument type failing to unify, and nothing anywhere consulted the
lattice. march moved that guarantee into a deferred sweep; this checker had
to move it too, in the same commit. A fix that "makes the failing file pass"
would have silently opened three holes.

It also exposed a second-order gap: `Infer` was ignoring `dfn` return
annotations. That was invisible while every builtin's result was pinned by
its argument types, and R4a's polymorphic `cap_narrow` removed that pinning.

## 2. Known gaps (corpus-invisible)

Recorded in full in `specs/march-findings.md`. Summarized here because the
conformance gate is structurally incapable of reporting them, so a green run
must not be read as evidence about any of them:

1. **Path-scoped capabilities** — `needs IO.FileRead("/etc")`. The emitter
   carries scopes in a new `scopes` array; `Elab`'s `DNeeds` reads only
   `paths`. A scope never subsumes unscoped, so a narrow declaration decodes
   here as the broadest possible one. A false accept **by construction**, with
   zero corpus files using the syntax.
2. **`Tagged`** — march's `caps_in_ty` now recurses into it; `capsInTy` still
   mirrors the arm march deleted.
3. **Check 4 semantics (march#209)** — an importer now inherits only the caps
   of the functions it references. This checker still uses the whole-module
   rule, so it is now strictly STRICTER than march: a false-REJECT direction.
4. **`normalize`** — march's dedupes, ours does not. Latent only because
   `normalize` is not on the verdict path.

Gaps 1 and 3 are the ones with teeth, and they point opposite ways. Neither
has a corpus witness; both need hand-built probes.

## 3. Coverage change

`accept/t49_transitive_use_covered` regressed MATCH -> SKIP, so A3 slice (a)
now holds 10 of the 11 files it claimed. The cause is not a checker
regression: march#209 rewrote the file to add `Vault.new("t")` (the reference
the new Check 4 requires), march accepts it, and march's own
`--emit-core-ast` emits `resolved_ty: TError` for that stdlib call. H3
honest-skips on `TError`, which is correct behavior. The inconsistency —
an accepted program whose emitted AST carries an elaboration-error sentinel —
is march-side and is recorded as a finding.

## 4. What did NOT change

`format_version` is still 3, so no emitter-version dance and no two-repo
sequencing. `module_caps` is still emitted. The harness, exit-code contract,
and `Compare` are untouched.

## 5. If you are bumping the pin again

- Build march from the target SHA. Do not trust whatever `march` is on PATH.
- Diff `lib/dump/ast_json.ml`, `lib/caps/`, and the corpus file count first;
  those three predicted every finding here.
- Read new corpus filenames as a checklist. `reject/t148`-`t152` named their
  own subject matter, and each one that skips rather than matches is a
  question, not a pass.
- A skip is not a pass. Nine of the 26 new ledger entries are capability
  rejects this checker cannot judge.
