# march-lean

An independent Lean checker for a **modeled subset** of March’s exported core
AST, plus a proof layer for its capability lattice, effect closure, grants and
checker algebra.
Acceptance is not a proof of the whole March compiler. Unsupported language
features explicitly skip; known export limitations are tracked separately.

## Build

Install elan and put its `bin` directory on `PATH`, then:

```sh
lake build
```

This builds both `MarchLean` (including the proof modules and regression guards)
and `.lake/build/bin/march-lean-check`, using the version in `lean-toolchain`.

```sh
/path/to/march --emit-core-ast program.march | .lake/build/bin/march-lean-check
```

Checker exit codes: `0` accept, `1` reject, `2` unsupported/skip, `3` malformed
input/internal error, `4` inferred types disagree with March’s witnesses.
The checker does not use March’s verdict or diagnostic messages to decide its
answer.

## Verify against March

CI pins March and its corpus to the same full revision in
[the workflow](.github/workflows/conformance.yml). Build that revision in a clean
March checkout with `dune build --root . bin/main.exe`; use that binary rather
than an unrelated installed `march`. Install `jq`, `python3`, and `z3`.

```sh
scripts/conformance-harness.sh \
  --march-bin /path/to/march/_build/default/bin/main.exe \
  --corpus-dir /path/to/march/specs/lang/types \
  --lang-dir /path/to/march/specs/lang \
  --march-lean-check-bin "$PWD/.lake/build/bin/march-lean-check"

scripts/tailcall-probes.sh \
  --march-bin /path/to/march/_build/default/bin/main.exe \
  --march-lean-check-bin "$PWD/.lake/build/bin/march-lean-check"

python3 scripts/sync-probes.py \
  --march-bin /path/to/march/_build/default/bin/main.exe \
  --march-lean-check-bin "$PWD/.lake/build/bin/march-lean-check"
```

The harness rejects new disagreements, compiler/export verdict inconsistencies,
incorrect corpus placement, and drift in either direction of the skip and
known-limitation ledgers. The sync probes additionally flip the compiler’s
verdict and remove diagnostics to check oracle independence.

## Current scope and next work

- [November main-sync audit](specs/plans/2026-11-06-march-main-resync.md)
- [Capability closure and grant proofs](specs/progress/2026-11-06-capability-closure-proofs.md)
- [Future theory plan](specs/plans/2026-11-06-future-theory.md)
- [Historical findings](specs/march-findings.md)

Capability closure and grant checking are now proved for the finite effect
graph used by the executable; source extraction remains outside that proof.
Lexical scoped authority and concrete normalization are also implemented;
linear ownership and a typed operational core remain next. See the
[scope proof record and export limits](specs/progress/2026-11-07-scoped-authority.md).

Audit the public capability theorems' trust dependencies with:

```sh
lake env lean scripts/check-closure-axioms.lean
```
