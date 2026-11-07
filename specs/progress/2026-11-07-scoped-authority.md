# Scoped authority and concrete normalization

Task 3 of the future-theory plan connects lexical scope containment to the
exported module's capability checks. Task 2's graph closure and grant proofs
remain imported into the build. Validation targets March main
`e6b528f6f410d97f038cfe54e1b9817a466acb6e`, fetched on 2026-11-07;
the CI binary and corpus use this same revision.

## Executable definitions and proofs

- `CapScope.Scope` distinguishes unbounded authority from an absolute or
  relative path represented as lexical segments. `Scope.ofPath` follows
  `lib/caps/cap_scope.ml`: collapse empty and `.` components, pop on `..`,
  drop traversal above the root, preserve absolute versus relative roots.
- `scopeSubsumes` uses segment prefixes, so `/etc` covers `/etc/a` but cannot
  cover `/etcpasswd`. `Authority` combines the capability ancestry order with
  this scope order; `covered` requires one authority witness covering both.
- `Calculus.Scopes` proves reflexivity, transitivity and antisymmetry for
  both orders, an existential characterization of executable coverage, and
  monotonicity when grants are added. These are general kernel proofs over
  the segment representation. Raw-string normalization examples use native
  evaluation separately; no general theorem depends on those examples.
- Concrete `CapLattice.normalize` deduplicates first, then applies the
  historical domination filter. `Calculus.Concrete` proves duplicate-free
  output, survivor order as a sublist, idempotence and coverage preservation.
  The old abstract duplicate-preserving `normalizeIn` remains explicitly
  distinct. The `CheckCaps` bridges and `no_extern` normalization
  counterexample are retained.
- The persistent axiom audit now checks 22 public results from Tasks 2 and 3,
  allowing only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

## Decode/check connection

`Syntax.ScopeFacts` preserves each module's declared authorities, its effective
scope environment, and raw literal-path uses alongside the existing declarations.
`Elab.decodeScopeFacts` requires a string scope entry for every declared path;
missing, null, or differently sized arrays are malformed inputs. The historical
return-capability envelope regression now includes the current exporter's
`scopes` field. Raw capability
manifests remain available for syntax-sensitive behavioral checks.

`Elab.literalPathUses` walks the exported syntax before annotation erasure. It
matches March's literal-only path positions (including both arguments of
`file_copy` and `file_rename`), traversal, and intentional omissions such as
match guards and `ECond`. Computed paths are not statically rejected. The current
source rule recognizes bare builtin spelling even when shadowed; this is not
claimed to be a fully resolved semantic effect analysis.

`CapCheck.checkScopeFacts`, called by the shipping `checkCaps`, validates scope
kinds and absolute roots, then checks literal requirements with `Authority`
coverage. A module with no relevant declaration leaves the missing-capability
error to the existing needs pass. An unbounded declaration permits every path.
Signature and main-grant checks remain capability-only because the exported
`Cap` types do not contain path requirements.

The prior whole-file skip for scoped needs is removed. `Infer.builtins` also
registers March's monomorphic `file_exists : String → Bool`: the accepted
source probes first exposed its absence as an unrelated inference skip.

## Review finding and execution rulings

1. **Nested environment:** March checks a nested module's literal paths with
   the preceding *outer* environment, while validating the child's own scope
   declarations separately. The entry module uses its final environment.
   The first Lean implementation incorrectly checked every module with its
   own declarations. Two raw checker regressions failed before the fix:
   outer `/etc`, child `/srv`, literal `/etc/a` must pass; `/srv/a` must reject.
   The decoder now threads the preceding outer environment, and source probes
   pin both outcomes. This mirrors current March rather than asserting a
   stronger own-manifest restriction. Cost if the upstream rule changes:
   update the environment bridge and these probes with the new main revision.
2. **Empty scope export:** the emitter uses `""` for both no scope and the
   invalid source declaration `needs IO.FileRead("")`. The decoder must treat
   this sentinel as unbounded, while `Scope.ofPath ""` denotes an actual
   relative empty path. The source distinction cannot be reconstructed from
   the current export. It needs a nullable/tagged export field; no claim here
   covers erased source validation failures.
3. **Proof boundary:** the order proofs apply to the actual coverage operation;
   they do not prove the OCaml exporter, graph extraction, raw syntax walk,
   filesystem symlink resolution, race freedom, or OS sandbox enforcement.
   Native path examples and differential probes are evidence for the bridge,
   not a proof of full March source or runtime soundness.

## Validation

The duplicate regression was observed failing before deduplicate-first
normalization; the scoped-needs probe failed under the old unsupported gate.
Both now run in the regular suite. The nested environment tests above were
also observed failing before the review fix. Raw JSON guards exercise preserved
scopes, sentinel handling, malformed arrays, literal positions, and annotation
erasure. Source probes cover containment, near-prefix escape, traversal,
relative paths, union grants, unbounded grants, broad filesystem grants,
invalid scope kinds, computed paths, and nesting; their verdicts and diagnostics
are mutated to demonstrate independent decisions.

Final local results:

- `lake build`: all 46 build jobs pass.
- Axiom audit: all 22 public capability theorems pass.
- All 31 source regression probes pass, including verdict-independence mutations.
- All 22 tail-call probes pass.
- Full 601-file conformance gate: 108 matches, 492 skips, one known erased-derive
  limitation; zero mismatches, errors, compiler/export inconsistencies or corpus
  violations. Both ledgers pass, with no membership changes from Task 2.

The compiler captures were freshly generated from a clean build of the revision
above. The local shell gate replayed those immutable outputs while executing the
final Lean checker anew; CI invokes the real compiler directly. The PR's
Conformance run is the published CI result for the pushed commit.
