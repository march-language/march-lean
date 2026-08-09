# march findings

`march-lean-check` is a differential oracle: it independently re-implements
march's ERROR-level static checks and re-checks march's own compiler output.
Any disagreement between the two sides is a finding about *one* side or the
other — sometimes march is right and the checker has a gap (fixed in
`march-lean`), sometimes the checker is right and march has a bug. This file
is the oracle's output channel for the latter kind: confirmed march bugs,
recorded here so they can be reported upstream and are not lost. Each entry
should be self-contained (reproducer + source location + status) and this
file should stay simple to append to — new findings go at the bottom, in the
same format as the first entry below.

## Format

Each entry:
- **What was found** — one or two sentences.
- **Reproducer** — a minimal `.march` snippet and the two exit codes
  (march's `--check`/`--emit-core-ast`, and `march-lean-check`).
- **march's source location** — file and line range of the bug.
- **Which side is wrong** — march or the checker (this file only records
  march-is-wrong findings; a checker-is-wrong finding is a bug to fix in
  `march-lean`, not an entry here).
- **How it was found** — which A-series slice/task surfaced it.
- **Status** — `reported upstream: NOT YET` / `reported upstream: <link>` /
  `fixed upstream: <link>`.

---

## Finding: `calls_in_expr` misses IO calls nested inside tuple/record/list literals

**What was found.** march's Check 8 (migrate-state IO-freedom) walks a
function body looking for IO-capable builtin calls via `calls_in_expr`. That
walk is not total over `Ast.expr`: it ends in a catch-all `| _ -> acc` and has
no arm for `ETuple`, `ERecord`, or `EList`, so a call nested directly inside
one of those literals is never visited. The result is a false ACCEPT: a
`*_migrate_state` function that performs IO from inside a tuple/record/list
expression is silently let through, even though march's own stated invariant
for migrate-state functions is that they must be IO-free.

**Reproducer.**
```march
mod Counter do
  needs IO.Console
  fn counter_migrate_state(old : Int) : (Unit, Int) do (println("hi"), old) end
end
```
- march (`--check` / `--emit-core-ast`): exit 0 (ACCEPT) — the `println`
  inside the `ETuple` is invisible to `calls_in_expr`.
- `march-lean-check`: exit 1 (REJECT) — `MarchLean/CapCheck.lean`'s
  `bodyCallsIO` is a total structural walk over every `Term` constructor
  (including `.tuple`), so it correctly finds the nested `println` call and
  flags Check 8.

**march's source location.** `lib/typecheck/typecheck.ml`, `calls_in_expr`,
lines 6740–6769 (catch-all `| _ -> acc`; no `ETuple`/`ERecord`/`EList` arm).
This function is called from Check 8's body scan at line 6909
(`calls_in_expr [] clause.Ast.fc_body`). Note the file defines **two**
functions named `calls_in_expr`: this one at line 6740, and an unrelated
second `let rec calls_in_expr` at line 8063 (used later in the file, by the
panic-surface/no-panic check, not by Check 8). All references above are to
the first one, at line 6740.

**Which side is wrong.** march. The checker's total walk is the correct
behavior per march's own documented Check 8 invariant; march's traversal has
a gap that lets IO leak out of a migrate-state function through a
tuple/record/list literal.

**How it was found.** A3 slice (b), implementing Check 8 (migrate-state
IO-freedom) in `MarchLean/CapCheck.lean` (`bodyCallsIO`) and cross-checking
its behavior against march's `calls_in_expr` line by line.

**Status.** reported upstream: https://github.com/march-language/march/issues/82 (filed 2026-07-24)

---

## Finding: the SECOND `calls_in_expr` (pure/deterministic/no_panic) has the identical missing-`ETuple` gap, and feeds three checks, not one

**What was found.** The entry above flagged that march's source defines a
second, unrelated `let rec calls_in_expr` (then at line 8063) but only
attributed it to "the panic-surface/no-panic check." That was incomplete:
this second copy is the single shared body-walk behind **three** checks —
`check_pure_module`, `check_deterministic_module`, and
`check_no_panic_module` — and it ends in the exact same catch-all `| _ ->
acc` with no `ETuple` (or `ERecord`/`EList`) arm as the first copy. A direct
call hidden inside a tuple element is therefore invisible to `cap pure`,
`cap deterministic`, and `cap no_panic` alike, not just to the no-panic
check. This is the root cause of three false REJECTs surfaced by
`MarchLean/CapCheck.lean`'s `bodyCalls` (a deliberately total walk that
already handles `.tuple`, per Check 8's fix) against march's real,
non-total walk.

**Reproducers.** All three verified directly against
`_build/default/bin/main.exe` and `march-lean-check` on this branch:

```march
mod P do
  cap pure
  needs IO.Console
  fn f() : (Unit, Int) do (println("hi"), 1) end
end
```
- march (`--check`): exit 0 (ACCEPT) — `println` inside the `ETuple` is
  invisible to `calls_in_expr`.
- `march-lean-check`: exit 1 (REJECT) — `cap pure: fn `f`... performs a
  side effect`.

```march
mod P do
  cap deterministic
  needs IO.Clock
  fn f() : (Int, Int) do (unix_time_ms(()), 1) end
end
```
- march: exit 0 (ACCEPT). `march-lean-check`: exit 1 (REJECT) — `cap
  deterministic: fn `f`... performs a non-deterministic operation`.

```march
mod P do
  cap no_panic
  fn f() : (Unit, Int) do (panic("boom"), 1) end
end
```
- march: exit 0 (ACCEPT). `march-lean-check`: exit 1 (REJECT) — `cap
  no_panic: fn `f`... may panic (explicit panic)`.

**march's source location.** `lib/typecheck/typecheck.ml`, the second `let
rec calls_in_expr` (currently lines 8834–8863; catch-all `| _ -> acc` at
line 8863, no `ETuple`/`ERecord`/`EList` arm — structurally identical to the
first copy's gap). Called from `check_no_panic_module` (line 8886, body
scan inside `check_no_panic_module` at line 8879), `check_pure_module`
(line 9009, function starts line 9003), and `check_deterministic_module`
(line 9074, function starts line 9068).

**Which side is wrong.** march. `MarchLean/CapCheck.lean`'s `bodyCalls` is
a single generalised walk (Task 1 of this slice) shared by Check 8 and by
the `cap pure`/`deterministic`/`no_panic` explicit-call scan; it is total
over every `Term` constructor including `.tuple`, matching the checker's own
already-established correct behavior for Check 8 above. march's traversal
has the same gap in its second copy, letting a banned call leak out of a
`cap pure`/`deterministic`/`no_panic` function through a tuple literal.

**How it was found.** A3 slice (c), generalising `bodyCallsIO` to
`bodyCalls` and reusing it for the `pure`/`deterministic`/`no_panic`
explicit-call scan; the resulting three false REJECTs (oracle rejects,
march accepts) were traced to this second `calls_in_expr` copy by reading
`typecheck.ml` end to end and confirming empirically with the reproducers
above (2026-07-31).

**Status.** reported upstream: NOT YET — same underlying defect class as
march#82 but a distinct source location (second copy, three different call
sites); should be reported as its own issue or as an amendment to #82 since
the fix (adding `ETuple`/`ERecord`/`EList` arms to *this* `calls_in_expr`,
not just the first one) is a separate code change.

---

## Checker gaps against march main 6867c783 that the corpus CANNOT catch

Unlike every entry above, these are **checker-is-wrong** items, recorded here
by exception because of a property they share: each is a live divergence
against the pinned march with **zero corpus witnesses**, so the conformance
gate is structurally incapable of reporting them. The standing rule that a
green run is weak evidence is usually a caution; here it is a certainty.
Each needs a hand-built probe, not a corpus file.

Found during the 2026-08-08 capability resync (pin 7c1d701c -> 6867c783),
which fixed five corpus-visible divergences; these three were found by
reading march's diff rather than by running anything.

### 1. Path-scoped capabilities decode as unscoped — FALSE ACCEPT by construction

march added scopes: `needs IO.FileRead("/etc/myapp")` narrows a filesystem
capability to a directory subtree (`lib/caps/cap_scope.ml`). The emitter now
carries them in a NEW `scopes` array parallel to `paths`, and march's own
comment on that change says the scope is emitted "so a dumped AST is not a
widened version of the source."

`Elab.decodeDecl`'s `DNeeds` arm reads only `paths`. The scope is dropped, so
a scoped declaration decodes identically to an unscoped one. Since
`Cap_scope.scope_subsumes` states that `None` (unscoped) subsumes everything
and **a scope never subsumes `None`**, this checker reads a strictly narrower
declaration as the broadest possible one — the exact direction that produces
a false accept.

Not yet reachable in the corpus: no file under `specs/lang/types` uses the
syntax. That is why it is dangerous rather than reassuring.

**Fix shape.** Decode `scopes` alongside `paths`, carry the scope on
`Decl.dneeds`, and gate coverage on `scope_subsumes` as well as
`capSubsumes`. Until then this is a known false-accept source.

### 2. `capsInTy` does not descend into `Tagged`

march's `Cap_surface_ty.caps_in_ty` recurses into every `TyCon`'s arguments,
including `Tagged`. Its predecessor had an explicit `| Tagged -> []` arm;
that arm is GONE, and march's comment records why: skipping it "also blinded
the walk to `Tagged(R, Cap(IO))`, which is a worse trade."

`CapCheck.capsInTy` still has `| .con "Tagged" _ => []`, mirroring the arm
march deleted. A capability nested inside a `Tagged` payload is therefore
invisible to Check 1 here and visible to march. No corpus file exercises it.

### 3. `normalize` does not deduplicate

march's `Cap_lattice.normalize` now dedupes before filtering; ours does not,
so the two disagree on any input containing repeated caps (ours returns the
duplicates, march returns one). march's change was a performance fix (an env
reused across ~1800 modules grew the list without bound), but it is a
semantic difference in the returned list.

Latent only because `normalize` is not on this checker's verdict path — it is
defined and proved about (`Calculus/Lattice.lean`) but never consulted by
`checkCaps`. If it is ever wired in, this must be fixed first, and the
`normalizeIn` theorems re-proved against the deduping definition.

### 4. Check 4 uses the pre-#209 whole-module rule — we are now STRICTER than march

march#209 ("an importer inherits only the capabilities it actually
references", 8f8c66d6) changed Check 4's semantics. `use M` used to force
every capability `M` declares onto the importer; it now forces only the
capabilities demanded by the functions the importer actually references, via
the new `import_required_caps`.

`CapCheck.checkOneModule`'s Check 4 still implements the old rule: it takes
`M`'s entire declared `needs` from the `module_caps` table and requires the
importer to cover all of it. march's own commit message states the change is
"strictly loosening by construction: the result is always a subset of what
the import required before" — so this checker is now strictly STRICTER than
march on Check 4, and the divergence direction is FALSE REJECT.

The witness shape: a module that imports a cap-declaring module but
references only its cap-free functions. march accepts (nothing referenced
demands the cap); this checker rejects (the cap is in `M`'s declared set).

No corpus witness today. `reject/t39_transitive_use_missing_cap` still
matches, because there the capability is uncovered under either rule.
`accept/t49_transitive_use_covered` was rewritten by the same commit to add
the reference the new rule requires (`let _ = Vault.new("t")`), and now
SKIPS here for an unrelated reason — see below.

**Corollary finding (march side): an accepted file's emitted AST contains
`TError`.** `accept/t49`'s added `Vault.new("t")` is a call into stdlib
`Vault`. march's `--check` resolves it and ACCEPTS; its own
`--emit-core-ast` emits `resolved_ty: TError` for that call and for the
enclosing `let`, while the envelope's `verdict` field still says `accept`.
This checker honest-skips on `TError` by design (H3: never check a file
built on an elaboration error), which is why t49 regressed MATCH -> SKIP and
why A3 slice (a) is now one file short of the 11 it claimed. The skip is
correct behavior here; the inconsistency is march emitting an
elaboration-error sentinel in a program it accepts.

**Status.** reported upstream: NOT YET (both halves).
