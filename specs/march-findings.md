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

**Status.** FIXED UPSTREAM — https://github.com/march-language/march/pull/136
(`fix(typecheck): calls_in_expr is now total over Ast.expr`), merged as
`9a373001`. The fix went further than this finding asked: it added an explicit
arm for EVERY `Ast.expr` constructor to BOTH copies of `calls_in_expr` and
removed the `| _ -> acc` catch-all entirely, so a future constructor fails to
compile here rather than silently falling through the scan again.

Confirmed converged: `(println("hi"), 1)` under `cap pure` is now rejected by
march AND by `march-lean-check`. The deliberate `bodyCalls` over-detection that
this finding documented is no longer a divergence.

Note the fix INVERTED the coverage relationship for a while — march's total
walk reached constructs our decoder mapped to `Term.unsupported`, so we skipped
where march rejected. Closed separately by `Term.opaque_` (nine AST kinds) and
by the `ELet` decode fix.

---

## Behavior we DEPEND ON (not a bug): march drops inferred `CInterface` constraints

**What.** `MarchLean/Infer.lean` registers `println : ∀a. a → ()` — fully
unconstrained. That is deliberately *more permissive* than it looks, and it is
correct only because of a specific march behavior.

march's builtin `("println", Mono (TArrow (t_string, t_unit)))`
(`typecheck.ml:1951`) is **dead code**. `stdlib/prelude.march:243` defines an
ordinary `fn println(x) do print(show(x)); print("\n") end`, and
`bin/main.ml:214-217` unwraps prelude.march's `mod` body into the entry
module's own top-level scope — it is the head of `stdlib_file_list`
(`bin/main.ml:236`) and the only stdlib file so unwrapped. The prelude binding
therefore shadows the builtin at every call site.

That prelude scheme is unconstrained. march attaches only *declared*
constraints — `bound_constraints` (`typecheck.ml:6926`) and `when`-clause
`class_constraints` (`typecheck.ml:7051`), spliced at `:7139-7165`. The
`CInterface("Show", _)` raised by the body's `show(x)` lands in
`env.pending_constraints` and is discharged at the declaration boundary while
still a `TVar`, hitting `| TVar _ -> ()  (* Still polymorphic — cannot check
yet *)` at `typecheck.ml:7530-7531`, and is dropped.

**Verified** (`march --check`, all exit 0): `println(1)`, `println(true)`,
`println((1,"a"))`, `println({x:1,y:2})`, `println(some_fn_name)`, and
`println(Red)` for a `type Color = Red | Green` with **no `impl Show`**.

**Why we match it rather than model `Show`.** A `Show`-constrained scheme would
be a NEW false-reject source here: this checker models no `impl` declarations
at all, so no `Show` constraint could ever discharge. Modelling march's actual
(constraint-dropping) behavior is the faithful choice.

**The fragility.** This is a bug-for-bug match against an *implementation
accident*, not a specified rule. If march ever propagates inferred
`CInterface` constraints into schemes, `println` becomes genuinely
`Show`-constrained and our unconstrained version starts **false-accepting** —
and no corpus file would catch the flip, because every corpus use of `println`
is on a Show-able type. Re-check this at every CI re-pin: if
`typecheck.ml:7530-7531` stops dropping `TVar` constraints, revisit
`Infer.lean`'s `println` registration.

**Contrast.** `print` is NOT prelude-shadowed (prelude defines no `fn print`),
so it keeps `Mono (String → ())` and march rejects `print(1)`. We match. The
`print`/`println` split is the discriminating pair — pinned by fixture.

**Status.** not a march bug; no upstream report. Recorded because our
correctness depends on it and the dependency is invisible from our source alone.

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

### 5. Check 1b is now an ERROR in march, and this checker does not implement it — a LIVE false-accept class

**This one obsoletes a design decision, so it is the most consequential entry
in this section.**

`specs/plans/2026-07-23-a3-capability-lattice-design.md` §1.3 decided NOT to
implement Checks 1b/1c, and said so plainly:

> They are WARNING-only in march. §2.8.6 calls this three-tier reality "the
> single most consequential fact for anyone relying on `needs` as a soundness
> guarantee." A checker that rejected on them would manufacture false
> MISMATCHes against a march that accepts. Consequence, stated plainly: the
> oracle inherits march's weaker guarantee here — it will not catch a program
> that uses a builtin requiring an undeclared cap in a function body.

That reasoning was correct when written. It is now obsolete: march main
(`6867c783`) raises Check 1b with `Err.error_with_fix`
(`typecheck.ml:9098-9106`), not `Err.warning` —

    function body calls a builtin that requires `Cap(IO.Console)`
    but `M` does not declare `needs IO.Console`.

march closed the hole its own docs called the most consequential fact about
`needs`. This checker did not, so the "weaker guarantee" the design accepted
is no longer shared with march — it is a **divergence**, and it points the
false-ACCEPT way: any module calling an IO builtin in a body without declaring
the capability is rejected by march and accepted here.

**Witness.** Every one of `scripts/tailcall-probes/*.march` before the
accompanying fix: `mod M do fn main() do println("hi") end end` with no
`needs`. march rejects; `march-lean-check` exits 0.

**How it was found, which matters more than the finding.** The 277-file
conformance corpus reports MISMATCH 0 against this same pin — every corpus
file declares its capabilities properly, so not one of them witnesses this.
It surfaced only because the tail-call probes were hand-written without
capability manifests and the pin bump made march start rejecting them. A
green corpus run said nothing about a whole false-accept class; eighteen
throwaway probes found it immediately.

**Fix shape.** The machinery already exists: `CapCheck.builtinCaps` maps
builtin name -> required cap path, and `bodyCalls` already walks bodies for
builtin calls (both were built for Check 8 and the behavioral caps). Check 1b
is those two joined to `covered declared`. What needs care is the gating, and it is
not hypothetical care — implementing this slightly too eagerly converts the
false-accept class into a false-REJECT class. Three specific hazards, all
verified against march `6867c783`:

1. **Shadowing.** `bodyCalls` matches purely by NAME
   (`banned.contains n`), with no scope awareness. A module defining its own
   `fn println(...)` and calling it would be flagged as calling the builtin.
   The corpus already contains shadowing cases
   (`accept/t126_entry_module_shadows_list_length`,
   `accept/t139_nested_module_shadows_list_length_extern`) and march grew
   `shadow_*` tail-call probes, so this WILL fire.
2. **Direct calls only.** march's own comment scopes 1b explicitly: it
   catches a direct builtin call in a module body; a stdlib-MEDIATED call
   (`File.read` rather than `file_read`) is invisible to it and is handled by
   `--cap-strict`'s TIR ceiling instead. Scanning transitively would reject
   where march accepts.
3. **1c stays off.** march flipped 1b only —
   Check 1c (extern implies `IO.Foreign`) is deliberately still a warning.
   Flipping both because they were skipped together would be wrong.

The self-declaration exemption applies here too: march tests
`not covered && not self_declared` against `env.proof_caps`, which
`checkOneModule` already threads as `selfDeclaredCaps`.

**Status.** reported upstream: N/A (march is correct here; this checker is
behind). NOT YET FIXED in march-lean.

### 6. No grant check at all — confirmed live false-accept, one instance fixed, the transitive-reach core is not

The 2026-08-10 sync-drift note (below the corpus this checker runs against
was rebuilt against march main HEAD `9d481cb3`, well past the CI pin —
see "Status" for what that means for THIS repo's gate) predicted that
`reject/t166_grant_narrow_violated_by_helper` and a since-renumbered sibling
would be hard MISMATCHes: march rejects a grant-narrowing violation,
`CapCheck.lean` has no grant-tracking at all, so it would accept. That
specific prediction was **verified false** — checked directly against a
march binary built from origin/main HEAD. Every corpus fixture built to
witness R1 stages A–D (`t166`, `t174_fn_grant_violated_by_helper`,
`t176_main_no_grant_does_io`, and their `t173`/`t175` SIMD/accept
neighbors — SIMD landed alongside grant-checking in the same window) uses a
builtin (`file_write`, `Simd.make_f32x4`, `Simd.splat_u8x16`) this checker's
`Infer.lean` does not type at all, so every one of them SKIPs with `unbound
variable` before the missing grant check would ever matter. Ledgered in
`scripts/expected-skips.txt`.

**But the full-corpus run this predicate ran under DID find a real,
different hard MISMATCH**: `reject/t177_main_mixed_param_list.march`
(`fn main(cap : Cap(IO), n : Int)`) — R1 stage D's rule that `main`'s
parameter list is zero-or-more capabilities, never a mix. march rejects it
outright, at signature-validation time, before grant-tracking runs at all.
`CapCheck.lean` had nothing checking `main`'s signature shape, so it fell
through every existing check to `.ok`. **Fixed**: `mainMixedParamsViolation`
(`MarchLean/CapCheck.lean`, wired into `checkOneModule` as `R1-D`) mirrors
`Desugar.check_main_signature` — reuses the existing `concreteLatticeCap`
IO-lattice predicate per parameter, `none`/non-`Cap(IO...)` counts as
non-capability. Verified: `t177` now correctly rejects, and the stage-D
multi-cap accept fixtures (`t174`–`t176` accept-side) are unaffected (they
still skip on `file_write`, unchanged).

**What is NOT fixed, and is a live false-accept: the transitive grant-reach
check itself** (R1 stages A/B/C — "the whole program's IO reach is held
under the union of `main`'s (or a function's) `Cap(...)` parameters").
`CapCheck.lean` has zero code implementing this — no call-graph closure, no
per-function grant discharge, nothing. It is invisible to the corpus purely
because every corpus witness happens to reach the violation through an
untyped builtin. It is NOT invisible in general — hand-built probe, run
directly against march origin/main HEAD and this checker:

```march
mod Main do
  needs IO.Clock
  needs IO.Console

  fn helper() : () do
    println("leak")
  end

  fn main(cap : Cap(IO.Clock)) : () do
    helper()
  end
end
```

`println` IS a typed builtin (`Infer.lean:941`, required cap
`IO.Console` per `CapCheck.builtinCaps`) — no `unbound variable` skip fires.
march rejects: `` `main` is granted `Cap(IO.Clock)`, but the program reaches
`IO.Console` (reached in `helper`) ``. `march-lean-check` exits 0 (accept).
This is the exact false-accept class the sync-drift finding warned about,
just witnessed through `println`/`IO.Console` rather than the corpus's
`file_write`/`IO.FileWrite` fixtures, because `println`/`print` are the
only two IO builtins `Infer.lean` types at all (every other entry in
`CapCheck.builtinCaps` — the `file_*`/`tcp_*`/`process_*`/... families
— is `unbound variable` to `Infer.lean` and skips first).

**Fix shape**, not attempted here: mirroring `check_main_grant` /
`check_fn_grants` (`typecheck.ml:12921-` onward) needs a call-graph closure
over which builtins/needs each function transitively reaches, held against
each grant point (`main`'s parameter union for stage A/B, each
`Cap`-parameter function's own parameters for stage C), plus stage D's
"performs IO but `main` takes no capability parameter" rule. This is
comparable in size to `CapCheck.lean`'s existing Check 1/4/5/8 machinery
combined, not a small addition, and a rushed version of a soundness-relevant
check risks trading a false-accept for a false-reject (see finding 5's three
hazards for the shape of that risk). Tracked as an open gap, not attempted
in this pass.

**Status.** reported upstream: N/A (march is correct; this checker is
behind). `t177`'s specific MISMATCH: **fixed in march-lean**. The general
transitive grant-reach check: **NOT YET FIXED**, confirmed live via the
probe above. Separately: **this repo's CI (`conformance.yml:139`) still
pins march at `6867c783`**, which predates the grant check entirely (R1
stages A/B landed in `78143049`/`759368b4`/`fb9a8c90`, all after that pin) —
so today's CI corpus doesn't contain `t166`–`t177` at all and this whole
finding is invisible to it either way. Bumping that pin is a separate,
larger action (full-corpus revalidation against everything march landed
since `6867c783`, not just the grant fixtures) and was not attempted here.
