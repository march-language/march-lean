# A2-reject two-sided oracle — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.
>
> **Executes in the `march-lean` repo**, on a branch off `main` (A2 is merged as #5). Design doc: `specs/plans/2026-07-22-a2-reject-oracle-design.md` — read §2 (exit codes), §3 (harness table), §4 (triage) first. The march emitter is **unchanged**.

**Goal:** Make `march-lean-check` render its own accept/reject verdict on every in-fragment file (ignoring march's verdict), so the harness can confirm march was right to *reject* — turning reject-corpus files from always-skipped into independently-judged.

**Architecture:** `Compare.inferModule` already distinguishes "inference found it ill-typed" from "inference ok but per-node types differ from `resolved_ty`" — but folds both into `.reject`. A2-reject splits them into a 4-way `OracleVerdict`, `MarchLeanCheck` maps that (plus linearity) to a redefined exit-code contract, and the harness — which already compares `march_verdict` to `lean_verdict` — gains exit-4 handling and reject-side skip-ledger enforcement.

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.29.0`), Lake, bash harness. No Mathlib.

## Global Constraints

- **Pure-independent:** `march-lean-check` must NOT read march's `verdict` or `diagnostics` to make its judgment. It keeps `parseVerdict` ONLY as the malformed/`format_version`-2 gate (→ exit 3) and IGNORES the returned verdict value.
- **Exit-code contract (redefined — the whole point):** `0` = A2 accepts (inference + linearity pass) AND per-node types agree with `resolved_ty`; `1` = A2 rejects (inference OR linearity found it ill-typed); `2` = skip (out-of-fragment / no module / unmodeled name); `3` = error (malformed JSON / wrong version); `4` = A2 accepts BUT per-node types disagree with `resolved_ty`.
- **The per-node cross-check runs ONLY after inference+linearity pass** — so on a rejected program inference fails first (exit 1) and the cross-check (whose `resolved_ty` target is error-y on a reject) never runs. This keeps "A2 rejects" (1) distinct from "types differ" (4).
- **Verdict-level, reject side:** both must reject for a MATCH; reject *reasons* are not compared. A2 accepting a march-rejected program is a MISMATCH.
- **No Mathlib.** Build with EXPLICIT targets `lake build MarchLean march-lean-check` (bare `lake build` = 0-job no-op). Committed tests must NOT `IO.FS.readFile` the gitignored `.superpowers/sdd/samples/` dir (breaks fresh-checkout CI).
- **Reject-side skips are now ledger-enforced** (were structural/uncounted) — a shrinking coverage tracker, like the accept side.

---

## File Structure

- `MarchLean/Result.lean` — **modify**: add the `OracleVerdict` type (the 4-way independent verdict).
- `MarchLean/Compare.lean` — **modify**: `inferModule` returns `OracleVerdict` (split the two current `.reject` cases into `.reject` [infer-fail] and `.typesDiffer` [cross-check-disagree]); update its `#eval` tests.
- `MarchLeanCheck.lean` — **modify**: remove the verdict gate, map `OracleVerdict` + linearity to exit `0/1/2/3/4`, `module:null` → skip.
- `scripts/conformance-harness.sh` — **modify**: add exit-`4`→MISMATCH handling; enumerate + enforce reject-side skips in the ledger (generalize the ledger check to both sides).
- `scripts/expected-skips.txt` — **regenerate** (Task 3): add reject-side skip entries.
- `.github/workflows/conformance.yml` — reused unchanged (CI pins the v2-emitter march `main`; the harness change is picked up automatically).

Local test resources (present from A2): samples `.superpowers/sdd/samples/*.json`; march v2 binary `/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/_build/default/bin/main.exe`; corpus `/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/specs/lang/types`.

---

## Task 1: `OracleVerdict` split + `MarchLeanCheck` rewire (one atomic change)

The result-type change and its only consumer (`MarchLeanCheck`) must land together — changing `inferModule`'s return type breaks the executable until `main` is rewired, so this is one task that ends with a green `lake build MarchLean march-lean-check`.

**Files:**
- Modify: `MarchLean/Result.lean` (add `OracleVerdict`)
- Modify: `MarchLean/Compare.lean` (`inferModule` returns it; update `#eval` tests)
- Modify: `MarchLeanCheck.lean` (remove verdict gate; map to exit `0/1/2/3/4`)

**Interfaces:**
- Produces: `MarchLean.Result.OracleVerdict` (`| accept | reject (msg : String) | typesDiffer (msg : String) | skip (reason : String)`, `deriving Repr`) and `MarchLean.Compare.inferModule : Module → IO OracleVerdict`.

- [ ] **Step 1: Add `OracleVerdict` to `Result.lean`**

After the existing `CheckResult` (`MarchLean/Result.lean:17-21`), add:

```lean
/-- A2's INDEPENDENT verdict on a program, distinct from A1's `CheckResult`:
`reject` (inference found it ill-typed) is kept separate from `typesDiffer`
(A2 accepts it as well-typed, but its per-node types disagree with march's
`resolved_ty`). `MarchLeanCheck` maps these to distinct exit codes (1 vs 4) so
the harness can tell "A2 rejects the program" apart from "A2 accepts it but
disagrees on types" — collapsing them would hide a reject-file disagreement. -/
inductive OracleVerdict where
  | accept
  | reject (msg : String)
  | typesDiffer (msg : String)
  | skip (reason : String)
  deriving Repr, Inhabited
```

- [ ] **Step 2: Change `inferModule`'s return type + split the reject cases**

In `MarchLean/Compare.lean`, `inferModule` (currently `: Module → IO CheckResult`, line 274). Change the signature to `: Module → IO OracleVerdict` and remap its returns:
- the `.skip` returns (out-of-fragment decl, out-of-fragment constraint, `out of modeled fragment: {e}`) → `.skip` (unchanged tag, new type).
- `return .reject s!"MISMATCH (infer): {e}"` (inference failure, ~line 290) → `return .reject s!"infer: {e}"` (A2's reject verdict — inference found it ill-typed).
- `return .reject s!"MISMATCH (type) at {repr span}"` (per-node cross-check disagreement, ~line 303) → `return .typesDiffer s!"type at {repr span}"` (A2 accepts, but types differ).
- `return .ok` (line 305) → `return .accept`.

(Update `open`/references so `OracleVerdict` resolves; it lives in `MarchLean.Result` which `Compare` already opens.)

- [ ] **Step 3: Update the `#eval` sanity tests in `Compare.lean`**

The existing `Compare.Test` `#eval`s expect `CheckResult.ok`/`.reject`/`.skip`. Update the expected values to the new type:
- the ok-case → `OracleVerdict.accept`.
- the reject-type-case (cross-check disagreement) → `OracleVerdict.typesDiffer ...`.
- the reject-infer-case (inference failure) → `OracleVerdict.reject ...`.
- the skip cases → `OracleVerdict.skip ...`.
Keep them hand-built (no sample `readFile`).

- [ ] **Step 4: Confirm the lib compiles + tests pass (exe still red — that's why we continue in this same task)**

Run: `export PATH="$PATH:/Users/80197052/.elan/bin" && lake build MarchLean.Compare 2>&1 | tail -5`
Expected: clean; the `#eval`s print the new `OracleVerdict.*` values. (`lake build march-lean-check` will fail until Step 5 rewires `MarchLeanCheck` — do NOT commit yet; this task commits once at Step 6 with a green exe.)

- [ ] **Step 5: Rewrite `MarchLeanCheck.run` to the new contract**

Replace `MarchLeanCheck.lean`'s `run` (the whole function below — no verdict gate, `module:null`→skip, exit `0/1/2/3/4`):

```lean
def run (input : String) : IO UInt32 := do
  match Json.parse input with
  | .error e => IO.eprintln s!"invalid JSON: {e}"; pure 3
  | .ok envelope =>
    -- Version/format gate ONLY: reuse parseVerdict for the malformed /
    -- format_version≠2 check (→ exit 3), but IGNORE march's verdict — A2
    -- renders its OWN verdict below (pure-independent).
    match MarchLean.Json.parseVerdict input with
    | .error msg => IO.eprintln msg; pure 3
    | .ok _ =>
      -- A parse-reject emits "module": null — no AST to judge ⇒ skip.
      match envelope.getObjVal? "module" with
      | .ok .null => IO.eprintln "skip: no module (parse failure)"; pure 2
      | _ =>
        match MarchLean.Elab.decodeModule envelope with
        | .error e => IO.eprintln s!"decode error: {e}"; pure 3
        | .ok m =>
          let iv ← MarchLean.Compare.inferModule m
          match iv with
          | .skip r => IO.eprintln s!"skip: {r}"; pure 2
          | .reject r => IO.eprintln s!"reject (infer): {r}"; pure 1
          | _ =>  -- .accept or .typesDiffer: A2 says well-typed; check linearity
            match MarchLean.Linearity.checkLinearity m with
            | .skip r => IO.eprintln s!"skip: {r}"; pure 2
            | .reject r => IO.eprintln s!"reject (linearity): {r}"; pure 1
            | .ok =>
              match iv with
              | .typesDiffer r => IO.eprintln s!"accept, but types differ: {r}"; pure 4
              | _ => pure 0
```

Notes: `envelope.getObjVal? "module"` returns `Except String Json`; `.ok .null` matches the JSON null literal (`Lean.Json.null`). Everything else (missing/object) falls to the decode path. Update imports if needed (`Compare` and `Linearity` are already imported).

- [ ] **Step 5b: Build the whole thing green**

Run: `lake build MarchLean march-lean-check 2>&1 | tail -5`
Expected: clean (lib + exe).

- [ ] **Step 5c: Verify the new exit codes**

```bash
export PATH="$PATH:/Users/80197052/.elan/bin"; B=./.lake/build/bin/march-lean-check
M=/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/_build/default/bin/main.exe
C=/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/specs/lang/types
# accept-corpus modeled file -> A2 accepts + types match -> 0
$M --emit-core-ast $C/accept/t01_literals.march 2>/dev/null | $B; echo " accept=$?"
# a reject-corpus TYPE-ERROR file -> A2's inference fails -> 1 (was 2 skip under A2)
$M --emit-core-ast $C/reject/t01_int_vs_string.march 2>/dev/null | $B; echo " reject-type=$?"
# malformed -> 3 ; a parse-reject (module:null) -> 2
printf 'not json' | $B; echo " malformed=$?"
```
Expected: `accept=0`, `reject-type=1` (A2 independently rejects the int/string mismatch — the key new behavior), `malformed=3`. If `reject-type` is 2 (skip) instead of 1, the file hit the skip gate or an unmodeled-name path — check the stderr; if it's 0/4, A2 wrongly accepted an ill-typed program (investigate before proceeding — that's a real engine gap).

- [ ] **Step 6: Commit (single atomic commit — lib + exe green together)**

```bash
git add MarchLean/Result.lean MarchLean/Compare.lean MarchLeanCheck.lean
git commit -m "feat(marchlean): two-sided OracleVerdict + independent verdict exit codes 0/1/2/3/4 (A2-reject Task 1)"
```

---

## Task 2: Harness — exit-4 handling + reject-side skip-ledger

**Files:**
- Modify: `scripts/conformance-harness.sh`

**Interfaces:**
- Consumes: `march-lean-check`'s new exit codes (0/1/2/3/4).

- [ ] **Step 1: Map exit 4 (and re-confirm the verdict comparison)**

In `scripts/conformance-harness.sh`'s classification (the `case "$lean_exit"` block, ~line 187, and the `if/elif` classification below it, ~line 216): the harness already maps `0→accept, 1→reject, 2→skip, 3→error` and does `march_verdict != lean_verdict → MISMATCH`. Add exit **4**: it means "A2 accepts the program but its types differ from `resolved_ty`" — a MISMATCH in BOTH directions (on an accept file it's a type divergence; on a reject file A2 wrongly accepted). So:

In the `case "$lean_exit"` block, add before the `*)` default:
```bash
        4) lean_verdict="types_differ" ;;
```
Then in the classification `if/elif` chain, add a branch (before the `march_verdict != lean_verdict` comparison) that treats `types_differ` as a mismatch regardless of march's verdict:
```bash
    elif [ "$lean_verdict" = "types_differ" ]; then
        mismatch_files="$mismatch_files$f (A2 accepts but per-node types differ from resolved_ty; march=$march_verdict)"$'\n'
```

- [ ] **Step 2: Enumerate + enforce reject-side skips in the ledger**

Currently reject-side skips are only counted (`reject_skip_n`), not ledger-checked (the header comment says "reject-side skips are NOT enumerated"). Under A2-reject, reject files split into judged (match/mismatch) and skipped, so the reject-side skip set is now a shrinking coverage tracker and must be enforced like the accept side. In the `lean_verdict = skip` branch (~line 227), record reject-side skip paths too:
```bash
        skip_files="$skip_files$f (lean_verdict=skip, march_verdict=$march_verdict)"$'\n'
        observed_skip_paths="$observed_skip_paths$parent_dir/$(basename "$f")"$'\n'
```
(Introduce `observed_skip_paths=""` alongside `accept_skip_paths=""` in the init block ~line 147; it now holds BOTH `accept/...` and `reject/...` skip paths.) Then in the skip-ledger comparison block (after the loop, the block that diffs `accept_skip_paths` against `expected-skips.txt`), compare `observed_skip_paths` (both sides) against the full ledger:
```bash
    observed_skips_sorted="$(printf '%s\n' "$observed_skip_paths" | sed '/^$/d' | sort -u)"
    expected_skips_sorted="$(sed 's/#.*//; s/[[:space:]]*$//; /^$/d' "$expected_ledger" | sort -u)"
    if [ "$observed_skips_sorted" != "$expected_skips_sorted" ]; then
      echo "SKIP-LEDGER MISMATCH — observed skips (accept+reject) differ from scripts/expected-skips.txt:"
      diff <(printf '%s\n' "$expected_skips_sorted") <(printf '%s\n' "$observed_skips_sorted") || true
      ledger_fail=1
    fi
```
(Keep `reject_skip_n` for the summary line if you like; the ledger now governs both sides.) Update the header comment (the block that says reject-side skips are not enumerated) to reflect that BOTH sides are now ledger-tracked.

- [ ] **Step 3: Syntax-check the harness**

Run: `bash -n scripts/conformance-harness.sh && echo "parse OK"` — Expected: `parse OK`. (Optionally `shellcheck scripts/conformance-harness.sh`.)

- [ ] **Step 4: Commit**

```bash
git add scripts/conformance-harness.sh
git commit -m "feat(harness): exit-4 mismatch + reject-side skip-ledger enforcement (A2-reject Task 2)"
```

(The ledger itself is regenerated in Task 3 — the harness will fail the ledger check until then, which is expected.)

---

## Task 3: Exploratory corpus run, reject-side triage, ledger regen, forced-relaxation

**Prerequisite:** march v2 binary built (path in File Structure); `march-lean-check` built.

- [ ] **Step 1: Run the corpus, record the reject-side landscape**

```bash
cd /Users/80197052/code/march-lean/.claude/worktrees/<a2-reject-worktree>
export PATH="$PATH:/Users/80197052/.elan/bin"
export MARCH_BIN=/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/_build/default/bin/main.exe
export CORPUS_DIR=/Users/80197052/code/march/.claude/worktrees/a1-emit-core-ast-v2/specs/lang/types
export MARCH_LEAN_CHECK_BIN=$(pwd)/.lake/build/bin/march-lean-check
bash scripts/conformance-harness.sh 2>&1 | tee /tmp/a2reject_run1.log || true
```
Record MATCH / MISMATCH / SKIP counts. **This is the exploratory run** (design §4/§6): reject files A2 now judges will produce MATCHES (both reject) and MISMATCHES (A2 accepts a march-reject because it doesn't model that reject reason) — the mismatches are expected triage, not a blocker.

- [ ] **Step 2: Triage every reject-side MISMATCH**

For each `reject/*.march` file reported MISMATCH (A2 accepted a program march rejected), pipe it through `$MARCH_BIN --emit-core-ast FILE | $MARCH_LEAN_CHECK_BIN` and read the exit/stderr. Classify (per design §4):
- **A2 SHOULD have caught it, cheaply modelable** (e.g. a type error A2's inference missed, or a check like match-exhaustiveness that's in-fragment): extend the engine (its own commit + review) so A2 rejects it. Prefer this when the reject reason is genuinely in the Core+linearity fragment.
- **Reject reason is out of A2's fragment** (non-exhaustive match if you choose not to model it, `let?`/Result, refinement, capability, a march-specific stricter rule): **skip-ledger** the file — but a MISMATCH means A2 *accepted* it, so it did NOT skip. To make it skip, the construct must trip the whole-file skip gate. If the file uses an out-of-fragment construct that the decoder currently decodes as in-fragment, that's the gap: the fix is that the file's out-of-fragment feature should decode to `unsupported` (so `Decl.hasUnsupported` skips it). If instead the program is fully in-fragment but march rejects for a subtle reason A2 can't model, record it as a **documented finding** (a genuine A2-completeness limitation) and skip-ledger it via a targeted mechanism — do NOT silence it by making the checker lie. Report each such file and its disposition.
Iterate until every reject-side MISMATCH is either fixed (A2 now rejects → MATCH) or converted to a documented skip. Do the same for any accept-side regression (there should be none — the accept side is unchanged).

- [ ] **Step 3: Regenerate `scripts/expected-skips.txt` (both sides)**

From the final all-green run, regenerate the ledger to include BOTH accept-side and reject-side skip paths (one relative path per line: `accept/...` and `reject/...`, each with a `# reason` comment). Update the ledger's header comment to note it now covers both sides. Confirm the harness's ledger check passes (observed == expected).

- [ ] **Step 4: Reject-side forced-relaxation acceptance test**

Prove the reject signal is load-bearing: temporarily break the engine so it *accepts* an ill-typed program — e.g. in `MarchLean/Infer.lean`'s `unify`, delete the `con` name check so `Int` unifies with `String` (a real type error is no longer caught). Rebuild `march-lean-check`, rerun the harness, and confirm at least one **reject** file flips MATCH→MISMATCH (A2 now wrongly accepts a march-reject) and the harness exits nonzero. Then revert (confirm `git diff` clean on the engine sources), rebuild, rerun, confirm all-green. Paste both runs' summaries in the report. Do NOT commit the break. (Keep A2's accept-side forced-relaxation intact — this adds the reject-side one.)

- [ ] **Step 5: Commit**

```bash
git add scripts/expected-skips.txt   # + any engine fixes from Step 2 (separate commits)
git commit -m "test(a2-reject): reject-side triage, dual-side skip-ledger, forced-relaxation (A2-reject Task 3)"
```

---

## Done criteria

- `lake build MarchLean march-lean-check` green; `#eval` tests print the new `OracleVerdict.*` values.
- `march-lean-check` renders an independent verdict (ignores march's `verdict`); exit codes 0/1/2/3/4 verified; a reject-corpus type-error file now exits **1** (independently rejected), was 2 (skip).
- Full corpus: 0 MISMATCH / 0 ERROR over the modeled accept+reject subset; observed skips (both sides) == the regenerated dual-side ledger; RESULT: PASS.
- Reject-side forced-relaxation flips ≥1 reject file MATCH→MISMATCH and reverts to green (evidence in the report).
- Every reject-side divergence found is either fixed (A2 rejects) or a documented skip-ledger entry with a recorded reason. Any genuine A2-completeness limitations are recorded as findings.
