#!/usr/bin/env bash
#
# conformance-harness.sh — diff march's own --check verdict against the
# Lean-side re-check (march-lean-check) over a corpus of *.march programs.
#
# For every "$CORPUS_DIR"/{accept,reject}/*.march file this:
#   1. runs `march --check FILE`            -> march_verdict (accept/reject)
#   2. runs `march --emit-core-ast FILE`    -> JSON envelope
#   3. feeds that JSON to `march-lean-check` -> lean_verdict (accept/reject/skip/error)
#   4. (cheap cross-check) compares the JSON's own "verdict" field against
#      march_verdict, to catch march disagreeing with itself
#   5. derives expected_verdict from the file's PARENT DIRECTORY (files
#      under accept/ are expected to accept, files under reject/ are
#      expected to reject — the corpus's own naming convention, see e.g.
#      specs/lang/types/INDEX.md) and compares it against march_verdict, to
#      catch march agreeing with itself and with Lean while both are simply
#      wrong (e.g. march's type checker regressed and started accepting
#      everything, or a missing external dependency like z3 silently
#      disabled a class of checks) — a case plain MISMATCH can never catch,
#      since at A0 the Lean side just echoes march's own verdict back
#
# and reports MATCH / MISMATCH / SKIP / ERROR / KNOWN_LIMITATION /
# MARCH_SELF_INCONSISTENT / CORPUS_VIOLATION counts, plus the filenames in
# every non-MATCH category.
#
# --- KNOWN_LIMITATION (A2-reject) ---
# A handful of reject/*.march files are rejected by march for a reason that is
# ERASED from the Core AST march-lean-check sees (e.g. a construct desugared
# away before --emit-core-ast runs), so A2 independently — and correctly, given
# only the residual well-typed program — accepts them. These would otherwise
# read as MISMATCH forever with no in-fragment fix. scripts/known-limitations.txt
# enumerates them (with reasons); a listed wrong-accept is reclassified as
# KNOWN_LIMITATION (reported, NOT a failure). The list is enforced both
# directions like the skip ledger: a listed file that no longer wrong-accepts
# (A2 improved to skip/reject it) is a STALE entry and FAILS the run, and a
# wrong-accept NOT on the list is still a hard MISMATCH.
#
# --- A1/A2 note: SKIP is normal, not a failure ---
# At A0 the Lean side merely echoed march's own verdict back, so ANY skip
# was unexpected (the Lean side had no fragment restriction of its own) and
# a hard failure. At A1 march-lean-check independently type-/linearity-
# checks a MODELED FRAGMENT of Core March, so `skip` (lean exit 2) is the
# expected, frequent response to any construct outside that fragment:
# roughly two-thirds of accept/*.march skips (out-of-fragment constructs:
# interfaces, actors, sessions, capabilities, refinements, derive/module
# features, ...), and at A1 every reject/*.march file skipped too (A1 only
# re-verified accepts, never modeled the reject side). At A2-reject
# march-lean-check renders its OWN accept/reject verdict on reject/*.march
# files as well (A2's inference oracle judges a modeled fragment of the
# reject corpus), so reject-side files now split into judged (match/
# mismatch, exit 0/1/4) and skipped (exit 2, out-of-fragment) just like the
# accept side. SKIP is therefore excluded from the hard-fail set below; in
# its place this script enforces a SKIP LEDGER (scripts/expected-skips.txt)
# recording exactly which accept/*.march AND reject/*.march files are
# expected to skip and why — a newly-skipping file (not on the ledger) is a
# coverage regression, and a ledger entry that no longer skips is a stale
# ledger entry, and BOTH fail the run (see the ledger-enforcement block
# after the corpus loop below). Both sides are now ledger-tracked, since
# both are shrinking coverage sets as the modeled fragment grows.
#
# Exits nonzero iff any MISMATCH, ERROR, MARCH_SELF_INCONSISTENT,
# CORPUS_VIOLATION, or SKIP-LEDGER MISMATCH occurred.
#
# Usage:
#   scripts/conformance-harness.sh [options]
#
# Options (each also settable via the like-named environment variable;
# a flag overrides the env var if both are given):
#   --march-bin PATH             (env MARCH_BIN)
#       Path to the march executable (must support --check and
#       --emit-core-ast). Required.
#   --corpus-dir PATH            (env CORPUS_DIR)
#       Path to the corpus root, i.e. the directory containing accept/ and
#       reject/ subdirectories of *.march files (e.g. march's
#       specs/lang/types). Required.
#   --march-lean-check-bin PATH  (env MARCH_LEAN_CHECK_BIN)
#       Path to the built march-lean-check executable (the raw binary, e.g.
#       .lake/build/bin/march-lean-check — NOT `lake exe march-lean-check`,
#       which re-triggers a build check on every invocation and is far too
#       slow over a whole corpus). Required.
#   -h, --help
#       Print this help and exit 0.
#
# Exit status:
#   0  every non-skip file MATCHed (march's --check verdict agrees with the
#      Lean re-check, march's own two flags agree with each other, AND
#      march's verdict agrees with the corpus's accept/reject placement),
#      AND the observed skip set (accept- and reject-side) ==
#      scripts/expected-skips.txt
#   1  at least one MISMATCH, ERROR, MARCH_SELF_INCONSISTENT,
#      CORPUS_VIOLATION, or SKIP-LEDGER MISMATCH was recorded (see the
#      printed summary for which)
#
# Dependencies: bash, standard Unix tools (find, mktemp, wc), and jq (used
# to pull the "verdict" field out of the --emit-core-ast JSON for the
# self-consistency check; present by default on GitHub Actions'
# ubuntu-latest runners).

set -u

print_help() {
    # Print this file's header comment (everything up to the first blank
    # line after "Dependencies:") as the usage text.
    sed -n '2,/^set -u/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'
}

march_bin="${MARCH_BIN:-}"
corpus_dir="${CORPUS_DIR:-}"
lean_check_bin="${MARCH_LEAN_CHECK_BIN:-}"

while [ $# -gt 0 ]; do
    case "$1" in
        --march-bin)
            march_bin="$2"; shift 2 ;;
        --march-bin=*)
            march_bin="${1#--march-bin=}"; shift ;;
        --corpus-dir)
            corpus_dir="$2"; shift 2 ;;
        --corpus-dir=*)
            corpus_dir="${1#--corpus-dir=}"; shift ;;
        --march-lean-check-bin)
            lean_check_bin="$2"; shift 2 ;;
        --march-lean-check-bin=*)
            lean_check_bin="${1#--march-lean-check-bin=}"; shift ;;
        -h|--help)
            print_help; exit 0 ;;
        *)
            echo "unknown argument: $1" >&2
            echo "run with --help for usage" >&2
            exit 1 ;;
    esac
done

if [ -z "$march_bin" ] || [ -z "$corpus_dir" ] || [ -z "$lean_check_bin" ]; then
    echo "error: MARCH_BIN, CORPUS_DIR, and MARCH_LEAN_CHECK_BIN must all be set" >&2
    echo "       (via --march-bin/--corpus-dir/--march-lean-check-bin flags or env vars)" >&2
    echo >&2
    print_help >&2
    exit 1
fi

if [ ! -x "$march_bin" ]; then
    echo "error: march binary not found or not executable: $march_bin" >&2
    exit 1
fi
if [ ! -x "$lean_check_bin" ]; then
    echo "error: march-lean-check binary not found or not executable: $lean_check_bin" >&2
    exit 1
fi
if [ ! -d "$corpus_dir/accept" ] || [ ! -d "$corpus_dir/reject" ]; then
    echo "error: CORPUS_DIR must contain accept/ and reject/ subdirectories: $corpus_dir" >&2
    exit 1
fi
if ! command -v jq >/dev/null 2>&1; then
    echo "error: jq is required (used to read the \"verdict\" field out of --emit-core-ast JSON)" >&2
    exit 1
fi

total=0
match_count=0
mismatch_files=""
error_files=""
skip_files=""
accept_skip_paths=""
observed_skip_paths=""
reject_skip_n=0
self_inconsistent_files=""
corpus_violation_files=""
known_limitation_files=""
observed_known_limitations=""

# --- known-limitations allowlist (A2-reject) ---
# Reject-corpus files march rejects for a reason ERASED from the Core AST A2
# checks (e.g. a construct desugared away before --emit-core-ast), so A2
# independently accepts them. Listed files are reclassified from MISMATCH to
# KNOWN_LIMITATION below. Enforced both directions after the loop (a stale
# entry — one that no longer wrong-accepts — fails the run).
known_limitations_file="$(cd "$(dirname "$0")/.." && pwd)/scripts/known-limitations.txt"
if [ -f "$known_limitations_file" ]; then
    known_limitations_set="$(sed 's/#.*//; s/[[:space:]]*$//; /^$/d' "$known_limitations_file" | sort -u)"
else
    known_limitations_set=""
fi

json_tmp="$(mktemp)"
trap 'rm -f "$json_tmp"' EXIT

for f in "$corpus_dir"/accept/*.march "$corpus_dir"/reject/*.march; do
    [ -e "$f" ] || continue
    total=$((total + 1))

    # expected_verdict comes solely from the file's parent directory name —
    # the corpus's own naming convention (accept/ vs reject/) — independent
    # of anything march or Lean report.
    parent_dir="$(basename "$(dirname "$f")")"
    case "$parent_dir" in
        accept) expected_verdict="accept" ;;
        reject) expected_verdict="reject" ;;
        *) expected_verdict="unknown" ;;
    esac
    rel_path="$parent_dir/$(basename "$f")"

    if "$march_bin" --check "$f" >/dev/null 2>&1; then
        march_verdict="accept"
    else
        march_verdict="reject"
    fi

    "$march_bin" --emit-core-ast "$f" >"$json_tmp" 2>/dev/null
    emit_exit=$?

    if [ ! -s "$json_tmp" ]; then
        echo "  [ERROR] $f  (--emit-core-ast produced zero bytes; march exit=$emit_exit)" >&2
        error_files="$error_files$f (empty --emit-core-ast output, march exit=$emit_exit)"$'\n'
        continue
    fi

    "$lean_check_bin" <"$json_tmp"
    lean_exit=$?
    case "$lean_exit" in
        0) lean_verdict="accept" ;;
        1) lean_verdict="reject" ;;
        2) lean_verdict="skip" ;;
        3) lean_verdict="error" ;;
        4) lean_verdict="types_differ" ;;
        *) lean_verdict="error" ;;  # defensive: unexpected exit code treated as error
    esac

    json_verdict="$(jq -r '.verdict // "MISSING"' "$json_tmp" 2>/dev/null)"
    self_consistent=1
    if [ "$json_verdict" != "$march_verdict" ]; then
        self_consistent=0
        self_inconsistent_files="$self_inconsistent_files$f (--check=$march_verdict, --emit-core-ast verdict field=$json_verdict)"$'\n'
    fi

    # Corpus-placement check: does march's own --check verdict match what
    # the file's directory (accept/ vs reject/) says it SHOULD be? This is
    # independent of whether Lean agrees with march — it catches march
    # regressing (or an external dependency like z3 silently disabling a
    # class of checks) in a way that Lean, which at A0 merely echoes
    # march's verdict, would rubber-stamp as a MATCH.
    corpus_ok=1
    if [ "$expected_verdict" = "unknown" ]; then
        corpus_ok=0
        corpus_violation_files="$corpus_violation_files$f (could not determine expected verdict from parent directory)"$'\n'
    elif [ "$march_verdict" != "$expected_verdict" ]; then
        corpus_ok=0
        corpus_violation_files="$corpus_violation_files$f (march=$march_verdict, expected=$expected_verdict per corpus directory)"$'\n'
    fi

    if [ "$lean_verdict" = "error" ]; then
        error_files="$error_files$f (lean_verdict=error, march_verdict=$march_verdict)"$'\n'
    elif [ "$lean_verdict" = "skip" ]; then
        # SKIP is expected at A1/A2 (see the header comment): a known subset
        # of accept/ and reject/ files skip because they use a construct
        # outside the modeled fragment. Record it for the summary and for
        # the skip-ledger comparison below — both sides are now
        # ledger-tracked (see the ledger-enforcement block after the loop).
        skip_files="$skip_files$f (lean_verdict=skip, march_verdict=$march_verdict)"$'\n'
        observed_skip_paths="$observed_skip_paths$rel_path"$'\n'
        if [ "$parent_dir" = "accept" ]; then
            accept_skip_paths="$accept_skip_paths$rel_path"$'\n'
        else
            reject_skip_n=$((reject_skip_n + 1))
        fi
    elif [ "$march_verdict" = "reject" ] && { [ "$lean_verdict" = "accept" ] || [ "$lean_verdict" = "types_differ" ]; } \
         && printf '%s\n' "$known_limitations_set" | grep -Fxq "$rel_path"; then
        # A2 did not reject a march-reject (it accepted, or accepted-but-types-
        # differ), AND this file is on the known-limitations allowlist: march
        # rejects for a reason erased from the Core AST A2 checks. Reclassify
        # from MISMATCH to KNOWN_LIMITATION — reported, but not a failure. The
        # allowlist is enforced both directions after the loop (a listed file
        # that no longer wrong-accepts is a stale entry and fails).
        known_limitation_files="$known_limitation_files$f (march=reject, lean=$lean_verdict; on known-limitations allowlist)"$'\n'
        observed_known_limitations="$observed_known_limitations$rel_path"$'\n'
    elif [ "$lean_verdict" = "types_differ" ]; then
        mismatch_files="$mismatch_files$f (A2 accepts but per-node types differ from resolved_ty; march=$march_verdict)"$'\n'
    elif [ "$march_verdict" != "$lean_verdict" ]; then
        mismatch_files="$mismatch_files$f (march=$march_verdict, lean=$lean_verdict)"$'\n'
    else
        if [ "$self_consistent" -eq 1 ] && [ "$corpus_ok" -eq 1 ]; then
            match_count=$((match_count + 1))
        fi
        # else: march_verdict == lean_verdict, but either march's own two
        # flags disagree with each other (MARCH_SELF_INCONSISTENT, recorded
        # above) or both march and lean agree yet disagree with the
        # corpus's accept/reject placement (CORPUS_VIOLATION, recorded
        # above); either way this is intentionally excluded from
        # match_count.
    fi
done

mismatch_n=$(printf '%s' "$mismatch_files" | grep -c . || true)
error_n=$(printf '%s' "$error_files" | grep -c . || true)
known_limitation_n=$(printf '%s' "$known_limitation_files" | grep -c . || true)
skip_n=$(printf '%s' "$skip_files" | grep -c . || true)
accept_skip_n=$(printf '%s' "$accept_skip_paths" | grep -c . || true)
self_inconsistent_n=$(printf '%s' "$self_inconsistent_files" | grep -c . || true)
corpus_violation_n=$(printf '%s' "$corpus_violation_files" | grep -c . || true)

# --- skip-ledger enforcement (A1/A2) ---
# Compare the OBSERVED skip set — BOTH accept/ and reject/ sides — against
# the checked-in ledger (scripts/expected-skips.txt, paths only, `# reason`
# comments and blank lines stripped). Any difference — either direction —
# fails the run:
#   - a file skipping that ISN'T on the ledger is a newly-skipping file,
#     i.e. a coverage regression (the fragment shrank, or a decode/check
#     bug started bailing out on something it used to handle);
#   - a ledger entry that is NOT observed skipping is a stale ledger entry
#     (the fragment widened and this file is now judged — update the
#     ledger to reflect the improved coverage, don't leave it stale).
ledger_fail=0
expected_ledger="$(cd "$(dirname "$0")/.." && pwd)/scripts/expected-skips.txt"
if [ ! -f "$expected_ledger" ]; then
    echo "error: skip ledger not found: $expected_ledger" >&2
    ledger_fail=1
    ledger_diff=""
else
    observed_skips_sorted="$(printf '%s\n' "$observed_skip_paths" | sed '/^$/d' | sort -u)"
    expected_skips_sorted="$(sed 's/#.*//; s/[[:space:]]*$//; /^$/d' "$expected_ledger" | sort -u)"
    if [ "$observed_skips_sorted" != "$expected_skips_sorted" ]; then
        ledger_fail=1
        ledger_diff="$(diff <(printf '%s\n' "$expected_skips_sorted") <(printf '%s\n' "$observed_skips_sorted") || true)"
    else
        ledger_diff=""
    fi
fi

# --- known-limitations enforcement (both directions) ---
# A listed file that was NOT observed wrong-accepting is STALE: A2 now skips or
# rejects it (an improvement), so the entry must be removed. This mirrors the
# skip ledger's stale-entry check and keeps the allowlist strictly shrinking.
known_limitations_fail=0
if [ -n "$known_limitations_set" ]; then
    observed_known_sorted="$(printf '%s\n' "$observed_known_limitations" | sed '/^$/d' | sort -u)"
    known_stale="$(comm -23 <(printf '%s\n' "$known_limitations_set") <(printf '%s\n' "$observed_known_sorted"))"
    if [ -n "$known_stale" ]; then
        known_limitations_fail=1
    fi
else
    known_stale=""
fi

echo "==================================================================="
echo "Conformance harness summary"
echo "==================================================================="
echo "corpus:            $corpus_dir"
echo "march binary:      $march_bin"
echo "march-lean-check:  $lean_check_bin"
echo "-------------------------------------------------------------------"
echo "total files:              $total"
echo "MATCH:                    $match_count"
echo "MISMATCH:                 $mismatch_n"
echo "ERROR:                    $error_n"
echo "SKIP:                     $skip_n  (accept-side: $accept_skip_n, reject-side: $reject_skip_n)"
echo "KNOWN_LIMITATION:         $known_limitation_n"
echo "MARCH_SELF_INCONSISTENT:  $self_inconsistent_n"
echo "CORPUS_VIOLATION:         $corpus_violation_n"
echo "SKIP-LEDGER:              $([ "$ledger_fail" -eq 0 ] && echo OK || echo MISMATCH)"
echo "KNOWN-LIMITATIONS:        $([ "$known_limitations_fail" -eq 0 ] && echo OK || echo STALE)"
echo "-------------------------------------------------------------------"

if [ "$mismatch_n" -gt 0 ]; then
    echo "MISMATCH files:"
    printf '%s' "$mismatch_files" | sed '/^$/d;s/^/  - /'
fi
if [ "$error_n" -gt 0 ]; then
    echo "ERROR files:"
    printf '%s' "$error_files" | sed '/^$/d;s/^/  - /'
fi
if [ "$skip_n" -gt 0 ]; then
    echo "SKIP files (expected at A1/A2 — out-of-fragment; see scripts/expected-skips.txt for the accept- and reject-side ledger):"
    printf '%s' "$skip_files" | sed '/^$/d;s/^/  - /'
fi
if [ "$ledger_fail" -ne 0 ]; then
    echo "SKIP-LEDGER MISMATCH — observed skips (accept- and reject-side) differ from scripts/expected-skips.txt:"
    echo "  (lines prefixed '<' are in the ledger but NOT observed skipping — stale ledger entry;"
    echo "   lines prefixed '>' are observed skipping but NOT in the ledger — coverage regression)"
    printf '%s\n' "$ledger_diff" | sed '/^$/d;s/^/  /'
fi
if [ "$known_limitation_n" -gt 0 ]; then
    echo "KNOWN_LIMITATION files (march=reject, but the rejection reason is invisible to the Core AST A2 checks — see scripts/known-limitations.txt; reported, NOT a failure):"
    printf '%s' "$known_limitation_files" | sed '/^$/d;s/^/  - /'
fi
if [ "$known_limitations_fail" -ne 0 ]; then
    echo "KNOWN-LIMITATIONS STALE — these files are on scripts/known-limitations.txt but no longer wrong-accept (A2 now skips or rejects them). Remove them from the allowlist:"
    printf '%s\n' "$known_stale" | sed '/^$/d;s/^/  - /'
fi
if [ "$self_inconsistent_n" -gt 0 ]; then
    echo "MARCH_SELF_INCONSISTENT files (--check disagrees with --emit-core-ast's own verdict field):"
    printf '%s' "$self_inconsistent_files" | sed '/^$/d;s/^/  - /'
fi
if [ "$corpus_violation_n" -gt 0 ]; then
    echo "CORPUS_VIOLATION files (march's own --check verdict disagrees with the accept/reject directory it lives in):"
    printf '%s' "$corpus_violation_files" | sed '/^$/d;s/^/  - /'
fi

echo "==================================================================="

if [ "$mismatch_n" -gt 0 ] || [ "$error_n" -gt 0 ] || [ "$self_inconsistent_n" -gt 0 ] || [ "$corpus_violation_n" -gt 0 ] || [ "$ledger_fail" -ne 0 ] || [ "$known_limitations_fail" -ne 0 ]; then
    echo "RESULT: FAIL"
    exit 1
else
    echo "RESULT: PASS"
    exit 0
fi
