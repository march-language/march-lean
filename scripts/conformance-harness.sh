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
#
# and reports MATCH / MISMATCH / SKIP / ERROR / MARCH_SELF_INCONSISTENT
# counts, plus the filenames in every non-MATCH category. Exits nonzero iff
# any MISMATCH, ERROR, SKIP, or MARCH_SELF_INCONSISTENT occurred.
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
#   0  every file MATCHed (march's --check verdict agrees with the Lean
#      re-check, and march's own two flags agree with each other)
#   1  at least one MISMATCH, ERROR, SKIP, or MARCH_SELF_INCONSISTENT was
#      recorded (see the printed summary for which)
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
self_inconsistent_files=""

json_tmp="$(mktemp)"
trap 'rm -f "$json_tmp"' EXIT

for f in "$corpus_dir"/accept/*.march "$corpus_dir"/reject/*.march; do
    [ -e "$f" ] || continue
    total=$((total + 1))

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
        *) lean_verdict="error" ;;  # defensive: unexpected exit code treated as error
    esac

    json_verdict="$(jq -r '.verdict // "MISSING"' "$json_tmp" 2>/dev/null)"
    self_consistent=1
    if [ "$json_verdict" != "$march_verdict" ]; then
        self_consistent=0
        self_inconsistent_files="$self_inconsistent_files$f (--check=$march_verdict, --emit-core-ast verdict field=$json_verdict)"$'\n'
    fi

    if [ "$lean_verdict" = "error" ]; then
        error_files="$error_files$f (lean_verdict=error, march_verdict=$march_verdict)"$'\n'
    elif [ "$lean_verdict" = "skip" ]; then
        skip_files="$skip_files$f (lean_verdict=skip, march_verdict=$march_verdict; UNEXPECTED at A0)"$'\n'
    elif [ "$march_verdict" != "$lean_verdict" ]; then
        mismatch_files="$mismatch_files$f (march=$march_verdict, lean=$lean_verdict)"$'\n'
    else
        if [ "$self_consistent" -eq 1 ]; then
            match_count=$((match_count + 1))
        fi
        # else: verdicts agree pairwise but march's own two flags disagree
        # with each other; already recorded above as
        # MARCH_SELF_INCONSISTENT and intentionally excluded from
        # match_count.
    fi
done

mismatch_n=$(printf '%s' "$mismatch_files" | grep -c . || true)
error_n=$(printf '%s' "$error_files" | grep -c . || true)
skip_n=$(printf '%s' "$skip_files" | grep -c . || true)
self_inconsistent_n=$(printf '%s' "$self_inconsistent_files" | grep -c . || true)

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
echo "SKIP:                     $skip_n"
echo "MARCH_SELF_INCONSISTENT:  $self_inconsistent_n"
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
    echo "SKIP files (unexpected at A0):"
    printf '%s' "$skip_files" | sed '/^$/d;s/^/  - /'
fi
if [ "$self_inconsistent_n" -gt 0 ]; then
    echo "MARCH_SELF_INCONSISTENT files (--check disagrees with --emit-core-ast's own verdict field):"
    printf '%s' "$self_inconsistent_files" | sed '/^$/d;s/^/  - /'
fi

echo "==================================================================="

if [ "$mismatch_n" -gt 0 ] || [ "$error_n" -gt 0 ] || [ "$skip_n" -gt 0 ] || [ "$self_inconsistent_n" -gt 0 ]; then
    echo "RESULT: FAIL"
    exit 1
else
    echo "RESULT: PASS"
    exit 0
fi
