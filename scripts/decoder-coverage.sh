#!/usr/bin/env bash
#
# decoder-coverage.sh — diff "AST node kinds march actually emits" against
# "AST node kinds MarchLean/Elab.lean actually decodes", and fail on a gap.
#
# --- WHY THIS EXISTS ---
# Two of the worst defects in this project were the same mechanical
# oversight: march emits a node kind, the decoder has no arm for it, and the
# node silently degrades.
#
#   ELet    `decodeTerm` had no arm, so a `do` block whose sole statement is
#           a `let` DISCARDED the binding's right-hand side, blinding all
#           four CapCheck capability walks at once.
#   EAnnot  no arm, and `Desugar` synthesizes one for every `app` block
#           (desugar.ml:929), so a `cap` violation in an app body was
#           invisible.
#
# Both cost expensive hand-probing to find. Both were rationalised away by
# reasoning from march's GRAMMAR — "no parser production reaches this kind".
# That reasoning is unsound, and this script exists to make it unnecessary:
# `Desugar` sits between the parser and the emitter and manufactures nodes
# with no surface syntax, so "no parser production reaches X" does NOT imply
# "X is not emitted". The only sound test is to look at what comes out of
# --emit-core-ast.
#
# --- HOW THE HANDLED SET IS DERIVED, AND WHY ---
# The emitted set is easy: sweep the corpora, collect every `"kind"` string.
# The handled set is the interesting half, and there are three ways to get
# it, two of which do not work:
#
#   1. Regex the `| "EFoo" =>` arms out of Elab.lean. Fragile, and it rots
#      the first time an arm is written differently.
#   2. Hand-maintain a `handledKinds` list next to the decoder and print it.
#      This LOOKS authoritative and is not: deleting the `"ELet"` arm would
#      not change the list, so the check would keep passing while the exact
#      historical bug was reintroduced. A parallel declaration can only ever
#      restate the author's belief about the code.
#   3. Ask the decoder itself. That is what this does.
#
# `march-lean-check --kind-coverage` (MarchLean/KindCoverage.lean) reads kind
# names on stdin and, for each, RUNS the real decoder on a synthetic node
# bearing that kind, at every `kind`-dispatching site in Elab.lean. It probes
# each site twice — once with the kind under test, once with a sentinel
# string march can never emit — and compares the results, which separates
# "this kind has its own arm" from "this kind is indistinguishable from one
# that does not exist". The answer therefore comes from the live match arms
# and cannot drift from them; removing an arm changes it immediately. That
# also means this script needs no knowledge of Lean syntax.
#
# It reports one of five categories per kind:
#
#   modeled       an arm exists and yields a real modelled constructor
#   opaque        an arm exists and yields `Term.opaque_`: the shape is
#                 unmodelled but the child EXPRESSIONS survive, so CapCheck's
#                 walks can still find a violation nested inside
#   unsupported   an arm exists and yields an `.unsupported` sentinel:
#                 children are DISCARDED
#   fell-through  no arm at all
#   probe-error   an arm exists but demanded a field KindCoverage.lean's
#                 fixture does not supply — a stale fixture, fix it there
#
# --- WHAT COUNTS AS A FAILURE ---
# Only `modeled` passes unconditionally. `opaque`, `unsupported` and
# `fell-through` are all legitimate outcomes for genuinely unmodelled
# constructs, but a kind reaching one SILENTLY is precisely the failure mode
# above, so each must be declared in scripts/decoder-degraded-kinds.txt with
# its exact category. Enforced both directions, like the harness's ledgers:
#
#   GAP             an emitted kind degrades and is not on the allowlist.
#   CATEGORY DRIFT  a listed kind's observed category differs from the
#                   declared one. Covers both the stale direction (now
#                   `modeled` — delete the entry) and the regression
#                   direction (`opaque` -> `fell-through` — an arm was lost).
#                   This is what makes deleting the EAnnot arm detectable:
#                   EAnnot stays degraded either way, but stops being
#                   `opaque`. Keeping the three categories distinct instead
#                   of collapsing them into one "degraded" bucket is the
#                   whole reason that test fails.
#   AMBIGUOUS       a kind recognised at two dispatch sites at once. march's
#                   tags are namespaced by prefix (E/D/Pat/Lit/Ty/T/TD/C/FP/
#                   Nat/Use) and none is reused today, which is what lets
#                   this script compare bare kind strings without tracking
#                   which JSON slot each came from. This check is what keeps
#                   that from being an assumption.
#   PROBE ERROR     KindCoverage.lean's fixture is missing a field. Loud on
#                   purpose: a silently unclassifiable kind is the thing this
#                   script exists to prevent.
#
# Allowlist category validation is corpus-independent — it probes the
# decoder, not the corpus — so it holds even for a declared kind no scanned
# file emits. Those are reported separately, as information, not failures.
#
# --- SCOPE OF THE SWEEP ---
# The whole --emit-core-ast envelope is scanned EXCEPT `diagnostics`, which
# is march's own error-reporting channel (its `fix.kind` values are the
# fix-it hint tags `insert`/`replace`/`delete`, not AST nodes). Everything
# else is scanned, including envelope keys this script knows nothing about,
# so a node moving into a NEW top-level slot is still caught.
#
# This script does NOT re-check anything in Lean — it runs --emit-core-ast
# and compares two sets — so it is far cheaper than
# scripts/conformance-harness.sh and is meant to run before it.
#
# Usage:
#   scripts/decoder-coverage.sh [options]
#
# Options (each also settable via the like-named environment variable;
# a flag overrides the env var if both are given). The first four match
# scripts/conformance-harness.sh exactly, so CI can pass both the same
# corpus paths:
#   --march-bin PATH             (env MARCH_BIN)
#       Path to the march executable (must support --emit-core-ast).
#       Required.
#   --corpus-dir PATH            (env CORPUS_DIR)
#       Path to the corpus root, i.e. the directory containing accept/ and
#       reject/ subdirectories of *.march files (e.g. march's
#       specs/lang/types). Required.
#   --march-lean-check-bin PATH  (env MARCH_LEAN_CHECK_BIN)
#       Path to the built march-lean-check executable (the raw binary, e.g.
#       .lake/build/bin/march-lean-check). Required. Invoked once, with
#       --kind-coverage; it renders no verdict in that mode.
#   --lang-dir PATH              (env LANG_DIR)
#       Path to march's specs/lang root, adding the same THREE extra corpora
#       the harness takes — specs/lang/{grammar/parse,grammar/reject,golden}.
#       OPTIONAL: omit it and only --corpus-dir's accept/ + reject/ are
#       swept, but the summary then prints "EXTRA CORPORA: NOT SCANNED" so
#       the missing coverage is loud rather than silent. CI passes it.
#   --histogram                  (env HISTOGRAM=1)
#       Print the full kind -> occurrence-count table, annotated with each
#       kind's category, so a human can see what is rare versus common. A
#       kind occurring once (EAnnot did) is exactly the kind a corpus sweep
#       is likely to be the only witness for.
#   --jobs N                     (env JOBS, default 4)
#       How many march processes to run at once. --emit-core-ast costs about
#       a second of fixed startup per file regardless of file size, so the
#       sweep is entirely process-bound and parallelises linearly.
#   -h, --help
#       Print this help and exit 0.
#
# Exit status:
#   0  every emitted kind is either `modeled` or declared in
#      scripts/decoder-degraded-kinds.txt with its observed category
#   1  at least one GAP, CATEGORY DRIFT, AMBIGUOUS, PROBE ERROR, or
#      --emit-core-ast failure (see the printed summary for which)
#
# Dependencies: bash, standard Unix tools (find, mktemp, sort, xargs), and
# jq (used to walk the envelope and pull out every "kind" string; present by
# default on GitHub Actions' ubuntu-latest runners).

set -u

print_help() {
    # Print this file's header comment (everything up to the first blank
    # line after "Dependencies:") as the usage text.
    sed -n '2,/^set -u/p' "$0" | sed '$d' | sed 's/^# \{0,1\}//'
}

march_bin="${MARCH_BIN:-}"
corpus_dir="${CORPUS_DIR:-}"
lean_check_bin="${MARCH_LEAN_CHECK_BIN:-}"
lang_dir="${LANG_DIR:-}"
histogram="${HISTOGRAM:-}"
jobs="${JOBS:-4}"

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
        --lang-dir)
            lang_dir="$2"; shift 2 ;;
        --lang-dir=*)
            lang_dir="${1#--lang-dir=}"; shift ;;
        --histogram)
            histogram=1; shift ;;
        --jobs)
            jobs="$2"; shift 2 ;;
        --jobs=*)
            jobs="${1#--jobs=}"; shift ;;
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
    echo "error: jq is required (used to walk the --emit-core-ast envelope for \"kind\" strings)" >&2
    exit 1
fi
case "$jobs" in
    ''|*[!0-9]*|0) echo "error: --jobs must be a positive integer: $jobs" >&2; exit 1 ;;
esac

# Directories to sweep. Same set the conformance harness scans, and derived
# the same way, so the two are always looking at the same corpus.
scan_dirs="$corpus_dir/accept
$corpus_dir/reject"

if [ -n "$lang_dir" ]; then
    if [ ! -d "$lang_dir" ]; then
        echo "error: --lang-dir is not a directory: $lang_dir" >&2
        exit 1
    fi
    for extra in grammar/parse grammar/reject golden; do
        if [ ! -d "$lang_dir/$extra" ]; then
            echo "error: --lang-dir is missing the expected subdirectory $extra: $lang_dir" >&2
            exit 1
        fi
        scan_dirs="$scan_dirs
$lang_dir/$extra"
    done
fi

allowlist_file="$(cd "$(dirname "$0")/.." && pwd)/scripts/decoder-degraded-kinds.txt"
if [ ! -f "$allowlist_file" ]; then
    echo "error: degraded-kind allowlist not found: $allowlist_file" >&2
    exit 1
fi

work_dir="$(mktemp -d)"
trap 'rm -rf "$work_dir"' EXIT

# ---------------------------------------------------------------------------
# 1. Sweep the corpora and collect every emitted "kind" string.
# ---------------------------------------------------------------------------
# One worker per file. Each prints either `K<TAB>kind` lines (one per "kind"
# occurrence, duplicates INCLUDED so the histogram can count them) or a
# single `F<TAB>path` line if --emit-core-ast produced nothing usable.
#
# `del(.diagnostics)` drops march's error-reporting channel: its `fix.kind`
# values are fix-it hint tags (insert/replace/delete), not AST nodes. Every
# other envelope key is walked, including ones this script does not know
# about, so a node appearing in a NEW top-level slot is still collected.
file_list="$work_dir/files"
: >"$file_list"
while IFS= read -r d; do
    [ -n "$d" ] || continue
    for f in "$d"/*.march; do
        [ -e "$f" ] || continue
        printf '%s\n' "$f" >>"$file_list"
    done
done <<EOF
$scan_dirs
EOF

total_files=$(wc -l <"$file_list" | tr -d ' ')
if [ "$total_files" -eq 0 ]; then
    echo "error: no *.march files found under the scanned directories" >&2
    exit 1
fi

export MARCH_BIN_FOR_WORKER="$march_bin"
# shellcheck disable=SC2016  # the single-quoted worker body is deliberate:
# $1/$MARCH_BIN_FOR_WORKER must be expanded by the worker shell, not here.
xargs -P "$jobs" -I{} sh -c '
    out=$("$MARCH_BIN_FOR_WORKER" --emit-core-ast "$1" 2>/dev/null)
    if [ -z "$out" ]; then
        printf "F\t%s\n" "$1"
        exit 0
    fi
    printf "%s" "$out" | jq -r "del(.diagnostics) | .. | objects | select(has(\"kind\")) | .kind | \"K\t\" + ." 2>/dev/null \
        || printf "F\t%s\n" "$1"
' _ {} <"$file_list" >"$work_dir/raw"

grep '^F	' "$work_dir/raw" | cut -f2- | sort -u >"$work_dir/emit-failures"
grep '^K	' "$work_dir/raw" | cut -f2- >"$work_dir/kind-occurrences"

emit_failure_n=$(grep -c . "$work_dir/emit-failures" || true)

sort "$work_dir/kind-occurrences" | uniq -c | sort -rn -k1,1 -k2,2 >"$work_dir/histogram"
awk '{print $2}' "$work_dir/histogram" | sort -u >"$work_dir/emitted-kinds"
emitted_n=$(grep -c . "$work_dir/emitted-kinds" || true)

# ---------------------------------------------------------------------------
# 2. Read the declared degraded-kind allowlist.
# ---------------------------------------------------------------------------
# `KIND CATEGORY # reason`, comments and blank lines stripped. A malformed
# line is a hard error rather than a silently ignored one: an entry that does
# not parse is an entry that is not enforcing anything.
sed 's/#.*//; s/[[:space:]]*$//; /^[[:space:]]*$/d' "$allowlist_file" >"$work_dir/allow-raw"
if awk 'NF != 2 { print FILENAME ": malformed line: " $0 > "/dev/stderr"; bad=1 } END { exit bad?1:0 }' \
        "$work_dir/allow-raw"; then
    :
else
    echo "error: $allowlist_file has malformed entries (expected: KIND CATEGORY  # reason)" >&2
    exit 1
fi
awk '{print $1 "\t" $2}' "$work_dir/allow-raw" | sort -u >"$work_dir/allowlist"
awk -F'\t' '{print $1}' "$work_dir/allowlist" | sort -u >"$work_dir/allowlist-kinds"
allow_n=$(grep -c . "$work_dir/allowlist-kinds" || true)

if [ "$(wc -l <"$work_dir/allowlist" | tr -d ' ')" -ne "$allow_n" ]; then
    echo "error: $allowlist_file declares the same kind twice with different categories" >&2
    exit 1
fi

# ---------------------------------------------------------------------------
# 3. Ask the decoder what it does with each kind.
# ---------------------------------------------------------------------------
# Union of (emitted, declared) so both the coverage check and the
# corpus-independent allowlist validation have an answer to compare against.
sort -u "$work_dir/emitted-kinds" "$work_dir/allowlist-kinds" >"$work_dir/query"
if ! "$lean_check_bin" --kind-coverage <"$work_dir/query" >"$work_dir/coverage"; then
    echo "error: '$lean_check_bin --kind-coverage' failed" >&2
    exit 1
fi
# KIND<TAB>CATEGORY<TAB>SITES
awk -F'\t' '{print $1 "\t" $2}' "$work_dir/coverage" | sort -u >"$work_dir/observed"

lookup_category() {
    awk -F'\t' -v k="$1" '$1 == k { print $2; found=1 } END { if (!found) print "MISSING" }' \
        "$work_dir/observed"
}

# ---------------------------------------------------------------------------
# 4. Apply the policy.
# ---------------------------------------------------------------------------
gap_lines=""
drift_lines=""
ambiguous_lines=""
probe_error_lines=""
unemitted_lines=""
modeled_n=0
degraded_n=0

# PROBE ERROR / AMBIGUOUS: properties of the decoder itself, checked over
# every queried kind rather than only the emitted ones.
while IFS=$'\t' read -r kind cat sites; do
    [ -n "$kind" ] || continue
    if [ "$cat" = "probe-error" ]; then
        probe_error_lines="$probe_error_lines$kind (an arm exists but MarchLean/KindCoverage.lean's fixture lacks a field it reads)"$'\n'
    fi
    case "$sites" in
        *,*)
            ambiguous_lines="$ambiguous_lines$kind (recognised at several dispatch sites: $sites)"$'\n' ;;
    esac
done <"$work_dir/coverage"

# CATEGORY DRIFT: every declared entry must still say what it claims to say.
# Corpus-independent — this probes the decoder, not the corpus.
while IFS=$'\t' read -r kind declared; do
    [ -n "$kind" ] || continue
    observed="$(lookup_category "$kind")"
    if [ "$observed" != "$declared" ]; then
        drift_lines="$drift_lines$kind (declared '$declared', decoder now reports '$observed')"$'\n'
    fi
    if ! grep -Fxq "$kind" "$work_dir/emitted-kinds"; then
        unemitted_lines="$unemitted_lines$kind (declared '$declared'; not emitted by the scanned corpora)"$'\n'
    fi
done <"$work_dir/allowlist"

# GAP: an emitted kind that degrades and was never declared.
while IFS= read -r kind; do
    [ -n "$kind" ] || continue
    observed="$(lookup_category "$kind")"
    if [ "$observed" = "modeled" ]; then
        modeled_n=$((modeled_n + 1))
        continue
    fi
    degraded_n=$((degraded_n + 1))
    if ! grep -Fxq "$kind" "$work_dir/allowlist-kinds"; then
        count=$(awk -v k="$kind" '$2 == k { print $1 }' "$work_dir/histogram")
        gap_lines="$gap_lines$kind (decoder reports '$observed'; $count occurrence(s); not declared in scripts/decoder-degraded-kinds.txt)"$'\n'
    fi
done <"$work_dir/emitted-kinds"

gap_n=$(printf '%s' "$gap_lines" | grep -c . || true)
drift_n=$(printf '%s' "$drift_lines" | grep -c . || true)
ambiguous_n=$(printf '%s' "$ambiguous_lines" | grep -c . || true)
probe_error_n=$(printf '%s' "$probe_error_lines" | grep -c . || true)
unemitted_n=$(printf '%s' "$unemitted_lines" | grep -c . || true)

# ---------------------------------------------------------------------------
# 5. Report.
# ---------------------------------------------------------------------------
echo "==================================================================="
echo "Decoder coverage summary"
echo "==================================================================="
echo "corpus:            $corpus_dir"
if [ -n "$lang_dir" ]; then
    echo "extra corpora:     $lang_dir/{grammar/parse,grammar/reject,golden}"
else
    echo "extra corpora:     NOT SCANNED (--lang-dir not given)"
fi
echo "march binary:      $march_bin"
echo "march-lean-check:  $lean_check_bin"
echo "allowlist:         $allowlist_file"
echo "-------------------------------------------------------------------"
echo "files swept:              $total_files"
echo "distinct kinds emitted:   $emitted_n"
echo "  modeled:                $modeled_n"
echo "  degraded (declared):    $((degraded_n - gap_n))"
echo "  degraded (UNDECLARED):  $gap_n"
echo "allowlist entries:        $allow_n  (not emitted here: $unemitted_n)"
echo "CATEGORY DRIFT:           $drift_n"
echo "AMBIGUOUS KINDS:          $ambiguous_n"
echo "PROBE ERRORS:             $probe_error_n"
echo "EMIT FAILURES:            $emit_failure_n"
echo "-------------------------------------------------------------------"

if [ "$gap_n" -gt 0 ]; then
    echo "GAP — emitted kinds the decoder degrades, with nothing declaring that:"
    echo "  (this is the ELet/EAnnot failure mode. Either add a decoder arm in"
    echo "   MarchLean/Elab.lean, or declare the kind — with a reason — in"
    echo "   scripts/decoder-degraded-kinds.txt.)"
    printf '%s' "$gap_lines" | sed '/^$/d;s/^/  - /'
fi
if [ "$drift_n" -gt 0 ]; then
    echo "CATEGORY DRIFT — declared category no longer matches the decoder:"
    echo "  (observed 'modeled' means the entry is STALE: delete it. Any other"
    echo "   change — e.g. 'opaque' becoming 'fell-through' — means a decoder"
    echo "   arm was LOST.)"
    printf '%s' "$drift_lines" | sed '/^$/d;s/^/  - /'
fi
if [ "$ambiguous_n" -gt 0 ]; then
    echo "AMBIGUOUS — kinds recognised at more than one dispatch site:"
    echo "  (this script compares bare kind strings, which is only sound while"
    echo "   march's tag namespaces stay disjoint. They no longer are.)"
    printf '%s' "$ambiguous_lines" | sed '/^$/d;s/^/  - /'
fi
if [ "$probe_error_n" -gt 0 ]; then
    echo "PROBE ERRORS — MarchLean/KindCoverage.lean's fixtures are stale:"
    echo "  (an arm reads a field no fixture supplies, so the kind cannot be"
    echo "   classified. Add the field to the relevant Site.)"
    printf '%s' "$probe_error_lines" | sed '/^$/d;s/^/  - /'
fi
if [ "$emit_failure_n" -gt 0 ]; then
    echo "EMIT FAILURES — --emit-core-ast produced nothing for these files:"
    echo "  (they contributed no kinds, so the sweep is incomplete.)"
    sed 's/^/  - /' "$work_dir/emit-failures"
fi
if [ "$unemitted_n" -gt 0 ]; then
    echo "Declared but not emitted by the scanned corpora (informational, not a failure —"
    echo "the allowlist is validated against the decoder, not against the corpus):"
    printf '%s' "$unemitted_lines" | sed '/^$/d;s/^/  - /'
fi

if [ -n "$histogram" ]; then
    echo "-------------------------------------------------------------------"
    echo "Kind histogram (occurrences across all swept files, most common first):"
    printf '  %8s  %-22s %-14s %s\n' COUNT KIND CATEGORY SITES
    while read -r count kind; do
        [ -n "$kind" ] || continue
        line=$(awk -F'\t' -v k="$kind" '$1 == k { print $2 "\t" $3 }' "$work_dir/coverage")
        cat_of="${line%%	*}"
        sites_of="${line#*	}"
        printf '  %8s  %-22s %-14s %s\n' "$count" "$kind" "$cat_of" "$sites_of"
    done <"$work_dir/histogram"
fi

echo "==================================================================="

if [ "$gap_n" -gt 0 ] || [ "$drift_n" -gt 0 ] || [ "$ambiguous_n" -gt 0 ] \
   || [ "$probe_error_n" -gt 0 ] || [ "$emit_failure_n" -gt 0 ]; then
    echo "RESULT: FAIL"
    exit 1
else
    echo "RESULT: PASS"
    exit 0
fi
