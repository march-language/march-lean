#!/usr/bin/env bash
#
# tailcall-probes.sh — hand-built probes for march's Pass 3 tail-call
# enforcement (`enforce_tail_calls_in_decls`, march typecheck.ml:11367).
#
# The conformance corpus finds nothing here: it contains no unbounded non-tail
# recursion, so a green harness run is no evidence at all that this pass works.
# These probes ARE the instrument. Each one is a hand-built program whose march
# verdict was confirmed by hand, and each `tailcall` probe is additionally
# confirmed to produce march's *tail-call* diagnostic rather than a parse or
# unbound-name error — the failure mode that silently makes a probe vacuous.
#
# Contract asserted per probe:
#
#   class=tailcall   march MUST exit 1, its output MUST contain
#                    "not in tail position", and march-lean-check MUST exit 1.
#                    These are the false-accept class this pass exists to close.
#
#   class=clean      march MUST exit 0, and march-lean-check MUST NOT exit 1.
#                    These are the false-REJECT detectors — each is a shape
#                    march deliberately allows (structural recursion, a tail
#                    position, a shadowed name, an opted-out fn, a nested mod).
#                    A `clean` probe going red means we reject what march
#                    accepts, which is the one outcome that is never acceptable.
#
# Usage:
#   scripts/tailcall-probes.sh --march-bin PATH --march-lean-check-bin PATH

# NO `pipefail`. march exits 1 on `--emit-core-ast` for a file it rejects, so a
# pipefail'd `march --emit-core-ast | march-lean-check` reports march's 1 even
# when march-lean-check exited 0 — which silently turns every false accept in
# the `tailcall` class into a spurious "ok". The emit step's own exit code is
# irrelevant here (it emits a full module either way); only the checker's
# matters, and a bare pipeline yields exactly that.
set -u

march_bin=""
lean_bin=""
while [ $# -gt 0 ]; do
  case "$1" in
    --march-bin)            march_bin="$2"; shift 2 ;;
    --march-lean-check-bin) lean_bin="$2";  shift 2 ;;
    *) echo "unknown argument: $1" >&2; exit 2 ;;
  esac
done
: "${march_bin:=${MARCH_BIN:-}}"
: "${lean_bin:=${MARCH_LEAN_CHECK_BIN:-}}"
if [ -z "$march_bin" ] || [ -z "$lean_bin" ]; then
  echo "error: --march-bin and --march-lean-check-bin are both required" >&2
  exit 2
fi

probe_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")/tailcall-probes" && pwd)"

# name              class     what it pins down
PROBES=(
  "loopy            tailcall  self-recursive \`loopy(n + 1) + 1\` — the reported false accept"
  "go               tailcall  same shape under a name that collides with prelude's local \`go\`"
  "mutual           tailcall  walk/helper SCC — needs Tarjan, not just a self-call test"
  "nested_mod_flat  tailcall  a top-level module's fn IS checked (control for nested_mod)"

  "fact             clean     \`fact(n - 1) * n\` — structural, march warns and allows"
  "match_structural clean     recursion on match-bound sub-components of a param"
  "nullary_ctor     clean     a nullary constructor argument is structurally minimal"
  "tail_ok          clean     plain tail recursion with an accumulator"
  "cond_tail        clean     a \`match do\` (ECond) arm body IS tail position"
  "letq_tail        clean     a \`let?\` (ELetQ) continuation IS tail position"
  "attr             clean     \`@[no_warn_recursion]\` opts a fn out entirely"
  "attr_mutual      clean     \`@[no_warn_recursion]\` on both halves of an SCC"
  "lambda_body      clean     chk: march does not descend into a lambda at all"
  "lambda_edge      clean     calls: a lambda body must not forge a call-graph edge"
  "letfn_edge       clean     calls: an inner \`fn\` body must not forge a call-graph edge"
  "nested_mod       clean     march's Pass 3 does NOT reach inside a nested \`mod\`"

  # Shadowing is enforced at TWO sites, and a probe only ever exercises one of
  # them. The `shadow_*` trio pins the walk (`chk`): the offending call is the
  # shadowed one, so retiring the name inside the walk is what averts the
  # error. The `shadow_edge_*` trio pins the call graph (`calls`): the shadowed
  # binder is the ONLY thing that would forge the SCC edge, and the offending
  # non-tail call sits in the OTHER function, where no shadowing is in scope to
  # rescue it. Mutation testing confirmed the first trio alone leaves `calls`
  # unguarded.
  "shadow_let       clean     chk: a local \`let\` retires the name for its block siblings"
  "shadow_letfn     clean     chk: a local \`fn\` retires the name for its block siblings"
  "shadow_match     clean     chk: a match arm's pattern retires the name in that arm"
  "shadow_edge_let  clean     calls: a local \`let\` must not forge a call-graph edge"
  "shadow_edge_letfn clean    calls: a local \`fn\` must not forge a call-graph edge"
  "shadow_edge_match clean    calls: a match arm's pattern must not forge an edge"
)

pass=0; fail=0
printf '%-18s %-9s %-7s %-6s %s\n' PROBE CLASS MARCH LEAN RESULT
printf '%s\n' "-------------------------------------------------------------"

for entry in "${PROBES[@]}"; do
  read -r name class _rest <<<"$entry"
  f="$probe_dir/$name.march"
  if [ ! -f "$f" ]; then
    printf '%-18s %-9s %-7s %-6s %s\n' "$name" "$class" "-" "-" "FAIL (missing $f)"
    fail=$((fail + 1)); continue
  fi

  march_out="$("$march_bin" --check "$f" 2>&1)"; march_exit=$?
  lean_out="$("$march_bin" --emit-core-ast "$f" 2>/dev/null | "$lean_bin" 2>&1)"; lean_exit=$?

  why=""
  case "$class" in
    tailcall)
      if [ "$march_exit" -ne 1 ]; then
        why="march exit $march_exit, expected 1 — probe has rotted"
      elif ! printf '%s' "$march_out" | grep -q 'not in tail position'; then
        why="march rejected for some OTHER reason (parse? unbound name?) — probe is vacuous"
      elif [ "$lean_exit" -ne 1 ]; then
        why="FALSE ACCEPT: lean exit $lean_exit, expected 1 — ${lean_out:-(no message)}"
      fi
      ;;
    clean)
      if [ "$march_exit" -ne 0 ]; then
        why="march exit $march_exit, expected 0 — probe has rotted"
      elif [ "$lean_exit" -eq 1 ]; then
        why="FALSE REJECT: lean rejected what march accepts — ${lean_out:-(no message)}"
      fi
      ;;
    *) why="unknown class '$class'" ;;
  esac

  if [ -z "$why" ]; then
    printf '%-18s %-9s %-7s %-6s %s\n' "$name" "$class" "$march_exit" "$lean_exit" "ok"
    pass=$((pass + 1))
  else
    printf '%-18s %-9s %-7s %-6s %s\n' "$name" "$class" "$march_exit" "$lean_exit" "FAIL"
    printf '    %s\n' "$why"
    fail=$((fail + 1))
  fi
done

printf '%s\n' "-------------------------------------------------------------"
printf 'pass=%d fail=%d\n' "$pass" "$fail"
[ "$fail" -eq 0 ] || exit 1
