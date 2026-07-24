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
