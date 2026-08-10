# Tail-call enforcement (march Pass 3) — Design

**Status:** approved, pre-implementation.
**Repo:** `march-lean`, on a branch off `main`. The march emitter is **unchanged**.
**march reference (read-only):** `/Users/80197052/code/march/.claude/worktrees/lean-repin-baseline/lib/typecheck/typecheck.ml`

---

## 1. The defect

`march-lean-check` does not model march's tail-call enforcement pass at all. It is a
live FALSE ACCEPT class: we exit `0` on programs march rejects with an ERROR.

march's Pass 3 (`enforce_tail_calls_in_decls`, invoked at `typecheck.ml:11367` for the
whole-module path and `:11598` for the incremental path) runs
`check_recursion_safety` (`typecheck.ml:10715-10898`). It emits an **ERROR** — not a
warning — for *truly unbounded non-tail recursion*: a recursive call that is neither in
tail position nor structurally decreasing. Structurally decreasing non-tail recursion
gets a **warning** and is allowed (`typecheck.ml:10753-10780`).

Reproduced against the real binaries at the baseline commit:

```
probe       march  lean   what it is
--------------------------------------------------------------------------------
loopy         1      0    self-recursive `loopy(n + 1) + 1`      FALSE ACCEPT
go            1      0    same shape, name `go`                  FALSE ACCEPT
mutual        1      2    `walk`/`helper` SCC                    unconfirmed reject (§7)
fact          0      0    `fact(n - 1) * n` — structural         correct, MUST NOT REGRESS
attr          0      0    `@[no_warn_recursion]` on `loopy`      correct, MUST NOT REGRESS
cond_tail     0      2    tail call in a `match do` arm          correct, MUST NOT REGRESS
```

march's diagnostic on `loopy` is confirmed to be the tail-call error, not a parse or
unbound-name error:

> ``Function `loopy`: recursive call to `loopy` is not in tail position (wrapped in binary operation `+`).``

That confirmation is not ceremony. A `length` probe of the identical shape was drafted
and dropped: march does exit 1 on it, but for a **type** error — `length` resolves to
prelude's `length : List(a) -> Int`, so the probe would have passed while testing
nothing. Every `tailcall` probe asserts on the diagnostic text, not just the exit code.

A blanket "any non-tail recursive call ⇒ reject" is therefore **wrong** — `fact`
disproves it. A blanket skip on any recursive module is also wrong: it would forfeit
real coverage (§6).

## 2. Decision: model it faithfully, from march's own code

The algorithm is ~180 lines of a straightforward AST walk with no solver, no
unification, and no environment. It is transcribable. Every judgment — above all
"structurally decreasing" — is taken from `typecheck.ml`, never from intuition.

Two decisions follow from that, both settled during design:

**Placement — pre-gate, like `CapCheck`.** The pass runs in `MarchLeanCheck.run`
immediately after the `CapCheck` violation branch and **before**
`Compare.inferModule`'s whole-file skip gate. This mirrors march's own ordering (the
capability checks at `typecheck.ml:11351-11364` precede Pass 3 at `:11367`), and it
lets the pass convert reject-side SKIPs into confirmed rejects rather than only
flipping the small set of files that currently accept.

**Input — march's raw JSON envelope, not the decoded `Module`.** See §3.

## 3. Why this pass reads raw JSON

This is the first pass in the repo that does not consume `MarchLean.Syntax`. The
exception is deliberate and narrow: the decoder is lossy in exactly the four places
Pass 3 is structural.

| march Pass 3 needs | decoded `Module` has |
|---|---|
| `fn_attrs`, for the `no_warn_recursion` exemption (`typecheck.ml:10955`) | **dropped** by `Elab.decodeDecl` |
| `ECond` arm bodies are **tail** position (`typecheck.ml:10805-10809`) | `Term.opaque_` — an unordered bag, tail position erased |
| the `ELetQ` continuation is **tail** (`typecheck.ml:10888-10891`) | `Term.opaque_` — same erasure |
| `ELetFn` opens a new scope and shadows its name (`typecheck.ml:10846`, `:10857-10862`) | `Term.opaque_` — binder erased |
| a multi-clause `DFn`'s **name** (a valid SCC target) | `Decl.unsupported` — name erased |

The emitted JSON is march's *surface* AST and carries all of it: `attrs`, `clauses`,
`EBlock`, `EAnnot`, `ELetFn`, `DExtern`, `DMod`. Reading it directly gives a 1:1
transcription of `typecheck.ml` and — decisively — requires **no change to
`Syntax.lean` or `Elab.lean`**, so the existing 86 MATCHes cannot be perturbed by
construction.

Two alternatives were considered and rejected: carrying `attrs` onto `Decl.dfn` (still
permanently blind to `ECond`/`ELetQ`/`ELetFn`, and touches every `Decl.dfn` match site
in `Infer`/`Linearity`/`CapCheck`/`Compare`); and giving those three real `Term`
constructors (most faithful, but re-opens `hasUnsupported`, the whole-file skip gate,
and every existing `CapCheck` walk against the baseline).

Infix operators are emitted as `EApp (EVar "+", …)` — verified directly in emitter
output — so `is_infix_op` (`typecheck.ml:10679`) applies to the JSON unchanged.

## 4. Architecture

New file `MarchLean/TailCall.lean`. One entry point, one result type:

```lean
inductive TailResult where | ok | violation (msg : String)

def check (envelope : Json) : TailResult
```

`TailResult` has **no `skip` case**. The pass either rejects or falls through; `ok`
means "nothing to say", never "accept". Control continues to the unchanged gate →
inference → linearity path exactly as it does after a clean `CapCheck`. The pass can
only ever *add* a reject.

Wiring in `MarchLeanCheck.run`, after the `CapCheck` `.violation` branch:

```lean
match MarchLean.TailCall.check envelope with
| .violation msg => IO.eprintln s!"reject (tail-call): {msg}"; pure 1
| .ok => -- fall through, unchanged
```

`check` reads `envelope.module.decls` itself. `run` already returns exit `2` for
`"module": null` (a parse reject) before reaching this point, so the pass never sees a
module-less envelope; a malformed `decls` array is treated as "nothing to check" and
returns `.ok` rather than erroring, since this pass must never be the reason a file
changes verdict for a non-tail-call reason.

## 5. The port

### 5.1 Per-level driver (`enforce_tail_calls_in_decls`, `typecheck.ml:10902`)

Applied to `module.decls`. **It does not recurse into `DMod`** — see §5.5, which is a
correction to this design's first draft, found by a probe.

- `externNames` ← ∪ over `DExtern` of `extern.fns[*].name.txt`. An extern has no body
  and cannot recurse; march subtracts these so a bare call to one is not resolved
  against a same-named ordinary function (`typecheck.ml:10903-10907`).
- `fnNames` ← { `DFn.fn.name.txt` } `\` `externNames`.
- `adj` ← for each `DFn` with **exactly one** clause:
  `(name, collectDirectFnCalls fnNames clause.body)`. A multi-clause `DFn` contributes
  **no** entry, matching march's `List.filter_map` (`typecheck.ml:10927-10935`). It can
  therefore be an SCC *target* but never a source, and can never close a cycle.
- `sccs` ← Tarjan (`find_sccs`, `typecheck.ml:10631`), iterating `adj` in emission
  order.
- For each `DFn` with exactly one clause: `scc` ← `scc_of[name]`, defaulting to
  `[name]`; `direct` ← `adj[name]`, defaulting to `∅`;
  `isRecursive` ← `scc.length > 1 || name ∈ direct`.
  Check iff `isRecursive && "no_warn_recursion" ∉ fn.attrs`.
- `fnParams` ← per param: `FPNamed` / `FPDefault` → `param.name.txt`;
  `FPPat` → `collectPatternVars pattern` (`typecheck.ml:10957-10963`).

### 5.2 Call graph (`collect_direct_fn_calls`, `typecheck.ml:10539`)

Ported verbatim, including both shadowing sites, which exist because `fn_names` is a
**scope**, not a flat list (the caveat at `typecheck.ml:10530-10537`):

- `EBlock` is the one place a binder's scope extends to **sibling** expressions —
  `ELetFn`/`ELet` carry no continuation of their own, so the left-fold retires the name
  for the rest of the block (`typecheck.ml:10578-10590`).
- `EMatch` retires each arm's pattern-bound names inside that arm
  (`typecheck.ml:10565-10574`), and `ELetQ` retires its pattern's names in the
  continuation.
- `ELetFn` and `ELam` return `∅` — new scopes.

### 5.3 The walk (`check_tail_position`, `typecheck.ml:10726`)

All arms ported, threading `in_tail`, `names`, `smaller`. The load-bearing ones:

- **Recursive call.** `EApp (EVar f, args)` with `f ∈ names` and `¬in_tail` → error
  **unless** `∃ arg. isStructurallySmaller fnParams smaller arg`
  (`typecheck.ml:10742-10744`). Either way, args are then walked with
  `in_tail = false`. The structural branch is march's *warning* path — allowed and
  non-fatal, confirmed by `fact` exiting 0.
- **`isStructurallySmaller`** (`typecheck.ml:10693-10706`), all four clauses exactly:
  1. `EVar v` with `v ∈ smaller`;
  2. `v - k` or `v / k` where `v ∈ params ∪ smaller`;
  3. `EApp (EVar fn, arg :: _)` for `fn ∈ {list_nth_safe, list_nth, List.nth, List.hd, List.head}`, recursing on `arg`;
  4. a nullary `ECon` — structurally minimal.
- **`smaller` grows in exactly two places.** `EMatch` arms, when the scrutinee is a
  param-or-smaller variable (`scrutinee_is_param_or_smaller`, `typecheck.ml:10710`),
  extend it with that arm's pattern vars; and an `EBlock` `ELet` binding a `PatVar` to a
  structurally-smaller RHS adds that name (`typecheck.ml:10834-10841`).
- **`ELam` → no descent.** march skips lambdas entirely (`typecheck.ml:10864`).
  Descending would be a false-reject source.
- **`EAnnot` is transparent** and inherits `in_tail` (`typecheck.ml:10866`).
- **Tail-inheriting positions:** `EIf` branches, `ECond` arm bodies, `EMatch` arm
  bodies, the final `EBlock` element, and the `ELetQ` continuation. Every other
  position is `in_tail = false`.
- **Params are NOT subtracted from `names`.** march starts `chk` with
  `names = rec_set` and never removes parameters (`typecheck.ml:10898`), so neither do
  we.

Report the **first** error found. march reports all of them; one suffices for exit 1.
Message text mirrors march's `ctx` strings so probe output diffs directly against
march's diagnostic.

### 5.4 SCCs by mutual reachability

march runs Tarjan (`find_sccs`, `typecheck.ml:10631`) and asks the result two
questions: is this function on a cycle, and what is its SCC. Both are answered here by
mutual reachability, which *is* the definition of an SCC — a much smaller surface than
a hand-ported Tarjan, over graphs of a few dozen nodes. `reachFrom` returns the names
reachable in **one or more** steps, so `f ∈ reachFrom f` is exactly march's
`List.length scc > 1 || name ∈ direct`.

### 5.5 `DMod` is NOT recursed into — a correction from the probes

The first draft of this design said to recurse into `DMod`, mirroring the arm at
`typecheck.ml:10968-10969`. That would have been a **false reject**. A probe showed
march accepts a non-tail unbounded recursion nested inside `mod Inner do … end` while
rejecting the identical function at top level. Two follow-ups pinned it down:

- A nested *structural* recursion emits no "structurally recursive but not
  tail-recursive" warning either, so it is Pass 3 as a whole that never reaches inside,
  not just its error path.
- A blatant type error inside a nested `mod` is also not reported, so those decls
  appear not to be checked at all in the `--check` path.

Reading the source would not have found this: the `DMod` arm is right there in
`enforce_tail_calls_in_decls` and looks load-bearing. It is dead in this path.

A second, independent mechanism reinforces it, found while mutation-testing the first:
inside a nested module the emitter writes the recursive call as `EVar "Inner.boom"` —
**qualified** — while the declaration is named `boom`. So even a version of this pass
that *did* recurse would form no call-graph edge. `scripts/tailcall-probes/nested_mod.march`
is therefore protected twice over, which is why breaking one mechanism alone does not
turn it red.

### 5.6 Shared helpers

`collectPatternVars` (`typecheck.ml:10507`) and `isInfixOp` (`typecheck.ml:10679`) are
ported verbatim. `isInfixOp` affects only message text, never the verdict.

## 6. The no-false-reject contract

One bail rule:

> **An unrecognised expression `kind` inside a function body abandons that function
> entirely** — no report for it.

`collectDirectFnCalls` may instead return `∅` for an unknown kind: a missing edge can
only *shrink* an SCC, which under-reports. This is strictly safer than the decoder's
current behaviour, where an unhandled kind silently became `Term.unsupported` and
discarded its children.

Every other divergence from march is also under-reporting, i.e. it can leave a false
accept standing but cannot manufacture a false reject:

- A sibling that would decode to `Decl.unsupported` erases a name, which can remove an
  edge but never invent one.
- The envelope omits the injected prelude, which shrinks `fnNames` — again, edges can
  only be lost. Empirically confirmed: `length` (a prelude name) still draws march's
  tail-call ERROR, so prelude presence does not shield a user function.
- `EPipe` / `ESigil` are eliminated by `Desugar` before emission
  (`desugar.ml:543-586`, `:733-744`) and are absent from a 490-file corpus sweep; if
  one ever appears, the bail rule catches it.

Two verified false-reject vectors are handled explicitly, not incidentally:

- `@[no_warn_recursion]` is march's own escape hatch, live in
  `stdlib/hamt.march` and `stdlib/dataframe.march`. Probe `attr` confirms march exits 0
  with it. Ignoring `fn.attrs` would be a guaranteed false reject.
- `match do` (`ECond`) arm bodies are tail position. Probe `cond_tail` confirms march
  exits 0. Treating an arm body as non-tail would be a false reject.

## 7. Scope note: the mutual-recursion case

`mutual` currently exits 2 (`skip: unbound variable \`helper\``) because the
forward-reference fix `af6fece` ("fix(infer): resolve forward references via a
ground-signature pass-1 pre-pass") lives on the unmerged `claude/mutual-recursion`
branch, not `main`. See `.superpowers/sdd/mutual-recursion-report.md` §7.4.

That skip comes from `Compare.inferModule`, which runs **after** this pass. Pre-gate
placement therefore makes the SCC path reachable on `main` regardless: `mutual` should
flip from 2 to 1 once the pass lands, without waiting for `af6fece`. This is the
clearest single argument for the pre-gate placement chosen in §2 — post-gate, `mutual`
would stay a skip and the mutual-recursion half would be untestable end-to-end today.

`mutual` flipping to 1 is therefore an acceptance criterion, not a deferred one.

## 8. Verification

**Probes** — `scripts/tailcall-probes/*.march`, driven by `scripts/tailcall-probes.sh`,
which runs in CI *before* the harness so a false reject fails fast. 22 probes in two
classes: `tailcall` (march must exit 1 **with** the "not in tail position" diagnostic,
and we must exit 1) and `clean` (march must exit 0, and we must not exit 1). The
`clean` probes are the false-reject detectors and are the bulk of the suite.

The runner deliberately does **not** set `pipefail`. march exits 1 on
`--emit-core-ast` for a file it rejects, so a pipefail'd
`march --emit-core-ast | march-lean-check` reports march's 1 in place of the checker's
0 — which silently turned every false accept in the `tailcall` class into a spurious
"ok" on the first run of this suite.

**Mutation testing.** Every `clean` probe was verified to *bite* by breaking the guard
it protects and confirming it goes red. This caught three probes that passed for the
wrong reason:

- `cond_tail` originally recursed as `spin(n - 1)`, which is structurally smaller and
  therefore allowed **whether or not** the arm body is tail position. It tested
  nothing. Rewritten to `spin(dec(n))`.
- The `shadow_*` trio turned out to guard the *walk*, not the *call graph*, so `calls`'
  shadowing was unguarded. Added a `shadow_edge_*` trio in which the shadowed binder is
  the only thing that would forge the SCC edge and the offending non-tail call sits in
  the other function, where no shadowing is in scope to rescue it.
- Nothing guarded `calls` treating `ELam`/`ELetFn` bodies as new scopes. Added
  `lambda_edge` and `letfn_edge` on the same principle.

Guard → probe that goes red when it is broken:

| guard | probe(s) |
|---|---|
| `no_warn_recursion` read | `attr`, `attr_mutual` |
| structural-smallness allowance | `fact`, `match_structural`, `nullary_ctor` |
| `smaller` via match scrutinee | `match_structural` |
| nullary-constructor smallness | `nullary_ctor` |
| `ECond` arm body is tail | `cond_tail` |
| `ELetQ` continuation is tail | `letq_tail` |
| `EIf` branches inherit tail | `tail_ok`, `letq_tail` |
| `chk` does not descend into `ELam` | `lambda_body` |
| `calls`: `ELam` is a new scope | `lambda_edge` |
| `calls`: `ELetFn` is a new scope | `letfn_edge` |
| `calls`: `let` / `letfn` / match-arm shadowing | `shadow_edge_let` / `_letfn` / `_match` |
| both shadowing sites together | `shadow_let` / `shadow_letfn` / `shadow_match` |
| SCC detection (mutual recursion) | `mutual` |

`nested_mod` is the one probe no single mutation turns red, because it is protected
twice over — see §5.5.

**In-repo guards.** Three `native_decide` examples in `TailCall.lean` over real
`--emit-core-ast` envelopes (spans normalised), following the M1 pattern at
`MarchLeanCheck.lean`: `loopy` must violate, `fact` and `attr` must not. These need no
march binary, so they run everywhere the library builds, and a regression breaks the
**build**. Committed tests must not read the gitignored `.superpowers/sdd/samples/`
directory.

**Corpus gate.** Baseline, measured at this commit with
`--corpus-dir specs/lang/types --lang-dir specs/lang`:

```
total files:  334
MATCH:         86
MISMATCH:       0
SKIP:         246   (accept-side 145, reject-side 101)
KNOWN_LIMITATION: 2
RESULT:      PASS
```

The change must hold this or improve it by converting reject-side SKIPs to MATCHes.
**Any accept-side regression is a stop.** Per the standing lesson that green
conformance runs are weak evidence, the hand-built probes — not the corpus — are the
primary instrument here; the corpus is the regression gate.

**Result:** identical to baseline — `MATCH 86 / MISMATCH 0 / SKIP 246 (145 + 101) /
KNOWN_LIMITATION 2 / RESULT: PASS`. Exactly as expected: the corpus contains no
unbounded non-tail recursion, so it moved not one file. It confirms no regression and
nothing else.

**Stdlib sweep** (one-time, not in CI — the workflow's sparse checkout does not include
`stdlib/`). Every march-**accepted** file under march's `stdlib/` and `examples/` was
run through the pass: **124 files, 0 tail-call rejects**. Since march accepts all of
them, any reject would have been a false reject by definition. This is the broadest
false-reject evidence available, and it exercises real `@[no_warn_recursion]` uses in
`hamt.march` and `dataframe.march`. Performance is a non-issue: `dataframe.march`
(3520 lines, a 4 MB envelope) checks in 0.12 s.

## 9. Build

`lake build MarchLean march-lean-check` with **explicit** targets (bare `lake build`
is a 0-job no-op). Lean `leanprover/lean4:v4.29.0`, no Mathlib.
