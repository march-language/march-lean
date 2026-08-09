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
length        1      4    same shape, name collides with prelude FALSE ACCEPT
mutual        1      2    `walk`/`helper` SCC                    unconfirmed reject (§7)
fact          0      0    `fact(n - 1) * n` — structural         correct, MUST NOT REGRESS
attr          0      0    `@[no_warn_recursion]` on `loopy`      correct, MUST NOT REGRESS
cond_tail     0      2    tail call in a `match do` arm          correct, MUST NOT REGRESS
```

march's diagnostic on `loopy` is confirmed to be the tail-call error, not a parse or
unbound-name error:

> ``Function `loopy`: recursive call to `loopy` is not in tail position (wrapped in binary operation `+`).``

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

Applied to `module.decls`, recursing into each `DMod`'s own `decls` as an independent
level:

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

### 5.4 Shared helpers

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

**Probes.** Built as hand-written `.march` files, each run both ways
(`main.exe --check F` vs `main.exe --emit-core-ast F | march-lean-check`), and each
confirmed to produce march's *tail-call* diagnostic rather than a parse or
unbound-name error. The seven in §1 exist already. Still to write:

- structural recursion through an ADT `match` (the `smaller`-via-scrutinee path)
- `list_nth_safe` / `List.hd` accessor arguments
- a nullary-constructor argument
- shadowing by `let`, by `letfn`, and by a match-arm pattern
- an `extern` name colliding with a `DFn` name
- a multi-clause callee inside a cycle
- a nested `DMod`
- `@[no_warn_recursion]` on a *mutually* recursive pair

**In-repo guards.** `native_decide` examples over real emitter envelopes in
`TailCall.lean`, following the M1 pattern at `MarchLeanCheck.lean:123`. Committed tests
must not read the gitignored `.superpowers/sdd/samples/` directory.

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

## 9. Build

`lake build MarchLean march-lean-check` with **explicit** targets (bare `lake build`
is a 0-job no-op). Lean `leanprover/lean4:v4.29.0`, no Mathlib.
