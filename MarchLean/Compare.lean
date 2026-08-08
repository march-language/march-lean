import MarchLean.Syntax
import MarchLean.Result
import MarchLean.Infer

/-!
# `MarchLean.Compare`

Up-to-equivalence comparison of A2's independently-inferred types
(`Infer.MTy`, from `Infer.inferModule'`) against march's own per-node
`resolved_ty` (`Syntax.Ty`), plus `inferModule : Module → IO OracleVerdict`,
A2's independent accept/reject verdict (the A2-reject two-sided oracle;
`MarchLeanCheck`'s `run` composes directly with this, mapping the four
`OracleVerdict` cases plus `Linearity.checkLinearity` to exit codes).

## Design

- **`eqvTy`** walks a zonked `MTy` against a march `Ty` structurally
  (`con`/`arrow`/`tuple`/`record`/`nat`/`natOp`), threading a
  metavar-id ↔ march-`TVar`-id bijection (`IO.Ref (List (Nat × Int))`): a
  residual Lean `mvar id` against a march `Ty.var mid` is not compared by
  raw id (the two numbering schemes are unrelated) but by *consistency*:
  the first time a given `id` (or `mid`) is seen it binds the pairing:
  a later occurrence of the SAME `id` must map to the SAME `mid` (and
  vice versa) or the comparison fails. This is exactly "up to renaming".
- **`.lin` peeling.** `unify` (Task 3) drops `.lin` when solving
  metavariables, so a zonked `MTy` recorded off a `var`/`field` node
  never carries a residual `.lin` wrapper *from unification*, but it CAN
  still carry one transcribed straight from a `DType` ctor signature's
  declared type (`tyToMTy` preserves `Ty.lin` verbatim — see
  `Infer.tyToMTy`'s `.lin` arm — and `zonk` does not strip it either).
  March's `resolved_ty` independently may be a `Ty.lin l t` (`TLin`) at
  any node whose binder was declared linear/affine. Since linearity
  itself is checked by a wholly separate pass (`Linearity`, run by
  Task 7's `main`, NOT here), `eqvTy` peels **any number of** leading
  `.lin` qualifiers off BOTH sides independently before the structural
  match — the two `.lin` annotations are not required to agree (and
  their presence/absence isn't compared at all).
- **`canon` on the march side.** `Result.canon` is applied to the march
  `Ty` before comparison (named-record expansion, forward-compatible:
  the decoder currently routes `TDRecord`/aliases to `Decl.unsupported`,
  so no real sample exercises actual expansion today, but applying
  `canon` here means Compare doesn't silently regress if that changes).
- **`Ty.unsupported` ⇒ no cross-check target.** A `resolved_ty` that
  decoded to `Ty.unsupported` (from a `null` or genuinely out-of-fragment
  annotation) at some position means march gave us nothing to check
  there — `eqvTy` treats it as trivially equal rather than mismatching.
  In practice this should be unreachable by the time `eqvTy` runs (the
  `Decl.hasUnsupported` whole-module skip gate already walks every node's
  `ty` transitively via `Term.hasUnsupported`, so if any node anywhere
  had `Ty.unsupported` the whole module would already be `.skip`), but
  the check costs nothing and guards against any future gap in that
  transitive walk.
- **Bijection scope: per-node.** A fresh, empty bijection `IO.Ref` is
  allocated for each `(span, MTy)` record compared against its node's
  `resolved_ty` — NOT one shared bijection for the whole module. This is
  the simpler, safe option the brief calls out: each node's inferred type
  is checked for *internal* self-consistency (e.g. an `arrow (mvar q)
  (mvar q)` must map to the SAME march tvar on both sides within that ONE
  occurrence), but consistency is not required *across* different
  occurrences (e.g. a polymorphic identifier's two separate uses may
  legitimately be instantiated to different concrete types, and even
  where both remain polymorphic march's own tvar numbering for a fresh
  instantiation need not match across uses). Nothing in the accept
  fragment requires the stronger whole-module bijection, and per-node
  avoids a large class of accidental false-rejects from harmless numbering
  differences across occurrences.
-/

namespace MarchLean.Compare

open MarchLean.Syntax
open MarchLean.Result
open MarchLean.Infer

/-- Strip any number of leading `Ty.lin` qualifiers (march's linear/affine
annotation is checked by a separate pass, not here — see the module doc). -/
partial def unwrapLinTy : Ty → Ty
  | .lin _ t => unwrapLinTy t
  | t => t

/-- Strip any number of leading `MTy.lin` qualifiers (see `unwrapLinTy`; a
zonked `MTy` can still carry one transcribed from a ctor signature's
declared type — `unify` only drops `.lin` it itself introduces). -/
partial def unwrapLinMTy : MTy → MTy
  | .lin _ t => unwrapLinMTy t
  | t => t

/-- Consult/bind the metavar-id ↔ march-`TVar`-id bijection for one
`(mid, tid)` pairing. First encounter of either side: binds the pairing
and succeeds. Later encounter of `mid` with the SAME `tid` (or vice
versa): succeeds. `mid` (or `tid`) already bound to a DIFFERENT partner:
fails — that's an actual inconsistency, e.g. a single Lean metavariable
that would have to correspond to two different march type variables
simultaneously, which cannot be a valid renaming. -/
def bijCheck (bij : IO.Ref (List (Nat × Int))) (mid : Nat) (tid : Int) : IO Bool := do
  let l ← bij.get
  match l.find? (fun p => p.1 == mid) with
  | some (_, tid') => pure (tid' == tid)
  | none =>
    match l.find? (fun p => p.2 == tid) with
    | some _ => pure false   -- `tid` already claimed by a different `mid`
    | none => do
        bij.modify (fun l => (mid, tid) :: l)
        pure true

/-- Up-to-equivalence comparison of a zonked `Infer.MTy` (Lean's
independently-inferred type for one node) against march's decoded
`Syntax.Ty` (that same node's `resolved_ty`), threading the per-node
bijection `bij` (see the module doc for its scope). `env` is the
module's datatype environment, used by `Result.canon` to normalize the
march side first. Structural on `con`/`arrow`/`tuple`/`record`/`nat`/
`natOp` (mirroring `Infer.unify`'s own structural cases); a residual
`MTy.mvar` against a march `Ty.var` is reconciled via `bijCheck`; any
other shape combination (including a definite type meeting an
unresolved metavariable, or vice versa) is a genuine disagreement. -/
partial def eqvTy (bij : IO.Ref (List (Nat × Int))) (env : TyEnv)
    (mty0 : MTy) (ty0 : Ty) : IO Bool := do
  let ty1 := unwrapLinTy (canon env ty0)
  match ty1 with
  | .unsupported => pure true   -- no cross-check target; see module doc
  | _ =>
    let mty := unwrapLinMTy mty0
    match mty, ty1 with
    | .mvar mid, .var tid => bijCheck bij mid tid
    | .con n1 a1, .con n2 a2 => do
        if n1 != n2 || a1.length != a2.length then pure false
        else do
          let mut ok := true
          for (x, y) in a1.zip a2 do
            if !(← eqvTy bij env x y) then ok := false
          pure ok
    | .arrow a1 b1, .arrow a2 b2 => do
        let ra ← eqvTy bij env a1 a2
        let rb ← eqvTy bij env b1 b2
        pure (ra && rb)
    | .tuple t1, .tuple t2 => do
        if t1.length != t2.length then pure false
        else do
          let mut ok := true
          for (x, y) in t1.zip t2 do
            if !(← eqvTy bij env x y) then ok := false
          pure ok
    | .record f1, .record f2 => do
        if f1.length != f2.length then pure false
        else do
          let mut ok := true
          for ((n1, x), (n2, y)) in f1.zip f2 do
            if n1 != n2 then ok := false
            else if !(← eqvTy bij env x y) then ok := false
          pure ok
    | .nat n1, .nat n2 => pure (n1 == n2)
    | .natOp o1 a1 b1, .natOp o2 a2 b2 =>
        if o1 != o2 then pure false
        else do
          let ra ← eqvTy bij env a1 a2
          let rb ← eqvTy bij env b1 b2
          pure (ra && rb)
    | _, _ => pure false

/-- Is `t` (after canon-normalizing and peeling any leading `.lin`
qualifiers, same normalization `eqvTy` itself applies) an arrow type at
the top? Used to shape-condition the callee exclusion below — checking
the ALREADY-canon/peeled shape, not the raw `Ty`, so a `TLin`-wrapped or
named-record-aliased arrow is still recognized as an arrow. -/
def isArrowShaped (env : TyEnv) (t : Ty) : Bool :=
  match unwrapLinTy (canon env t) with
  | .arrow _ _ => true
  | _ => false

/-- Every `(span, ty)` pair carried by a `var`/`field` node reachable from
`t` — the only two `Term` constructors carrying a span (mirrors what
`Infer.infer` itself records into `ctx.acc`, so this list and A2's
recorded output are keyed the same way).

`isCallee` marks whether `t` is sitting in the direct callee (`fn`) slot
of an `EApp`. **Real-sample finding, and the fix's shape (tightened after
review):** march's emitter annotates an OPERATOR's callee `var` node
(`+`, `>`, `==`, …) with the APPLICATION's RESULT type, not the callee's
own arrow type — e.g. `p.x + p.y`'s `+` node is annotated `Int` (the
sum's type), not `Int → Int → Int`, and `n > m`'s `>` node is annotated
`Bool`, not `Int → Int → Bool` (confirmed directly against
`accept_record.json`'s `t09_record_literal_field.march` and
`accept_if_ord.json`'s `t04_if.march` samples). `Check.lean`'s A1 checker
already documents and works around this exact quirk (design §2: "the
callee node's own `resolved_ty` is NOT reliably the function type"),
treating an un-witnessed callee's non-arrow annotation as `.skip`, never
`.reject`.

An EARLIER version of this fix excluded EVERY callee-position span
unconditionally — that over-corrected: regular function callees
(`println`, `int_to_string`, a let-bound polymorphic identifier, a
user-defined `dfn`) carry a CORRECT `TArrow` `resolved_ty` and are a
perfectly good cross-check target; blanket-excluding them measured at
only 16 of 38 real-sample var/field spans (42%) actually being compared,
thinning the very per-node signal Task 6 exists to provide. The fix is
now SHAPE-CONDITIONED instead of position-blanket: a callee-position span
is excluded ONLY when its own `resolved_ty` (canon+`.lin`-peeled,
`isArrowShaped`) is NOT an arrow — i.e. only the genuine operator-quirk
case (`Int`/`Bool`/etc. where an arrow was expected) is dropped; a callee
whose annotation IS an arrow is kept and compared exactly like any other
occurrence. Every non-callee position (arguments, branches, bodies,
record/tuple elements, ...) was never affected either way. -/
partial def termSpanTys (env : TyEnv) (isCallee : Bool) : Term → List (Span × Ty)
  | .lit _ _ => []
  | .var _ span ty =>
      if isCallee && !isArrowShaped env ty then [] else [(span, ty)]
  | .app fn args _ =>
      termSpanTys env true fn ++ (args.map (termSpanTys env false)).foldl (· ++ ·) []
  | .lam _ body _ => termSpanTys env false body
  | .let_ _ _ _ rhs body _ => termSpanTys env false rhs ++ termSpanTys env false body
  | .letfn _ _ _ _ fnBody body _ => termSpanTys env false fnBody ++ termSpanTys env false body
  | .ite c t e _ => termSpanTys env false c ++ termSpanTys env false t ++ termSpanTys env false e
  | .con _ args _ => (args.map (termSpanTys env false)).foldl (· ++ ·) []
  | .tuple es _ => (es.map (termSpanTys env false)).foldl (· ++ ·) []
  | .record fs _ => (fs.map (fun (_, e) => termSpanTys env false e)).foldl (· ++ ·) []
  | .field r _ span ty =>
      (if isCallee && !isArrowShaped env ty then [] else [(span, ty)]) ++ termSpanTys env false r
  | .match_ scrut arms _ =>
      termSpanTys env false scrut ++
        (arms.map (fun (_, _, body) => termSpanTys env false body)).foldl (· ++ ·) []
  -- `.opaque_` is grouped with `.unsupported` and yields NO cross-check
  -- targets. This walk runs only inside `inferModule` step (3), i.e. AFTER
  -- the step-(1) whole-file skip gate — and `Term.hasUnsupported` hard-codes
  -- `true` for `opaque_`, so any module containing one has already returned
  -- `.skip`. The arm is unreachable; mirroring `.unsupported` is the choice
  -- that provably changes nothing. (Recursing would also be harmless, but it
  -- would suggest these spans participate in the resolved_ty cross-check,
  -- and they never can: their children are never inferred.)
  | .opaque_ _ _ => []
  | .unsupported _ => []

/-- `termSpanTys`, dispatched over one declaration (`dtype` carries no
terms). A decl's own top-level body is never itself a callee. -/
def declSpanTys (env : TyEnv) : Decl → List (Span × Ty)
  | .dtype .. => []
  | .dlet _ body => termSpanTys env false body
  | .dfn _ _ _ _ body => termSpanTys env false body
  -- A3 Task 2/3 decode-only constructors: no term of their own, so no
  -- `(span, ty)` pairs to contribute. `dmod` is inert-but-unreachable here:
  -- `inferModule` flattens nested `dmod`s via `flattenDecls` before this is
  -- ever called, so its children already appear as top-level decls.
  | .dmod .. | .dneeds _ | .duse _ | .dextern .. | .dproofcap _ | .dopts _ => []
  | .unsupported => []

/-- Every `(span, resolved_ty)` pair for every `var`/`field` node in the
whole module — the lookup table `inferModule` diffs A2's recorded
`(span, MTy)` output against. `env` is the module's datatype environment
(the same one `inferModule` already builds via `buildTyEnv`, passed in
rather than recomputed). -/
def moduleSpanTys (env : TyEnv) (m : Module) : List (Span × Ty) :=
  (m.decls.map (declSpanTys env)).foldl (· ++ ·) []

/-- The Task 8b coverage-gap marker: `Infer.lean` prefixes exactly its
unbound-variable and unknown-constructor throws with this literal string
(see `Infer`'s module doc, "Task 8b"). Any other inference throw is a
genuine type disagreement and does not carry it. -/
def skipMarker : String := "SKIP: "

/-! ## The non-tail-recursion accept gate

march runs an **ERROR**-level check this oracle does not model at all:
`enforce_tail_calls_in_decls` (`typecheck.ml:10902`, invoked as "Pass 3" at
`typecheck.ml:11368`), whose analysis is `check_tail_position`
(`typecheck.ml:10715-10898`). It rejects a recursive call that is **both**
outside tail position **and** not provably structurally decreasing. The
discriminator is easy to miss and worth stating precisely, because it is what
makes the check impossible to approximate safely:

- `fn pong(n : Int) : Int do pong(n - 1) + 1 end` — march proves the argument
  decreases, emits only a WARNING, and **accepts** (exit 0).
- `fn a(n : Int) : Int do b(n + 1) + 1 end` / `fn b(n : Int) : Int do a(n + 1) + 1 end`
  — march cannot prove decrease, so the non-tail call is an ERROR and march
  **rejects** (exit 1).

Both were verified directly. Telling those two apart requires march's
structural-decrease analysis, which this oracle deliberately does not
reconstruct (partial reconstructions of a march decision are how false rejects
get built). So the honest response to *either* is a non-verdict.

Before this gate, the inference layer answered ACCEPT for both — a confident
verdict on a program march rejects, on grounds we never examined. The
ground-signature pre-pass made that reachable for mutual recursion; it was
**already** reachable for self-recursion
(`fn loopy(n : Int) : Int do loopy(n + 1) + 1 end` ⇒ march 1, oracle 0), and the
same gate covers both.

**What the gate does.** Purely syntactically, and only on the ACCEPT path: if
any top-level `dfn` that participates in recursion mentions a member of its own
recursive group anywhere other than as the direct callee of a tail-position
call, the module returns `.skip`. It renders no opinion about tail-call
legality — it declines to answer.

**Scope, mirrored from march** (`typecheck.ml:10917-10966`): the call graph is
built over top-level `DFn` names only, a function is "recursive" exactly when
its SCC has more than one member or it calls itself directly
(`typecheck.ml:10951-10954`), and the names checked inside its body are its
whole SCC (`rec_set`, `typecheck.ml:10956`). Matching that scoping is what
keeps the gate from firing on an ordinary non-recursive caller — `fn main`
calling a recursive helper inside `println(...)` is not itself recursive, so it
is never gated.

**Every approximation is deliberately toward MORE skipping**, since
over-skipping is safe here and under-skipping is the false accept being closed:

- Graph edges come from *every* name a body mentions, ignoring shadowing, where
  march uses direct calls only (`collect_direct_fn_calls`). A superset of edges
  can only merge SCCs, never split them.
- march exempts a `fn` carrying the `no_warn_recursion` attribute
  (`typecheck.ml:10955`); this decoder does not model attributes, so such a
  function is gated anyway.
- A bare (non-callee) mention of a group member is treated as disqualifying even
  in tail position, and a lambda / local-`fn` body is treated as a non-tail
  context, even though march gives both their own scope
  (`typecheck.ml:10856-10863`).
- Anything not recognised as a tail position is treated as non-tail.
- march builds a separate graph per module level, recursing into each `DMod`
  with its own declarations (`typecheck.ml:10968`). This runs after
  `flattenDecls`, so nested-module functions share one graph with the top
  level — again only able to merge groups, never split them.

**REJECT stays reachable.** The gate runs only after `Infer.inferModule'` has
already succeeded, so a genuine type error — a wrong argument type, a wrong
return annotation, a wrong arity — still rejects exactly as before, tail
position notwithstanding. Only a would-be ACCEPT is downgraded. -/

/-- Every name syntactically mentioned anywhere in `t`. Deliberately
over-approximating: binder shadowing is ignored, so a local `let map = …` still
contributes the name `map`. Used only to build the recursion call graph, where a
superset of edges is the safe direction (see the section doc). -/
partial def termMentions : Term → List String
  | .lit _ _ => []
  | .var n _ _ => [n]
  | .app fn args _ => termMentions fn ++ args.flatMap termMentions
  | .lam _ body _ => termMentions body
  | .let_ _ _ _ rhs body _ => termMentions rhs ++ termMentions body
  | .letfn _ _ _ _ fnBody body _ => termMentions fnBody ++ termMentions body
  | .ite c t e _ => termMentions c ++ termMentions t ++ termMentions e
  | .con _ args _ => args.flatMap termMentions
  | .tuple es _ => es.flatMap termMentions
  | .record fs _ => fs.flatMap (fun (_, e) => termMentions e)
  | .field r _ _ _ => termMentions r
  | .match_ scrut arms _ =>
      termMentions scrut ++
        arms.flatMap (fun (_, g, b) => (g.map termMentions).getD [] ++ termMentions b)
  -- `.opaque_`/`.unsupported` children are never inferred (the whole module has
  -- already skipped by the time this runs), so they contribute no edges.
  | .opaque_ _ _ => []
  | .unsupported _ => []

/-- `(name, body)` for every top-level `dfn`. march's tail-call pass builds its
call graph over `DFn` declarations only (`typecheck.ml:10918-10935`); a `dlet` is
not a function and contributes neither a node nor an edge. -/
def dfnBodies (decls : List Decl) : List (String × Term) :=
  decls.filterMap (fun d => match d with
    | .dfn _ n _ _ body => some (n, body)
    | _ => none)

/-- One round of transitive-closure widening: replace each node's reachable set
with itself plus everything its members reach directly. -/
def closureStep (direct : List (String × List String)) (cur : List (String × List String)) :
    List (String × List String) :=
  cur.map (fun (x, ys) =>
    (x, ys.foldl (fun acc y =>
      match direct.find? (fun p => p.1 == y) with
      | some (_, zs) => zs.foldl (fun a z => if a.contains z then a else z :: a) acc
      | none => acc) ys))

/-- Transitive closure of `direct`, by bounded iteration. `fuel` rounds suffice
for a graph with `fuel` nodes (each round adds at least one edge to some node's
reachable set, or the fixpoint is already reached). -/
def closure : Nat → List (String × List String) → List (String × List String) → List (String × List String)
  | 0, _, cur => cur
  | fuel + 1, direct, cur =>
      let next := closureStep direct cur
      if next.map (fun p => p.2.length) == cur.map (fun p => p.2.length) then cur
      else closure fuel direct next

/-- Is `b` in `a`'s reachable set, per an already-computed `closure` table? -/
def reachesIn (reach : List (String × List String)) (a b : String) : Bool :=
  match reach.find? (fun p => p.1 == a) with
  | some (_, zs) => zs.contains b
  | none => false

/-- For each top-level `dfn`, the set of names it must be checked against: its
own recursive group, or `[]` when it does not participate in recursion.

This is march's `scc_of` / `is_recursive` / `rec_set` triple
(`typecheck.ml:10937-10956`) computed by mutual reachability rather than by
Tarjan: `n` is in `d`'s group exactly when each reaches the other, which is the
definition of "same SCC", and `d` is recursive exactly when its group is
non-empty (`d` reaches itself — covering both `|scc| > 1` and a direct
self-call). -/
def recursiveGroups (decls : List Decl) : List (String × List String) :=
  let bodies := dfnBodies decls
  let names := bodies.map (·.1)
  let direct := bodies.map (fun (n, b) =>
    (n, (termMentions b).filter (fun m => names.contains m)))
  let reach := closure names.length direct direct
  names.map (fun d =>
    if reachesIn reach d d then
      (d, names.filter (fun n => reachesIn reach d n && reachesIn reach n d))
    else (d, []))

/-! ### The structural-decrease whitelist

A non-tail recursive call is only an ERROR for march when it is ALSO not
provably structurally decreasing (`typecheck.ml:10738-10751`). Gating every
non-tail recursive call therefore over-skips a large and completely ordinary
class — `fn fib(n) do fib(n - 1) + fib(n - 2) end`, `n * fact(n - 1)` — that
march merely WARNS about and accepts. `specs/lang/grammar/parse/p15` is exactly
this, and blanket gating cost it.

So the gate consults a **whitelist of decreasing-argument shapes we are certain
about**. It is deliberately a strict SUBSET of march's own
`is_structurally_smaller` (`typecheck.ml:10693-10706`), never an attempt to
reproduce it, because the asymmetry is total: over-gating costs coverage,
under-gating reinstates the false accept that this whole gate exists to remove.

march's rule, for reference (`typecheck.ml:10693-10706` plus the `List.exists`
at `:10743`): a call is allowed when **at least one argument** is
(1) a variable in `smaller`, (2) `v - _` or `v / _` where `v` is a parameter or
in `smaller` — **the right operand is not examined at all**, so march accepts
`n - 0` and `n - m`, (3) a list-accessor application, or (4) a nullary
constructor. `smaller` grows at a `match` whose scrutinee is a bare parameter (or
already-smaller variable): every variable bound by an arm's pattern joins
`smaller` inside that arm (`typecheck.ml:10812-10824`) — which is what makes the
desugared multi-head `fib` work, since merging leaves one synthetic `__arg0`
parameter and binds `n` in a `PatVar` arm.

**What this whitelist recognises, and nothing else:** an argument
`p - k` where `p` is a bare variable in the current decrease base and `k` is a
**positive integer literal**. The base starts as the `dfn`'s own directly-bound
parameter names and grows exactly as march's `smaller` does at a `match` on a
base variable.

Every difference from march is in the over-gating direction:

| shape | march | here |
|---|---|---|
| `f(n - 1)` | smaller | **recognised** |
| `f(n - 0)` | smaller (rhs unexamined) | gated — `k` must be positive |
| `f(n - m)` | smaller | gated — `k` must be a literal |
| `f(n / 2)` | smaller | gated — only `-` is recognised |
| `f(xs_tail)` where `xs_tail` is pattern-bound | smaller (rule 1) | gated |
| `f(List.nth(xs, i))`, `f(Nil)` | smaller (rules 3, 4) | gated |
| `p` shadowed by an inner `let`/`lam`/pattern | still counted (march never removes) | gated — base is shadowing-aware |
| `f(n + 1)`, `f(n * 2)`, `f(g(n))`, `f(q)` | NOT smaller | gated (agrees) |

The last row is the one that matters for safety, and it agrees exactly. -/

/-- Every variable name a pattern binds (march's `collect_pattern_vars`). -/
partial def patternVars : Pattern → List String
  | .wild | .lit _ | .unsupported => []
  | .var n _ => [n]
  | .con _ args => args.flatMap patternVars
  | .tuple es => es.flatMap patternVars
  | .record fs => fs.flatMap (fun (_, p) => patternVars p)
  | .as n p => n :: patternVars p
  | .or_ alts => alts.flatMap patternVars

/-- Is `arg` a recognised structurally-decreasing argument — `p - k` for a bare
`p` in the decrease base `base` and a positive integer literal `k`? See the
section doc: this is a deliberate strict subset of march's
`is_structurally_smaller`. -/
def isRecognisedDecrease (base : List String) : Term → Bool
  | .app (.var "-" _ _) [.var p _ _, .lit (.int k) _] _ => base.contains p && k > 0
  | _ => false

/-- Does `t` contain a use of a member of `names` that march's tail-call pass
could flag as an ERROR — i.e. anything other than (a) the direct callee of a
tail-position call, or (b) the direct callee of a call carrying a recognised
structurally-decreasing argument?

`tail` is whether `t` itself sits in tail position; `base` is the decrease base
(see the section doc). Every unrecognised or ambiguous position is treated as
non-tail and every unrecognised argument as non-decreasing, so the answer errs
toward `true` (⇒ skip). -/
partial def hasNonTailRecUse (names : List String) : Bool → List String → Term → Bool
  | _, _, .lit _ _ => false
  -- A bare mention that is not an app callee: conservatively disqualifying even
  -- in tail position (march would not count it as a recursive CALL at all).
  | _, _, .var n _ _ => names.contains n
  | tail, base, .app fn args _ =>
      let calleeBad :=
        match fn with
        -- A direct call to a group member is fine when the call is itself in
        -- tail position, or when at least one argument is a recognised
        -- structural decrease (march's `List.exists`, `typecheck.ml:10743`).
        | .var n _ _ =>
            if names.contains n then
              !(tail || args.any (isRecognisedDecrease base))
            else false
        | _ => hasNonTailRecUse names false base fn
      calleeBad || args.any (hasNonTailRecUse names false base)
  -- A lambda's parameters shadow same-named entries in the decrease base.
  | _, base, .lam ps body _ =>
      hasNonTailRecUse names false (base.filter (fun b => !(ps.map (·.1)).contains b)) body
  | tail, base, .let_ n _ _ rhs body _ =>
      hasNonTailRecUse names false base rhs ||
        hasNonTailRecUse names tail (base.filter (· != n)) body
  | tail, base, .letfn n p _ _ fnBody body _ =>
      hasNonTailRecUse names false (base.filter (fun b => b != n && b != p)) fnBody ||
        hasNonTailRecUse names tail (base.filter (· != n)) body
  | tail, base, .ite c t e _ =>
      hasNonTailRecUse names false base c ||
        hasNonTailRecUse names tail base t || hasNonTailRecUse names tail base e
  | _, base, .con _ args _ => args.any (hasNonTailRecUse names false base)
  | _, base, .tuple es _ => es.any (hasNonTailRecUse names false base)
  | _, base, .record fs _ => fs.any (fun (_, e) => hasNonTailRecUse names false base e)
  | _, base, .field r _ _ _ => hasNonTailRecUse names false base r
  | tail, base, .match_ scrut arms _ =>
      -- march's `smaller` growth (`typecheck.ml:10812-10824`): matching on a
      -- bare base variable makes every arm-bound pattern variable part of the
      -- base inside that arm. Otherwise the pattern variables SHADOW, so they
      -- leave the base (march does not do this removal; doing it is stricter).
      let scrutInBase := match scrut with
        | .var v _ _ => base.contains v
        | _ => false
      hasNonTailRecUse names false base scrut ||
        arms.any (fun (p, g, b) =>
          let pv := patternVars p
          let armBase :=
            if scrutInBase then base ++ pv.filter (fun x => !base.contains x)
            else base.filter (fun x => !pv.contains x)
          (g.map (hasNonTailRecUse names false armBase)).getD false ||
            hasNonTailRecUse names tail armBase b)
  | _, _, .opaque_ _ _ => false
  | _, _, .unsupported _ => false

/-- The gate itself: `some name` when top-level `dfn` `name` participates in
recursion and uses a member of its own recursive group outside a tail-position
call — i.e. exactly when march would apply an ERROR-level check this oracle does
not model, and the module must therefore return `.skip` instead of `.accept`. -/
def nonTailRecursionGate (decls : List Decl) : Option String :=
  let groups := recursiveGroups decls
  decls.findSome? (fun d =>
    match d with
    | .dfn _ n params _ body =>
        match groups.find? (fun p => p.1 == n) with
        | some (_, grp) =>
            if grp.isEmpty then none
            -- The decrease base starts as this `dfn`'s own directly-bound
            -- parameter names (march's `fn_params`, `typecheck.ml:10957-10963`).
            else if hasNonTailRecUse grp true (params.map (·.1)) body then some n
            else none
        | none => none
    | _ => none)

/-- `inferModule m`: A2's independent verdict on a module, as an
`OracleVerdict` (not a pure value) because `Infer.inferModule'` runs in
`IO` (the `Supply` metavariable arena is backed by `IO.Ref`s) — this
composes directly with `MarchLeanCheck`'s `run`, which maps each
`OracleVerdict` case plus `Linearity.checkLinearity`'s result to an exit
code.

1. Whole-file skip gate: any out-of-fragment construct in a declaration
   (`Decl.hasUnsupported`, transitively covers every subterm/pattern/type),
   or any scheme carrying a `CInterface` constraint that is not
   `Num`/`Eq`/`Ord` (`Result.constraintOutOfFragment` — same judgment call
   A1 used, shared rather than re-derived).
2. Run `Infer.inferModule'` in `IO`; a `throw` is either a genuine
   inference failure (A2's independent engine finds the program ill-typed —
   `.reject`, A2's own reject verdict) or a coverage gap (the engine simply
   doesn't model some NAME or CONSTRUCT the module references — `.skip`,
   never a false reject). The two are told apart by the `SKIP:` marker
   prefix `Infer.lean` puts on exactly its unbound-variable and unknown-
   constructor throws (Task 8b; see `Infer`'s module doc, "Task 8b" — every
   other throw there, e.g. a `unify` shape clash, arity mismatch, occurs
   check, or `requireClass` violation, is a genuine type error and stays
   unmarked).
3. For every recorded `(span, MTy)`, look up that node's `resolved_ty`
   (`moduleSpanTys`) and `eqvTy` them (fresh per-node bijection); any
   disagreement is `.typesDiffer` (A2 accepts the program as well-typed,
   but its per-node types disagree with march's `resolved_ty`).
4. Otherwise `.accept`.

Linearity is checked by a separate pass (`Linearity.checkLinearity`,
run by `MarchLeanCheck`'s `run`), not here. -/
def inferModule (m : Module) : IO OracleVerdict := do
  -- Flatten nested `dmod` bodies into the enclosing scope first — inference
  -- treats a module as transparent (see `flattenDecls`'s docstring). `m'` is
  -- what every step below walks, in place of `m`.
  let m' : Module := { m with decls := flattenDecls m.decls }
  -- (1) whole-file skip gate: any out-of-fragment construct anywhere.
  if m'.decls.any Decl.hasUnsupported then
    return .skip "out-of-fragment construct in a declaration"
  -- (1b) skip gate: a scheme carrying a non-Num/Eq/Ord CInterface (as A1).
  if m'.schemes.any (fun sch => sch.constraints.any constraintOutOfFragment) then
    return .skip "scheme carries an out-of-fragment constraint"
  -- (2) run the independent inference engine.
  let s ← Supply.new
  match ← (inferModule' s m').run with
  | .error e =>
    -- (2b) Task 8b: an unmodeled name/constructor is a coverage gap, not a
    -- type disagreement — route it to `.skip` instead of a false `.reject`.
    if e.startsWith skipMarker then
      return .skip s!"out of modeled fragment: {e}"
    else
      return .reject s!"infer: {e}"
  | .ok recorded =>
    -- (2c) Non-tail-recursion accept gate. Inference found no type error, so
    -- the only verdicts still open are `.accept`/`.typesDiffer` — and neither
    -- is honest for a module where march applies its unmodeled ERROR-level
    -- tail-call check (`enforce_tail_calls_in_decls`). Decline to answer
    -- instead. Placed AFTER the `.error` branch above so a genuine type
    -- disagreement still rejects regardless of tail position, and BEFORE the
    -- step-(3) cross-check so we do not report `.typesDiffer` about a module we
    -- have just admitted we cannot judge. See `nonTailRecursionGate`.
    match nonTailRecursionGate m'.decls with
    | some n =>
      return .skip s!"out of modeled fragment: `{n}` uses its recursive group outside tail position; march's ERROR-level tail-call check (typecheck.ml:10902) is not modeled"
    | none => pure ()
    -- (3) cross-check every recorded var/field node against march's resolved_ty.
    let env := buildTyEnv m'.decls
    let spanTys := moduleSpanTys env m'
    for (span, mty) in recorded do
      match spanTys.find? (fun p => p.1 == span) with
      | none => pure ()   -- defensive: no module node carries this span
      | some (_, ty) =>
        let bij ← IO.mkRef ([] : List (Nat × Int))
        -- `mty` is already zonked by `inferModule'` (it zonks every recorded
        -- node type before returning); no need to zonk again here.
        if !(← eqvTy bij env mty ty) then
          return .typesDiffer s!"type at {repr span}"
    -- (4) all recorded nodes agree.
    return .accept

end MarchLean.Compare

-- Living tests (executable documentation; run at build time via `#eval`).
-- Hand-built `Module` values only — no `IO.FS.readFile` of the gitignored
-- `samples/` dir (that broke fresh-checkout CI once already; see A1 #4).
namespace MarchLean.Compare.Test
open MarchLean.Syntax MarchLean.Result MarchLean.Compare

private def dSpan : Span := ⟨"t", 0, 0, 0, 0⟩
private def dTy0 : Ty := Ty.con "Int" []   -- filler; ignored by `infer`/`eqvTy` on non-var/field nodes

/-- `let id = λx.x in id` — "id" used UNAPPLIED, so its recorded type is the
whole (fresh-instantiated) polymorphic arrow `?q → ?q`, exercising the
per-node bijection's OWN consistency requirement (the same Lean metavariable
appears twice and must map to the same march tvar both times). The inner
lambda's own `x` occurrence is annotated with a DIFFERENT march tvar id (`3`)
than the outer occurrence uses (`7`) — legitimate, since each is its own
per-node bijection and march's real tvar numbering need not agree with
Lean's mvar ids OR across occurrences (see the module doc on bijection
scope). -/
private def innerSpan : Span := ⟨"t", 1, 1, 1, 2⟩
private def innerVarTy : Ty := Ty.var 3
private def idLam : Term := Term.lam [("x", .unrestricted, none)] (Term.var "x" innerSpan innerVarTy) dTy0
private def useSpan : Span := ⟨"t", 2, 1, 2, 4⟩
private def idArrowTy : Ty := Ty.arrow (Ty.var 7) (Ty.var 7)
private def useBodyOk : Term := Term.var "id" useSpan idArrowTy
private def letTermOk : Term := Term.let_ "id" .unrestricted none idLam useBodyOk dTy0
private def mOk : Module := { decls := [.dlet "top" letTermOk], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mOk
  IO.println s!"ok-case: {repr r}"
-- expected: ok-case: OracleVerdict.accept

/-- Same module, but "id"'s use-site `resolved_ty` structurally contradicts
what A2 infers (`Bool` instead of an arrow) — a deliberate node-type
disagreement. -/
private def useBodyBad : Term := Term.var "id" useSpan (Ty.con "Bool" [])
private def letTermBad : Term := Term.let_ "id" .unrestricted none idLam useBodyBad dTy0
private def mRejectType : Module := { decls := [.dlet "top" letTermBad], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mRejectType
  IO.println s!"reject-type-case: {repr r}"
-- expected: reject-type-case: OracleVerdict.typesDiffer "type at ..."

/-- A module with an `unsupported` decl forces `.skip`. -/
private def mSkip : Module := { decls := [.unsupported], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mSkip
  IO.println s!"skip-case: {repr r}"
-- expected: skip-case: OracleVerdict.skip ...

/-- A scheme carrying a non-`Num`/`Eq`/`Ord` `CInterface` (a user typeclass)
also forces `.skip`, before inference is even attempted (as A1). -/
private def mSkipInterface : Module :=
  { decls := [.dlet "x" (Term.var "f" dSpan (Ty.con "Int" []))],
    schemes := [{ ids := [0], constraints := [Constraint.interface "Show" (Ty.var 0)], body := Ty.var 0 }],
    insts := [] }

#eval show IO Unit from do
  let r ← inferModule mSkipInterface
  IO.println s!"skip-interface-case: {repr r}"
-- expected: skip-interface-case: OracleVerdict.skip ...

/-- A module that A2's independent engine cannot type: applying an `Int`
literal as if it were a function. `unify` hits its `con`-vs-`arrow` shape
mismatch and `throw`s, which `inferModule` maps to `.reject "infer: ..."`
— A2's own reject verdict. -/
private def badAppTerm : Term :=
  Term.app (Term.lit (.int 1) dTy0) [Term.lit (.int 2) dTy0] dTy0
private def mRejectInfer : Module := { decls := [.dlet "z" badAppTerm], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mRejectInfer
  IO.println s!"reject-infer-case: {repr r}"
-- expected: reject-infer-case: OracleVerdict.reject "infer: ..."

/-! ### Task 8b: unmodeled name/constructor ⇒ `.skip`, genuine type error ⇒ `.reject`

The exploratory corpus run found several march-accepted files where A2's
`infer` throws not because it disagrees with march about a type, but
because the engine simply doesn't model some referenced NAME (a stdlib/
cross-module identifier like `Array.empty` or `List.range`) or CONSTRUCT
(an unknown constructor like `None`). Those are engine coverage gaps, not
real disagreements, and must `.skip` rather than falsely `.reject`. The two
tests below pin both sides of that classification using hand-built modules
(no `IO.FS.readFile` of the gitignored `samples/` dir): an unbound-variable
reference must `.skip`; `mRejectInfer` above (applying a non-function)
already pins that a genuine type error still `.reject`s — the second test
below adds a distinct genuine-type-error shape (a `let` annotation that
contradicts its rhs) for extra coverage of that side of the boundary. -/

/-- `z = undefinedName` — `undefinedName` is neither a user binder nor a
built-in, so `infer`'s `var` arm throws its `SKIP:`-marked "unbound
variable" error. `Compare.inferModule` must route this to `.skip`
("out of modeled fragment: ..."), NOT `.reject` — march may well have
accepted this program via a stdlib/cross-module name A2 simply has no
model for; that's a coverage gap, not a disagreement. -/
private def unboundVarTerm : Term := Term.var "undefinedName" dSpan dTy0
private def mSkipUnbound : Module :=
  { decls := [.dlet "z" unboundVarTerm], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mSkipUnbound
  IO.println s!"skip-unbound-case: {repr r}"
-- expected: skip-unbound-case: OracleVerdict.skip "out of modeled fragment: SKIP: unbound variable `undefinedName`"

/-- `let x : Int = true in x` — a genuine type error: the binding
annotation `Int` contradicts the rhs literal `true : Bool`, so `infer`'s
`let_` arm's `unify (rhsTy) (annotTy)` throws an UNMARKED (no `SKIP:`
prefix) unification-mismatch error. This must stay `.reject "infer: ..."`
— it is a real disagreement about a type, not an unmodeled name/
constructor, and must never be misclassified as a skip. -/
private def badAnnotLet : Term :=
  Term.let_ "x" .unrestricted (some (Ty.con "Int" []))
    (Term.lit (.bool true) dTy0) (Term.var "x" dSpan dTy0) dTy0
private def mRejectAnnotMismatch : Module :=
  { decls := [.dlet "z" badAnnotLet], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mRejectAnnotMismatch
  IO.println s!"reject-annot-mismatch-case: {repr r}"
-- expected: reject-annot-mismatch-case: OracleVerdict.reject "infer: ..."

/-! ### The non-tail-recursion accept gate

Fixtures for `nonTailRecursionGate` (see its section doc). Each shape below was
also run end-to-end against the real march binary; the quoted march verdict is
the observed one, and every `march=1` was confirmed to carry march's tail-call
diagnostic (`recursive call to 'X' is not in tail position`), not a parse or
unbound-name error. -/

private def iTy : Ty := Ty.con "Int" []
private def sp (k : Nat) : Span := ⟨"t", k, 0, k, 1⟩
private def vI (n : String) (k : Nat) : Term := Term.var n (sp k) iTy
private def lit1 : Term := Term.lit (.int 1) iTy
/-- `a + b`. The `+` callee node carries a non-arrow `resolved_ty`, exactly the
operator quirk `termSpanTys` already excludes from the cross-check. -/
private def plusT (k : Nat) (a b : Term) : Term :=
  Term.app (Term.var "+" (sp k) iTy) [a, b] iTy
/-- `f(arg)`. -/
private def call1 (f : String) (k : Nat) (arg : Term) : Term :=
  Term.app (Term.var f (sp k) iTy) [arg] iTy
/-- `fn <name>(n : Int) : Int do <body> end`. -/
private def fnI (name : String) (body : Term) : Decl :=
  .dfn .pub name [("n", .unrestricted, some iTy)] (some iTy) body

/-- SELF-RECURSION, non-tail. `fn loopy(n : Int) : Int do loopy(n + 1) + 1 end`.
march REJECTS (`recursive call to 'loopy' is not in tail position`). This was a
false accept BEFORE the forward-reference work too — self-recursion never needed
the pre-pass — and the gate closes it. -/
private def mGateSelf : Module :=
  { decls := [fnI "loopy" (plusT 10 (call1 "loopy" 11 (plusT 12 (vI "n" 13) lit1)) lit1)],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mGateSelf
  IO.println s!"gate-self-nontail: {repr r}"
-- expected: gate-self-nontail: OracleVerdict.skip "out of modeled fragment: `loopy` uses ..."

/-- MUTUAL RECURSION, non-tail. `fn a(n) do b(n + 1) + 1 end` /
`fn b(n) do a(n + 1) + 1 end`. march REJECTS. Reachable only since the
ground-signature pre-pass made the pair inferable at all; without the gate this
was a confident ACCEPT on a program march rejects. -/
private def mGateMutual : Module :=
  { decls := [fnI "a" (plusT 20 (call1 "b" 21 (plusT 22 (vI "n" 23) lit1)) lit1),
              fnI "b" (plusT 24 (call1 "a" 25 (plusT 26 (vI "n" 27) lit1)) lit1)],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mGateMutual
  IO.println s!"gate-mutual-nontail: {repr r}"
-- expected: gate-mutual-nontail: OracleVerdict.skip "out of modeled fragment: `a` uses ..."

/-- The gate must NOT fire on a tail-safe recursive group. `fn a(n) do b(n) end`
/ `fn b(n) do a(n) end`: every recursive call is the whole body, hence in tail
position. march accepts the corresponding program, and so must this. -/
private def mGateTailSafe : Module :=
  { decls := [fnI "a" (call1 "b" 30 (vI "n" 31)),
              fnI "b" (call1 "a" 32 (vI "n" 33))],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mGateTailSafe
  IO.println s!"gate-tailsafe: {repr r}"
-- expected: gate-tailsafe: OracleVerdict.accept

/-- SCOPING — the load-bearing half. A function that is not itself recursive is
never gated, however it calls a recursive one. `fn user(n) do count(n) + 1 end`
calls the (tail-safe, self-recursive) `count` from a non-tail position; march
does not flag that, because `check_tail_position` is only ever applied to
members of a recursive group with that group as `rec_set`
(`typecheck.ml:10943-10965`). Were the gate not scoped the same way, the
overwhelmingly common `fn main() do println(int_to_string(helper(x))) end`
would skip and the corpus baseline would collapse. -/
private def mGateScoping : Module :=
  { decls := [fnI "count" (call1 "count" 40 (vI "n" 41)),
              fnI "user" (plusT 42 (call1 "count" 43 (vI "n" 44)) lit1)],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mGateScoping
  IO.println s!"gate-scoping: {repr r}"
-- expected: gate-scoping: OracleVerdict.accept

/-- The gate must never MASK a reject. Same non-tail mutual shape as
`mGateMutual`, but `a` is called with a `Bool`: a genuine type error. The gate
runs only after inference has succeeded, so this must still be
`.reject`, not `.skip` — tail position is irrelevant once the program is
independently known to be ill-typed. -/
private def mGateRejectStillWins : Module :=
  { decls := [fnI "a" (plusT 50 (call1 "b" 51 (vI "n" 52)) lit1),
              fnI "b" (call1 "a" 53 (Term.lit (.bool true) (Ty.con "Bool" [])))],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mGateRejectStillWins
  IO.println s!"gate-reject-still-wins: {repr r}"
-- expected: gate-reject-still-wins: OracleVerdict.reject "infer: ..."

/-! #### The structural-decrease whitelist

`fn f(n) do f(n - 1) … end` is non-tail but march proves the decrease and only
WARNS, so it must NOT be gated. `specs/lang/grammar/parse/p15` (the desugared
multi-head `fib`) is the real-corpus instance: blanket gating regressed it from
MATCH to SKIP, which is what motivated the whitelist. -/

/-- `a - b`. -/
private def minusT (k : Nat) (a b : Term) : Term :=
  Term.app (Term.var "-" (sp k) iTy) [a, b] iTy
private def litN (v : Int) : Term := Term.lit (.int v) iTy

/-- `n * fact(n - 1)` — non-tail, but the argument decreases, so march WARNS and
accepts, and the gate must not fire. -/
private def mDecFact : Module :=
  { decls := [fnI "fact"
      (Term.app (Term.var "*" (sp 60) iTy)
        [vI "n" 61, call1 "fact" 62 (minusT 63 (vI "n" 64) (litN 1))] iTy)],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mDecFact
  IO.println s!"dec-fact: {repr r}"
-- expected: dec-fact: OracleVerdict.accept

/-- The `p15` shape: a merged multi-head `fn`, i.e. one synthetic parameter
`__arg0`, a `match` on it, and the recursive arm binding `n` via `PatVar`. `n`
is therefore NOT a parameter — it only counts because march's `smaller` set
grows at a match on a parameter (`typecheck.ml:10812-10824`), which
`hasNonTailRecUse`'s `match_` arm mirrors. Deleting that mirroring makes this
fixture skip, and takes p15 with it. -/
private def mDecFib : Module :=
  { decls := [.dfn .pub "fib" [("__arg0", .unrestricted, some iTy)] (some iTy)
      (Term.match_ (vI "__arg0" 70)
        [(Pattern.lit (.int 0), none, litN 0),
         (Pattern.var "n" .unrestricted, none,
           plusT 71 (call1 "fib" 72 (minusT 73 (vI "n" 74) (litN 1)))
                    (call1 "fib" 75 (minusT 76 (vI "n" 77) (litN 2))))]
        iTy)],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mDecFib
  IO.println s!"dec-fib: {repr r}"
-- expected: dec-fib: OracleVerdict.accept

/-- Shadowing has teeth: same body as `mDecFib`, but the arm variable is bound
by a `match` on something that is NOT in the decrease base (a literal), so `n`
never joins it and the call is gated. Pins that the base really is consulted
rather than every `PatVar` being trusted. -/
private def mDecFibNoBase : Module :=
  { decls := [.dfn .pub "fib2" [("__arg0", .unrestricted, some iTy)] (some iTy)
      (Term.match_ (litN 7)
        [(Pattern.var "n" .unrestricted, none,
           plusT 78 (call1 "fib2" 79 (minusT 80 (vI "n" 81) (litN 1))) (litN 0))]
        iTy)],
    schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mDecFibNoBase
  IO.println s!"dec-fib-no-base: {repr r}"
-- expected: dec-fib-no-base: OracleVerdict.skip ...

/- `isRecognisedDecrease` at its edges, with `n` in the base and `q` not.
Recognised: `n - 1`. Not recognised, each for its own reason: `n - 0` (`k` must
be positive — march WOULD accept this, we over-gate), `n + 1` (wrong operator),
`n - m` (`k` not a literal), `q - 1` (`q` not in the base), and a bare `n`
(march's rule 1, deliberately not implemented). -/
#eval show IO Unit from do
  let base := ["n"]
  let r := [ isRecognisedDecrease base (minusT 1 (vI "n" 2) (litN 1)),
             isRecognisedDecrease base (minusT 1 (vI "n" 2) (litN 0)),
             isRecognisedDecrease base (plusT 1 (vI "n" 2) (litN 1)),
             isRecognisedDecrease base (minusT 1 (vI "n" 2) (vI "m" 3)),
             isRecognisedDecrease base (minusT 1 (vI "q" 2) (litN 1)),
             isRecognisedDecrease base (vI "n" 2) ]
  IO.println s!"dec-shapes: {r}"
-- expected: dec-shapes: [true, false, false, false, false, false]

/- `recursiveGroups` directly: `count` is its own one-member group (a direct
self-call), while `user` — which only calls into it — is not recursive and gets
the empty group that disables gating. -/
#eval show IO Unit from do
  let g := recursiveGroups mGateScoping.decls
  IO.println s!"gate-groups: {repr g}"
-- expected: gate-groups: [("count", ["count"]), ("user", [])]

end MarchLean.Compare.Test
