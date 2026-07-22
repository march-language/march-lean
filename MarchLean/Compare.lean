import MarchLean.Syntax
import MarchLean.Result
import MarchLean.Infer
import MarchLean.Check

/-!
# `MarchLean.Compare`

Up-to-equivalence comparison of A2's independently-inferred types
(`Infer.MTy`, from `Infer.inferModule'`) against march's own per-node
`resolved_ty` (`Syntax.Ty`), plus `inferModule : Module → IO CheckResult`,
the A2 replacement for A1's `Check.checkModule` (Task 7's `main` composes
directly with this, exactly as it already does with `Check.checkModule` /
`Linearity.checkLinearity`).

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
  | .let_ _ _ rhs body _ => termSpanTys env false rhs ++ termSpanTys env false body
  | .letfn _ _ _ fnBody body _ => termSpanTys env false fnBody ++ termSpanTys env false body
  | .ite c t e _ => termSpanTys env false c ++ termSpanTys env false t ++ termSpanTys env false e
  | .con _ args _ => (args.map (termSpanTys env false)).foldl (· ++ ·) []
  | .tuple es _ => (es.map (termSpanTys env false)).foldl (· ++ ·) []
  | .record fs _ => (fs.map (fun (_, e) => termSpanTys env false e)).foldl (· ++ ·) []
  | .field r _ span ty =>
      (if isCallee && !isArrowShaped env ty then [] else [(span, ty)]) ++ termSpanTys env false r
  | .match_ scrut arms _ =>
      termSpanTys env false scrut ++
        (arms.map (fun (_, body) => termSpanTys env false body)).foldl (· ++ ·) []
  | .unsupported _ => []

/-- `termSpanTys`, dispatched over one declaration (`dtype` carries no
terms). A decl's own top-level body is never itself a callee. -/
def declSpanTys (env : TyEnv) : Decl → List (Span × Ty)
  | .dtype .. => []
  | .dlet _ body => termSpanTys env false body
  | .dfn _ _ body => termSpanTys env false body
  | .unsupported => []

/-- Every `(span, resolved_ty)` pair for every `var`/`field` node in the
whole module — the lookup table `inferModule` diffs A2's recorded
`(span, MTy)` output against. `env` is the module's datatype environment
(the same one `inferModule` already builds via `buildTyEnv`, passed in
rather than recomputed). -/
def moduleSpanTys (env : TyEnv) (m : Module) : List (Span × Ty) :=
  (m.decls.map (declSpanTys env)).foldl (· ++ ·) []

/-- `inferModule m`: A2's independent-inference replacement for A1's
`Check.checkModule`. `IO CheckResult` (not a pure `CheckResult`) because
`Infer.inferModule'` runs in `IO` (the `Supply` metavariable arena is
backed by `IO.Ref`s) — this composes directly with `MarchLeanCheck`'s
already-`IO` `main` (Task 7), exactly as that `main` already composes
with `Check.checkModule` / `Linearity.checkLinearity` today.

1. Whole-file skip gate: any out-of-fragment construct in a declaration
   (`Decl.hasUnsupported`, transitively covers every subterm/pattern/type),
   or any scheme carrying a `CInterface` constraint that is not
   `Num`/`Eq`/`Ord` (reusing A1's `Check.constraintOutOfFragment` — same
   judgment call, no need to re-derive it).
2. Run `Infer.inferModule'` in `IO`; a `throw` (a genuine inference
   failure — march accepted this AST but A2's independent engine cannot
   type it) is `.reject`.
3. For every recorded `(span, MTy)`, look up that node's `resolved_ty`
   (`moduleSpanTys`) and `eqvTy` them (fresh per-node bijection); any
   disagreement is `.reject`.
4. Otherwise `.ok`.

Linearity is checked by a separate pass (`Linearity.checkLinearity`,
run by Task 7's `main`), not here. -/
def inferModule (m : Module) : IO CheckResult := do
  -- (1) whole-file skip gate: any out-of-fragment construct anywhere.
  if m.decls.any Decl.hasUnsupported then
    return .skip "out-of-fragment construct in a declaration"
  -- (1b) skip gate: a scheme carrying a non-Num/Eq/Ord CInterface (as A1).
  if m.schemes.any (fun sch => sch.constraints.any MarchLean.Check.constraintOutOfFragment) then
    return .skip "scheme carries an out-of-fragment constraint"
  -- (2) run the independent inference engine.
  let s ← Supply.new
  match ← (inferModule' s m).run with
  | .error e => return .reject s!"MISMATCH (infer): {e}"
  | .ok recorded =>
    -- (3) cross-check every recorded var/field node against march's resolved_ty.
    let env := buildTyEnv m.decls
    let spanTys := moduleSpanTys env m
    for (span, mty) in recorded do
      match spanTys.find? (fun p => p.1 == span) with
      | none => pure ()   -- defensive: no module node carries this span
      | some (_, ty) =>
        let bij ← IO.mkRef ([] : List (Nat × Int))
        -- `mty` is already zonked by `inferModule'` (it zonks every recorded
        -- node type before returning); no need to zonk again here.
        if !(← eqvTy bij env mty ty) then
          return .reject s!"MISMATCH (type) at {repr span}"
    -- (4) all recorded nodes agree.
    return .ok

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
private def idLam : Term := Term.lam [("x", .unrestricted)] (Term.var "x" innerSpan innerVarTy) dTy0
private def useSpan : Span := ⟨"t", 2, 1, 2, 4⟩
private def idArrowTy : Ty := Ty.arrow (Ty.var 7) (Ty.var 7)
private def useBodyOk : Term := Term.var "id" useSpan idArrowTy
private def letTermOk : Term := Term.let_ "id" .unrestricted idLam useBodyOk dTy0
private def mOk : Module := { decls := [.dlet "top" letTermOk], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mOk
  IO.println s!"ok-case: {repr r}"
-- expected: ok-case: CheckResult.ok

/-- Same module, but "id"'s use-site `resolved_ty` structurally contradicts
what A2 infers (`Bool` instead of an arrow) — a deliberate node-type
disagreement. -/
private def useBodyBad : Term := Term.var "id" useSpan (Ty.con "Bool" [])
private def letTermBad : Term := Term.let_ "id" .unrestricted idLam useBodyBad dTy0
private def mRejectType : Module := { decls := [.dlet "top" letTermBad], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mRejectType
  IO.println s!"reject-type-case: {repr r}"
-- expected: reject-type-case: CheckResult.reject "MISMATCH (type) at ..."

/-- A module with an `unsupported` decl forces `.skip`. -/
private def mSkip : Module := { decls := [.unsupported], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mSkip
  IO.println s!"skip-case: {repr r}"
-- expected: skip-case: CheckResult.skip ...

/-- A scheme carrying a non-`Num`/`Eq`/`Ord` `CInterface` (a user typeclass)
also forces `.skip`, before inference is even attempted (as A1). -/
private def mSkipInterface : Module :=
  { decls := [.dlet "x" (Term.var "f" dSpan (Ty.con "Int" []))],
    schemes := [{ ids := [0], constraints := [Constraint.interface "Show" (Ty.var 0)], body := Ty.var 0 }],
    insts := [] }

#eval show IO Unit from do
  let r ← inferModule mSkipInterface
  IO.println s!"skip-interface-case: {repr r}"
-- expected: skip-interface-case: CheckResult.skip ...

/-- A module march (hypothetically) accepted but that A2's independent
engine cannot type: applying an `Int` literal as if it were a function.
`unify` hits its `con`-vs-`arrow` shape mismatch and `throw`s, which
`inferModule` maps to `.reject "MISMATCH (infer): ..."`. -/
private def badAppTerm : Term :=
  Term.app (Term.lit (.int 1) dTy0) [Term.lit (.int 2) dTy0] dTy0
private def mRejectInfer : Module := { decls := [.dlet "z" badAppTerm], schemes := [], insts := [] }

#eval show IO Unit from do
  let r ← inferModule mRejectInfer
  IO.println s!"reject-infer-case: {repr r}"
-- expected: reject-infer-case: CheckResult.reject "MISMATCH (infer): ..."

end MarchLean.Compare.Test
