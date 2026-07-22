import MarchLean.Syntax
import MarchLean.Elab

/-!
# `MarchLean.Check`

The A1 checker's brain: verify march's elaboration by **substitution + equality**,
never by re-running unification/inference.

`checkModule : Syntax.Module → CheckResult` returns:
- `.ok`     — every checked node's `resolved_ty` is consistent with its subterms
              and every instantiation witness substitutes to the recorded use type;
- `.reject` — a genuine A1 disagreement (a well-typed march program would not
              produce this AST), surfaced to the CLI as exit 1;
- `.skip`   — the module (or a construct in it) is out of the A1 fragment, so we
              honestly decline rather than risk a false accept.

## Design (mirrors the A1 elaboration-checker design doc)

1. **Whole-file skip gate.** If ANY decl `.hasUnsupported` (Task 2: covers
   unsupported nodes/subterms/patterns/types), OR any scheme carries a
   `CInterface` whose name is NOT `Num`/`Eq`/`Ord`, the whole module is `.skip`.
   (Application and lambda are now modeled N-ARILY — matching march's `EApp of
   expr * expr list` and `ELam`/`DFn` param lists — so no synthetic intermediate
   nodes with `Ty.unsupported` are invented; a 2-arg application no longer trips
   this gate.)

   A crucial invariant falls out of this gate: **by the time `checkTerm` runs,
   every node in every decl is free of `Ty.unsupported`** — so the structural
   rules below never meet an unknown type and never need defensive skips for it.

2. **Instantiation checking.** For each `EVar`/`EField` use with an
   `instantiations` entry (joined to its `schemes` entry by `ids` equality),
   `substTy (ids.zip args) scheme.body` is the identifier's authoritative
   monomorphic type. The join + constraint + arity validation lives in
   `checkInstantiations`; the use-site *type* is verified where the identifier is
   used: if it is the callee of an application, its substituted scheme body is
   peeled against the argument list (app arm) — this is the authoritative path,
   because the emitter annotates an *operator* callee node with the application's
   RESULT type (e.g. `n > m`'s `>` node carries `Bool`, not `Int → Int → Bool`),
   so the callee node's own `resolved_ty` is NOT reliably the function type. A
   var used in non-callee position (a polymorphic value) is checked in the `var`
   arm by `substTy body == node.ty`. No scheme for an instantiation's ids ⇒
   `.skip` (defensive; the emitter guarantees pairing).

3. **Constraint checking by interface NAME.** march emits the primitive
   `Num`/`Eq`/`Ord` constraints as `CInterface "Num"/"Eq"/"Ord"` (there is NO
   `CEq`), and sometimes as the direct `CNum`/`COrd` tags. `checkConstraint`
   switches on the NAME: `"Num"`→numeric-primitive, `"Ord"`→ordered-primitive,
   `"Eq"`→accept, any OTHER `CInterface` name → skip (user typeclass). A blanket
   "any `CInterface` ⇒ skip" would gut the arithmetic/comparison fragment.

4. **Canonical type equality.** A named record type and its structural form
   denote the same type, so we expand named records through the `DType`
   environment before `Ty.beq`. (In practice Task 3 decodes `TDRecord` to
   `Decl.unsupported` — which trips the skip gate — so no record-expansion path
   is reachable from the current decoder; `canon` still recurses structurally so
   nested types normalize, and variant ADTs stay nominal, compared by name+args.)

5. **Per-node structural rules (bidirectional).** Each node's `resolved_ty` must
   be consistent with its subterms: app (peel the callee's arrow chain — its
   substituted scheme body when instantiated, else its `resolved_ty` — against
   the args list: each domain == the matching arg's ty, final codomain == node.ty),
   ite (cond == Bool, both branches == node.ty), con (node.ty
   is the ctor's datatype applied, declared arg types matched under the derived
   param substitution), tuple/record/field (componentwise), lam/let/letfn/match
   (recurse + result-type agreement), lit (no sub-check).
-/

namespace MarchLean.Check

open MarchLean.Syntax

inductive CheckResult where
  | ok
  | reject (msg : String)
  | skip (reason : String)
  deriving Repr, Inhabited

/-- Sequence two checks: run the continuation only if the first is `.ok`,
otherwise short-circuit with the first non-`ok` result. -/
def CheckResult.andThen : CheckResult → (Unit → CheckResult) → CheckResult
  | .ok, f => f ()
  | other, _ => other

/-- First non-`ok` result in a list, or `.ok` if all are `ok`. -/
def firstBad (rs : List CheckResult) : CheckResult :=
  rs.foldl (fun acc r => match acc with | .ok => r | bad => bad) CheckResult.ok

/-- Datatype environment: name → (type-param names, constructor sigs). Built
from `Decl.dtype`; used to canonicalize named types and to type ADT ctors. -/
abbrev TyEnv := List (String × (List String × List CtorSig))

def buildTyEnv (decls : List Decl) : TyEnv :=
  decls.foldr (fun d acc =>
    match d with
    | .dtype n ps ctors => (n, (ps, ctors)) :: acc
    | _ => acc) []

/-- Find a constructor by name across all datatypes: returns the owning
datatype name, its type-param names, and the ctor signature. -/
def findCtor (env : TyEnv) (name : String) : Option (String × List String × CtorSig) :=
  env.findSome? (fun (dn, params, ctors) =>
    (ctors.find? (fun c => c.name == name)).map (fun c => (dn, params, c)))

/-- Substitute type arguments for quantified ids in a type. -/
partial def substTy (s : List (Int × Ty)) : Ty → Ty
  | .var id => match s.lookup id with | some t => t | none => .var id
  | .con n args => .con n (args.map (substTy s))
  | .arrow a b => .arrow (substTy s a) (substTy s b)
  | .tuple ts => .tuple (ts.map (substTy s))
  | .record fs => .record (fs.map (fun (n, t) => (n, substTy s t)))
  | .lin l t => .lin l (substTy s t)
  | .natOp o a b => .natOp o (substTy s a) (substTy s b)
  | t => t

/-- Canonicalize a type before equality: recurse structurally so nested types
normalize. Named records would expand to their structural form here, but Task 3
maps `TDRecord`/aliases to `Decl.unsupported` (skip-gated), so `TCon`s reaching
this point are nominal (variant ADTs / primitives) and are left as-is (recursing
into their args). -/
partial def canon (env : TyEnv) : Ty → Ty
  | .con n args => .con n (args.map (canon env))
  | .arrow a b => .arrow (canon env a) (canon env b)
  | .tuple ts => .tuple (ts.map (canon env))
  | .record fs => .record (fs.map (fun (n, t) => (n, canon env t)))
  | .lin l t => .lin l (canon env t)
  | .natOp o a b => .natOp o (canon env a) (canon env b)
  | t => t

/-- Canonical type equality (§4). -/
def tyEq (env : TyEnv) (a b : Ty) : Bool := (canon env a).beq (canon env b)

/-- Decompose a type into `(domain, codomain)` if it is arrow-shaped, peeling
any leading linearity qualifier (`T ⊸ U` is still an arrow underneath). -/
partial def asArrow (env : TyEnv) (t : Ty) : Option (Ty × Ty) :=
  match canon env t with
  | .arrow a b => some (a, b)
  | .lin _ inner => asArrow env inner
  | _ => none

/-- Peel `fty`'s arrow chain against an N-ary application's `args` left-to-right:
each successive domain must `tyEq` the corresponding arg's ty, and the final
codomain (after all args) must `tyEq` the node's `expected` result type.

`nonArrowSkip` controls the "callee type is not an arrow" outcome: when the
callee's type comes from an authoritative instantiation witness (a real function
type) a non-arrow is a genuine disagreement (`.reject`); but when the callee type
is a node's own `resolved_ty` and there is NO witness, a non-arrow is exactly the
operator-result-type quirk (the emitter annotates an operator callee with the
application's RESULT type), which we cannot verify without a witness → `.skip`,
never a false `.reject`. Domain/codomain `tyEq` mismatches always `.reject`. -/
partial def checkAppChain (env : TyEnv) (expected : Ty) (nonArrowSkip : Bool) : Ty → List Term → CheckResult
  | fty, [] =>
      if tyEq env fty expected then .ok
      else .reject s!"application result type {repr (canon env fty)} ≠ node type {repr (canon env expected)}"
  | fty, a :: rest =>
      match asArrow env fty with
      | some (dom, cod) =>
          if tyEq env dom a.ty then checkAppChain env expected nonArrowSkip cod rest
          else .reject s!"application argument type mismatch: fn expects {repr (canon env dom)} but arg is {repr (canon env a.ty)}"
      | none =>
          if nonArrowSkip then
            .skip s!"callee has a non-arrow (result-type) annotation {repr (canon env fty)} and no instantiation witness; cannot verify"
          else .reject s!"applying a non-function of type {repr (canon env fty)}"

/-- Peel exactly `n` arrows off `t`, returning the remaining codomain. Used to
recover a lambda's body type from its N-ary function `resolved_ty`. -/
partial def peelArrows (env : TyEnv) : Nat → Ty → Option Ty
  | 0, t => some t
  | n + 1, t =>
      match asArrow env t with
      | some (_, cod) => peelArrows env n cod
      | none => none

/-- `Num`: satisfied by numeric primitives (or a still-free var). -/
def numOk (env : TyEnv) (t : Ty) : Option (Sum String String) :=
  match canon env t with
  | .con "Int" [] | .con "Float" [] | .var _ => none
  | other => some (.inr s!"Num not satisfied by {repr other}")

/-- `Ord`: satisfied by the ordered primitives (or a still-free var). -/
def ordOk (env : TyEnv) (t : Ty) : Option (Sum String String) :=
  match canon env t with
  | .con "Int" [] | .con "Float" [] | .con "String" [] | .con "Bool" [] | .var _ => none
  | other => some (.inr s!"Ord not satisfied by {repr other}")

/-- Constraint check for the classes A1 models. `none` = satisfied;
`some (.inl r)` = out-of-fragment (skip); `some (.inr r)` = violated (reject).
Switches `CInterface` on the NAME (see design §3). -/
def checkConstraint (env : TyEnv) : Constraint → Option (Sum String String)
  | .interface "Num" t => numOk env t
  | .interface "Ord" t => ordOk env t
  | .interface "Eq" _ => none
  | .interface n _ => some (.inl s!"CInterface {n} (user typeclass) out of fragment")
  | .num t => numOk env t
  | .ord t => ordOk env t
  | .eqC _ => none
  -- H2: an ADT/nat bound is not something A1 verifies; honest-skip rather than
  -- silently auto-satisfy an unchecked bound.
  | .adtBound n _ => some (.inl s!"CADTBound {n} out of fragment")
  | .tnatBound _ => some (.inl "CTNatBound out of fragment")
  | .unsupported => some (.inl "unsupported constraint")

/-- Apply a type substitution to a constraint's carried type. -/
def substConstraint (s : List (Int × Ty)) : Constraint → Constraint
  | .num t => .num (substTy s t)
  | .ord t => .ord (substTy s t)
  | .eqC t => .eqC (substTy s t)
  | .interface n t => .interface n (substTy s t)
  | .adtBound n t => .adtBound n (substTy s t)
  | .tnatBound t => .tnatBound (substTy s t)
  | .unsupported => .unsupported

/-- Is this scheme constraint out of the A1 fragment (a user `CInterface`, or
an `unsupported` constraint)? Used by the whole-file skip gate. -/
def constraintOutOfFragment : Constraint → Bool
  | .interface "Num" _ | .interface "Ord" _ | .interface "Eq" _ => false
  | .interface _ _ => true
  | .unsupported => true
  | _ => false

/-- H4: does this constraint carry an `unsupported` type anywhere (independently
of whether its *class* is in-fragment)? A `Num`/`Ord`/`Eq` bound over an
out-of-fragment type should still make the file honest-skip, so the numeric /
ordered predicate never runs on a type outside our knowledge. -/
def constraintCarriesUnsupported : Constraint → Bool
  | .num t | .ord t | .eqC t | .interface _ t | .adtBound _ t | .tnatBound t => t.hasUnsupported
  | .unsupported => true

/-- Validate every instantiation against its scheme (joined by `ids`): arity,
plus each constraint under the instantiation's args. The use-site *equality*
check is done in `checkTerm`'s `var` arm, where the annotation is in scope. -/
def checkInstantiations (env : TyEnv) (m : Module) : CheckResult := Id.run do
  for inst in m.insts do
    match m.schemes.find? (fun s => s.ids == inst.ids) with
    | none => return .skip s!"instantiation at {repr inst.useSpan} has no scheme"
    | some sch =>
      if sch.ids.length != inst.args.length then
        return .reject s!"instantiation arity mismatch at {repr inst.useSpan}"
      let s := sch.ids.zip inst.args
      for c in sch.constraints do
        match checkConstraint env (substConstraint s c) with
        | some (.inl r) => return .skip r
        | some (.inr r) => return .reject r
        | none => pure ()
  return .ok

/-- Per-node checker. Every `Term` constructor has an explicit arm — there is
NO `| _ => .ok` catch-all (that would vacuously accept unmodeled nodes). Post
skip-gate, no node's `ty` is `Ty.unsupported`, so the structural rules operate
on real resolved types. -/
partial def checkTerm (env : TyEnv) (m : Module) (insts : List Instantiation) : Term → CheckResult
  -- H1: verify a literal's value against its annotation, but CONSERVATIVELY.
  -- Reject ONLY on a definitive primitive-vs-primitive contradiction; `.ok` on
  -- any ambiguity (var / unsupported / non-primitive TCon / tuple / record /
  -- arrow), so this rule can never false-reject a legitimately-typed literal.
  | .lit l ty =>
      let ct := canon env ty
      match l with
      -- int literals are Num-polymorphic (can resolve to Int OR Float);
      -- reject only a different concrete primitive.
      | .int _ =>
          match ct with
          | .con "Bool" [] | .con "String" [] => .reject s!"int literal annotated {repr ct}"
          | _ => .ok
      | .bool _ =>
          match ct with
          | .con "Int" [] | .con "Float" [] | .con "String" [] => .reject s!"bool literal annotated {repr ct}"
          | _ => .ok
      | .str _ =>
          match ct with
          | .con "Int" [] | .con "Float" [] | .con "Bool" [] => .reject s!"string literal annotated {repr ct}"
          | _ => .ok
      | .float _ =>
          match ct with
          | .con "Bool" [] | .con "String" [] => .reject s!"float literal annotated {repr ct}"
          | _ => .ok
      -- unit's type shape varies; don't risk it.
      | .unit => .ok
  | .var _ span ty =>
      -- Reached for a var in NON-callee position (a polymorphic *value*). A var
      -- in callee position is handled inline by the `app` arm, which uses the
      -- substituted scheme body rather than this node's `resolved_ty` (unreliable
      -- for operators — see design §2).
      match insts.find? (fun i => i.useSpan == span) with
      | none => .ok   -- monomorphic use: the annotation stands on its own
      | some inst =>
        match m.schemes.find? (fun s => s.ids == inst.ids) with
        | none => .skip s!"no scheme for instantiation at {repr span}"
        | some sch =>
          let expected := substTy (sch.ids.zip inst.args) sch.body
          if tyEq env expected ty then .ok
          else .reject s!"instantiation type mismatch at {repr span}: witness gives {repr (canon env expected)} but node is annotated {repr (canon env ty)}"
  | .app f args ty =>
      (firstBad (args.map (checkTerm env m insts))).andThen fun _ =>
        -- The function type to peel against `args`. When the callee is an
        -- identifier WITH an instantiation, its authoritative monomorphic type
        -- is the witness-substituted scheme body — NOT the fn node's own
        -- `resolved_ty`, which the emitter fills with the *result* type for
        -- operator applications (e.g. `n > m`'s `>` node is annotated `Bool`,
        -- not `Int → Int → Bool`). Instantiation constraints are validated
        -- globally in `checkInstantiations`. For a non-identifier callee we
        -- recurse and use its real (arrow) `resolved_ty`.
        match f with
        | .var _ span _ =>
            match insts.find? (fun i => i.useSpan == span) with
            | some inst =>
                match m.schemes.find? (fun s => s.ids == inst.ids) with
                -- Authoritative witness type: a non-arrow here is a genuine disagreement.
                | some sch => checkAppChain env ty false (substTy (sch.ids.zip inst.args) sch.body) args
                | none => .skip s!"no scheme for instantiation at {repr span}"
            -- No witness: the callee's own `resolved_ty` is unreliable for operators
            -- (result-type quirk), so a non-arrow head is skip-not-reject.
            | none => checkAppChain env ty true f.ty args
        | _ =>
            (checkTerm env m insts f).andThen fun _ =>
              checkAppChain env ty true f.ty args
  | .lam params body ty =>
      (checkTerm env m insts body).andThen fun _ =>
        -- One arrow per param off the node's own type; body.ty == the remainder.
        match peelArrows env params.length ty with
        | some cod =>
            if tyEq env body.ty cod then .ok
            else .reject s!"lambda body type {repr (canon env body.ty)} ≠ codomain {repr (canon env cod)}"
        | none => .skip s!"lambda node type not an arrow chain of length {params.length}: {repr (canon env ty)}"
  | .let_ _ _ rhs body ty =>
      (checkTerm env m insts rhs).andThen fun _ =>
      (checkTerm env m insts body).andThen fun _ =>
        if tyEq env body.ty ty then .ok
        else .reject s!"let body type {repr (canon env body.ty)} ≠ let node type {repr (canon env ty)}"
  | .letfn _ _ _ fnBody body ty =>
      (checkTerm env m insts fnBody).andThen fun _ =>
      (checkTerm env m insts body).andThen fun _ =>
        if tyEq env body.ty ty then .ok
        else .reject s!"letfn body type {repr (canon env body.ty)} ≠ letfn node type {repr (canon env ty)}"
  | .ite c t e ty =>
      (checkTerm env m insts c).andThen fun _ =>
      (checkTerm env m insts t).andThen fun _ =>
      (checkTerm env m insts e).andThen fun _ =>
        if !(tyEq env c.ty (Ty.con "Bool" [])) then .reject s!"if condition type {repr (canon env c.ty)} ≠ Bool"
        else if !(tyEq env t.ty ty) then .reject s!"if then-branch type {repr (canon env t.ty)} ≠ result {repr (canon env ty)}"
        else if !(tyEq env e.ty ty) then .reject s!"if else-branch type {repr (canon env e.ty)} ≠ result {repr (canon env ty)}"
        else .ok
  | .con name args ty =>
      (firstBad (args.map (checkTerm env m insts))).andThen fun _ =>
        match findCtor env name with
        | none => .skip s!"constructor {name} not declared in this module's datatype env"
        | some (dn, params, csig) =>
          match canon env ty with
          | .con dn2 tyArgs =>
              if dn2 != dn then .reject s!"constructor {name} builds {dn} but node type is {dn2}"
              else if tyArgs.length != params.length then
                .reject s!"constructor {name} result arity mismatch"
              else if args.length != csig.argTys.length then
                .reject s!"constructor {name} applied to {args.length} args but declares {csig.argTys.length}"
              else
                let psub := ((List.range params.length).map Int.ofNat).zip tyArgs
                let expected := csig.argTys.map (substTy psub)
                if (args.zip expected).all (fun (a, et) => tyEq env a.ty et) then .ok
                else .reject s!"constructor {name} argument type mismatch"
          | other => .skip s!"constructor {name} node type not a datatype application: {repr other}"
  | .tuple elems ty =>
      (firstBad (elems.map (checkTerm env m insts))).andThen fun _ =>
        match canon env ty with
        | .tuple ts =>
            if elems.length == ts.length && (elems.zip ts).all (fun (e, t) => tyEq env e.ty t) then .ok
            else .reject "tuple component type mismatch"
        | other => .skip s!"tuple node type not a tuple: {repr other}"
  | .record fields ty =>
      (firstBad (fields.map (fun (_, e) => checkTerm env m insts e))).andThen fun _ =>
        match canon env ty with
        | .record ftys =>
            if fields.length != ftys.length then .reject "record field-count mismatch"
            else if fields.all (fun (fn, e) =>
                match ftys.find? (fun (n, _) => n == fn) with
                | some (_, t) => tyEq env e.ty t
                | none => false) then .ok
            else .reject "record field type mismatch"
        | other => .skip s!"record node type not a record: {repr other}"
  | .field record name _span ty =>
      (checkTerm env m insts record).andThen fun _ =>
        match canon env record.ty with
        | .record ftys =>
            match ftys.find? (fun (n, _) => n == name) with
            | some (_, t) => if tyEq env t ty then .ok else .reject s!"field {name} type {repr (canon env t)} ≠ node type {repr (canon env ty)}"
            | none => .reject s!"field {name} not present in record type"
        | other => .skip s!"field {name} target not a record type: {repr other}"
  | .match_ scrut arms ty =>
      (checkTerm env m insts scrut).andThen fun _ =>
      (firstBad (arms.map (fun (_, body) => checkTerm env m insts body))).andThen fun _ =>
        if arms.all (fun (_, body) => tyEq env body.ty ty) then .ok
        else .reject "match arm result type mismatch"
  | .unsupported _ => .skip "unsupported term"

/-- Dispatch each decl to `checkTerm`; `dtype` carries no terms. Explicit arm
per constructor — no catch-all. -/
def checkDecl (env : TyEnv) (m : Module) (insts : List Instantiation) : Decl → CheckResult
  | .dtype _ _ _ => .ok
  | .dlet _ body => checkTerm env m insts body
  | .dfn _ _ body => checkTerm env m insts body
  | .unsupported => .skip "unsupported decl"

/-- Whole-module check. -/
def checkModule (m : Module) : CheckResult := Id.run do
  -- (1) skip gate: any unsupported construct anywhere.
  for d in m.decls do
    if d.hasUnsupported then
      return .skip "out-of-fragment construct in a declaration"
  -- (1b) skip gate: any scheme constraint that is a user typeclass / unsupported.
  for s in m.schemes do
    for c in s.constraints do
      if constraintOutOfFragment c then
        return .skip "scheme carries an out-of-fragment constraint"
  -- (1c) H4: defense-in-depth — skip if a scheme's BODY carries an unsupported
  -- type, if any constraint's carried type is unsupported, or if an
  -- instantiation's args include an out-of-fragment type. This prevents a
  -- false-reject where numOk/ordOk (or a structural rule) would otherwise run
  -- on an instantiation arg / scheme body outside the A1 fragment.
  for s in m.schemes do
    if s.body.hasUnsupported then
      return .skip "scheme body carries an out-of-fragment type"
    for c in s.constraints do
      if constraintCarriesUnsupported c then
        return .skip "scheme constraint carries an out-of-fragment type"
  for i in m.insts do
    if i.args.any Ty.hasUnsupported then
      return .skip "instantiation carries an out-of-fragment type argument"
  let env := buildTyEnv m.decls
  -- (2/3) instantiation join + arity + constraints.
  match checkInstantiations env m with
  | .ok => pure ()
  | other => return other
  -- (2/5) per-decl structural + use-site equality checks.
  for d in m.decls do
    match checkDecl env m m.insts d with
    | .ok => pure ()
    | other => return other
  return .ok

end MarchLean.Check

-- Living tests (executable documentation; run at build time via `#eval`).
namespace MarchLean.Check.Test
open MarchLean.Syntax MarchLean.Check

/-- ∀a. a, used at Int with arg [Int], use-site annotation Int → matches → ok. -/
def sOk : Module :=
  { decls := [Decl.dlet "x" (Term.var "id" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))],
    schemes := [{ ids := [0], constraints := [], body := Ty.var 0 }],
    insts := [{ useSpan := ⟨"f",1,1,1,2⟩, ids := [0], args := [Ty.con "Int" []] }] }
#eval (repr (checkModule sOk))   -- expected: CheckResult.ok

/-- Same scheme+args but the annotation says Bool while body[a:=Int] = Int → reject. -/
def sBad : Module :=
  { decls := [Decl.dlet "x" (Term.var "id" ⟨"f",1,1,1,2⟩ (Ty.con "Bool" []))],
    schemes := [{ ids := [0], constraints := [], body := Ty.var 0 }],
    insts := [{ useSpan := ⟨"f",1,1,1,2⟩, ids := [0], args := [Ty.con "Int" []] }] }
#eval (repr (checkModule sBad))  -- expected: CheckResult.reject ...

/-- An unsupported subterm forces skip. -/
def sSkip : Module :=
  { decls := [Decl.dlet "x" (Term.unsupported Ty.unsupported)], schemes := [], insts := [] }
#eval (repr (checkModule sSkip)) -- expected: CheckResult.skip ...

/-- A user-typeclass constraint on a scheme forces skip. -/
def sUserClass : Module :=
  { decls := [Decl.dlet "x" (Term.var "f" ⟨"f",1,1,1,2⟩ (Ty.con "Int" []))],
    schemes := [{ ids := [0], constraints := [Constraint.interface "Show" (Ty.var 0)], body := Ty.var 0 }],
    insts := [{ useSpan := ⟨"f",1,1,1,2⟩, ids := [0], args := [Ty.con "Int" []] }] }
#eval (repr (checkModule sUserClass)) -- expected: CheckResult.skip ...

/-- A `Num` constraint violated by a non-numeric arg forces reject. -/
def sNumBad : Module :=
  { decls := [Decl.dlet "x" (Term.var "add" ⟨"f",1,1,1,2⟩ (Ty.con "Bool" []))],
    schemes := [{ ids := [0], constraints := [Constraint.interface "Num" (Ty.var 0)], body := Ty.var 0 }],
    insts := [{ useSpan := ⟨"f",1,1,1,2⟩, ids := [0], args := [Ty.con "Bool" []] }] }
#eval (repr (checkModule sNumBad)) -- expected: CheckResult.reject ...

end MarchLean.Check.Test

-- THE REAL GATE: decode each committed emitter sample and run `checkModule`.
-- Every ACCEPT sample must be `.ok` or `.skip` — NEVER `.reject` (a well-typed
-- accept program producing a MISMATCH would be a checker false-mismatch bug).
namespace MarchLean.Check.RealGate
open Lean MarchLean.Elab MarchLean.Syntax MarchLean.Check

def sampleDir : String := ".superpowers/sdd/samples/"

def acceptSamples : List String := [
  "accept_literals", "accept_poly", "accept_if_ord", "accept_adt",
  "accept_record", "accept_linear_let", "accept_linear_param" ]

def checkSampleFile (name : String) : IO CheckResult := do
  let contents ← IO.FS.readFile (sampleDir ++ name ++ ".json")
  match Json.parse contents with
  | .error e => pure (.reject s!"invalid JSON in {name}: {e}")
  | .ok j =>
    match decodeModule j with
    | .error e => pure (.reject s!"decode error in {name}: {e}")
    | .ok m => pure (checkModule m)

/-- Run the checker on every accept sample and assert none `.reject`s. -/
def runAcceptGate : IO Unit := do
  for name in acceptSamples do
    let r ← checkSampleFile name
    let tag := match r with
      | .ok => "OK"
      | .skip why => s!"SKIP ({why})"
      | .reject why => s!"REJECT !!! FALSE-MISMATCH BUG: {why}"
    IO.println s!"{name}: {tag}"

#eval runAcceptGate

-- The march-rejected sample, for completeness (not part of the accept gate).
#eval do
  let r ← checkSampleFile "reject_int_str"
  IO.println s!"reject_int_str: {repr r}"

end MarchLean.Check.RealGate
