/-!
# `MarchLean.Syntax`

Executable Lean mirror of march's core AST for the A1 fragment (Core +
linearity). Named variables (match march's AST 1:1). Every out-of-fragment
construct decodes to an `unsupported` escape so the checker can honest-skip
rather than crash. Each `Term` node carries its resolved type (from the
emitter's `resolved_ty`), so `Check` verifies annotations rather than
re-inferring.
-/
namespace MarchLean.Syntax

/-- Source span (used to key instantiations; equality is structural). -/
structure Span where
  file : String
  startLine : Nat
  startCol : Nat
  endLine : Nat
  endCol : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Linearity qualifier. -/
inductive Lin where
  | linear | affine | unrestricted
  deriving DecidableEq, Repr, Inhabited

/-- Resolved type (decoded from `resolved_ty`). `unsupported` marks an
out-of-fragment type constructor (e.g. a session channel). -/
inductive Ty where
  | con (name : String) (args : List Ty)
  | arrow (from_ : Ty) (to_ : Ty)
  | tuple (elems : List Ty)
  | record (fields : List (String × Ty))
  | var (id : Int)
  | lin (l : Lin) (ty : Ty)
  | nat (n : Nat)
  | natOp (op : String) (a : Ty) (b : Ty)
  | err
  | unsupported
  deriving Repr, Inhabited

/-- Does this type contain an `unsupported` node anywhere? -/
partial def Ty.hasUnsupported : Ty → Bool
  | .unsupported => true
  | .con _ args => args.any Ty.hasUnsupported
  | .arrow a b => a.hasUnsupported || b.hasUnsupported
  | .tuple ts => ts.any Ty.hasUnsupported
  | .record fs => fs.any (fun (_, t) => t.hasUnsupported)
  | .lin _ t => t.hasUnsupported
  | .natOp _ a b => a.hasUnsupported || b.hasUnsupported
  -- H3: a `TError` should never appear in accept output; if it does, honest-skip
  -- rather than check a file built on an elaboration error.
  | .err => true
  | .var _ | .nat _ => false

/-- Structural type equality (NOT canonical — `Check` canonicalizes named
records first, then calls this). -/
partial def Ty.beq : Ty → Ty → Bool
  | .con n1 a1, .con n2 a2 => n1 == n2 && a1.length == a2.length && (a1.zip a2).all (fun (x,y) => x.beq y)
  | .arrow a1 b1, .arrow a2 b2 => a1.beq a2 && b1.beq b2
  | .tuple t1, .tuple t2 => t1.length == t2.length && (t1.zip t2).all (fun (x,y) => x.beq y)
  | .record f1, .record f2 =>
      f1.length == f2.length && (f1.zip f2).all (fun ((n1,t1),(n2,t2)) => n1 == n2 && t1.beq t2)
  | .var i1, .var i2 => i1 == i2
  | .lin l1 t1, .lin l2 t2 => l1 == l2 && t1.beq t2
  | .nat n1, .nat n2 => n1 == n2
  | .natOp o1 a1 b1, .natOp o2 a2 b2 => o1 == o2 && a1.beq a2 && b1.beq b2
  | .err, .err => true
  | .unsupported, .unsupported => true
  | _, _ => false

instance : BEq Ty := ⟨Ty.beq⟩

/-- Typeclass constraint carried by a scheme. -/
inductive Constraint where
  | num (ty : Ty)
  | ord (ty : Ty)
  | eqC (ty : Ty)
  | interface (name : String) (ty : Ty)   -- out-of-fragment → skip trigger
  | adtBound (name : String) (ty : Ty)
  | tnatBound (ty : Ty)
  | unsupported
  deriving Repr, Inhabited

/-- Literal. -/
inductive Lit where
  | int (n : Int) | float (s : String) | str (s : String) | bool (b : Bool) | unit
  deriving Repr, Inhabited

/-- Pattern (for `match`/`let` binders). -/
inductive Pattern where
  | wild
  | var (name : String) (lin : Lin)
  | con (name : String) (args : List Pattern)
  | tuple (elems : List Pattern)
  | lit (l : Lit)
  | record (fields : List (String × Pattern))
  | as (name : String) (p : Pattern)
  | unsupported
  deriving Repr, Inhabited

/-- Does this pattern contain an `unsupported` node anywhere? -/
partial def Pattern.hasUnsupported : Pattern → Bool
  | .unsupported => true
  | .con _ args => args.any Pattern.hasUnsupported
  | .tuple ps => ps.any Pattern.hasUnsupported
  | .record fs => fs.any (fun (_, p) => p.hasUnsupported)
  | .as _ p => p.hasUnsupported
  | .wild | .var _ _ | .lit _ => false

/-- Term. Each node carries its resolved type `ty`. `var` and `field` also
carry their `span` (for the instantiation join). -/
inductive Term where
  | lit (l : Lit) (ty : Ty)
  | var (name : String) (span : Span) (ty : Ty)
  | app (fn : Term) (args : List Term) (ty : Ty)
  | lam (params : List (String × Lin)) (body : Term) (ty : Ty)
  | let_ (name : String) (lin : Lin) (rhs : Term) (body : Term) (ty : Ty)
  | letfn (name : String) (param : String) (lin : Lin) (fnBody : Term) (body : Term) (ty : Ty)
  | ite (cond : Term) (then_ : Term) (else_ : Term) (ty : Ty)
  | con (name : String) (args : List Term) (ty : Ty)
  | tuple (elems : List Term) (ty : Ty)
  | record (fields : List (String × Term)) (ty : Ty)
  | field (record : Term) (name : String) (span : Span) (ty : Ty)
  | match_ (scrut : Term) (arms : List (Pattern × Term)) (ty : Ty)
  | unsupported (ty : Ty)
  deriving Inhabited

/-- The type annotation on a term node. -/
def Term.ty : Term → Ty
  | .lit _ t | .var _ _ t | .app _ _ t | .lam _ _ t | .let_ _ _ _ _ t
  | .letfn _ _ _ _ _ t | .ite _ _ _ t | .con _ _ t | .tuple _ t
  | .record _ t | .field _ _ _ t | .match_ _ _ t | .unsupported t => t

/-- Is this term (or any subterm/type) out of fragment? -/
partial def Term.hasUnsupported : Term → Bool
  | .unsupported _ => true
  | t =>
    t.ty.hasUnsupported ||
    (match t with
     | .app f args _ => f.hasUnsupported || args.any Term.hasUnsupported
     | .lam _ b _ => b.hasUnsupported
     | .let_ _ _ r b _ => r.hasUnsupported || b.hasUnsupported
     | .letfn _ _ _ fb b _ => fb.hasUnsupported || b.hasUnsupported
     | .ite c u v _ => c.hasUnsupported || u.hasUnsupported || v.hasUnsupported
     | .con _ args _ => args.any Term.hasUnsupported
     | .tuple es _ => es.any Term.hasUnsupported
     | .record fs _ => fs.any (fun (_, e) => e.hasUnsupported)
     | .field r _ _ _ => r.hasUnsupported
     | .match_ s arms _ => s.hasUnsupported || arms.any (fun (p, e) => p.hasUnsupported || e.hasUnsupported)
     | _ => false)

/-- Datatype constructor signature (from a `DType` decl). -/
structure CtorSig where
  name : String
  argTys : List Ty      -- declared arg types (may reference type params by var)
  resultTy : Ty         -- e.g. Box(a)
  deriving Repr, Inhabited

/-- Declaration (only what the fragment checks; others → `unsupported`). -/
inductive Decl where
  /-- Function declaration, modeled N-ARILY to match march's `DFn` faithfully
  (`params : List`, a clause's full parameter list). No currying — the whole
  param list is carried directly, so no synthetic intermediate nodes with
  unknown types are invented. A 0-param clause decodes to `dlet` instead. If
  the decoder can't represent a clause faithfully (multiple clauses, non-plain
  params, or a guard), it falls back to `Decl.unsupported`. The emitter attaches
  `resolved_ty` only to the *body* expression, not to the function itself, so a
  `dfn` carries no arrow type of its own; params' types (when needed) come from
  the enclosing context, not from a node field. -/
  | dfn (name : String) (params : List (String × Lin)) (body : Term)
  | dlet (name : String) (rhs : Term)
  | dtype (name : String) (params : List String) (ctors : List CtorSig)
  | unsupported
  deriving Inhabited

/-- Is this declaration (or any term/type it carries) out of fragment?
`dtype` carries no terms, but its constructor signatures may reference
out-of-fragment types, so those are checked too. -/
def Decl.hasUnsupported : Decl → Bool
  | .unsupported => true
  | .dfn _ _ body => body.hasUnsupported
  | .dlet _ body => body.hasUnsupported
  | .dtype _ _ ctors =>
      ctors.any (fun c => c.argTys.any Ty.hasUnsupported || c.resultTy.hasUnsupported)

structure Scheme where
  ids : List Int
  constraints : List Constraint
  body : Ty
  deriving Inhabited

structure Instantiation where
  useSpan : Span
  ids : List Int
  args : List Ty
  deriving Inhabited

structure Module where
  decls : List Decl
  schemes : List Scheme
  insts : List Instantiation
  deriving Inhabited

end MarchLean.Syntax

namespace MarchLean.Syntax.Test
open MarchLean.Syntax
-- A literal-int term annotated Int must be constructible and flagged clean.
-- `Ty.hasUnsupported` is a `partial def` (nested recursion through `List.any`
-- isn't structurally-recognized by the kernel), so plain `decide` gets stuck
-- unfolding it; `native_decide` evaluates via the compiler instead.
example : Ty.hasUnsupported (Ty.con "Int" []) = false := by native_decide
-- unsupported propagates through structure.
example : Ty.hasUnsupported (Ty.arrow Ty.unsupported (Ty.con "Int" [])) = true := by native_decide
-- H3: `TError` is a skip trigger — a TError anywhere flags the type.
example : Ty.hasUnsupported Ty.err = true := by native_decide
example : Ty.hasUnsupported (Ty.tuple [Ty.con "Int" [], Ty.err]) = true := by native_decide

-- Regression for the false-accept bug where `Term.hasUnsupported`'s
-- `match_` arm discarded the `Pattern` component of each arm, so an
-- `unsupported` pattern nested in a match arm was invisible.
private def intTy : Ty := Ty.con "Int" []
private def dummySpan : Span := ⟨"f", 0, 0, 0, 0⟩
private def okScrut : Term := Term.lit (Lit.int 0) intTy
private def okArm : Pattern × Term := (Pattern.wild, Term.lit (Lit.int 1) intTy)
private def badArm : Pattern × Term := (Pattern.unsupported, Term.lit (Lit.int 1) intTy)
-- Nested inside a `con` pattern too, not just at the top level of the arm.
private def badNestedArm : Pattern × Term :=
  (Pattern.con "Some" [Pattern.unsupported], Term.lit (Lit.int 1) intTy)

-- A match with only clean patterns/arms is in-fragment.
example : Term.hasUnsupported (Term.match_ okScrut [okArm] intTy) = false := by native_decide
-- A match with an `unsupported` pattern directly in an arm must be flagged
-- (this is exactly what the old code missed: `fun (_, e) => e.hasUnsupported`
-- ignored the pattern).
example : Term.hasUnsupported (Term.match_ okScrut [okArm, badArm] intTy) = true := by native_decide
-- Same, but the `unsupported` is nested inside a constructor pattern.
example : Term.hasUnsupported (Term.match_ okScrut [okArm, badNestedArm] intTy) = true := by native_decide
-- `Pattern.hasUnsupported` itself, standalone: top-level and nested.
example : Pattern.hasUnsupported Pattern.wild = false := by native_decide
example : Pattern.hasUnsupported Pattern.unsupported = true := by native_decide
example : Pattern.hasUnsupported (Pattern.tuple [Pattern.wild, Pattern.unsupported]) = true := by
  native_decide
example : Pattern.hasUnsupported (Pattern.as "x" Pattern.unsupported) = true := by native_decide

end MarchLean.Syntax.Test
