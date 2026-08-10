import MarchLean.Syntax

/-!
# The de-partialized walks are the folds they replaced

`Syntax.lean`'s tree walks were `partial def`s recursing through
`List.any`/`List.all`. Each is now a `mutual` block pairing the walk with an
explicit `List` helper, which makes the descent structural — the kernel can
unfold and induct on them, so the tests over them moved from `native_decide`
to `decide` and theorems about them became possible at all.

That refactor needs an argument that behavior did not change. The obvious one
is to keep the old body around and pin `legacy x = new x` on fixtures. This
file does better: each helper is **proved equal to the exact fold it
replaced**, by induction, for every input — not just the ones a corpus
happens to contain. A fixture pin can only ever say "the two agree on what we
thought to try"; these say "the two are the same function".

Each theorem below is literally the diff of the refactor, stated as an
equation. If a future edit to one of these walks drifts from its fold, the
corresponding theorem stops compiling.
-/

namespace MarchLean.Calculus.Walks

open MarchLean.Syntax

/-! ## `Ty` -/

theorem ty_anyHasUnsupported_eq (ts : List Ty) :
    Ty.anyHasUnsupported ts = ts.any Ty.hasUnsupported := by
  induction ts with
  | nil => rfl
  | cons t ts ih => simp [Ty.anyHasUnsupported, List.any_cons, ih]

theorem ty_anyFieldHasUnsupported_eq (fs : List (String × Ty)) :
    Ty.anyFieldHasUnsupported fs = fs.any (fun (_, t) => Ty.hasUnsupported t) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      obtain ⟨n, t⟩ := f
      simp [Ty.anyFieldHasUnsupported, List.any_cons, ih]

/-- `beqList` is the old `length == length && (zip …).all …`. The length
check is not lost: it is exactly the two `_, _` fall-through arms. -/
theorem ty_beqList_eq (xs ys : List Ty) :
    Ty.beqList xs ys
      = (xs.length == ys.length && (xs.zip ys).all (fun (a, b) => Ty.beq a b)) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [Ty.beqList]
  | cons x xs ih =>
      cases ys with
      | nil => simp [Ty.beqList]
      | cons y ys =>
          simp only [Ty.beqList, ih, List.length_cons, List.zip_cons_cons,
                     List.all_cons, beq_iff_eq, Nat.add_right_cancel_iff]
          cases Ty.beq x y <;> simp

/-! ## `Pattern` -/

theorem pattern_anyHasUnsupported_eq (ps : List Pattern) :
    Pattern.anyHasUnsupported ps = ps.any Pattern.hasUnsupported := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [Pattern.anyHasUnsupported, List.any_cons, ih]

theorem pattern_anyFieldHasUnsupported_eq (fs : List (String × Pattern)) :
    Pattern.anyFieldHasUnsupported fs
      = fs.any (fun (_, p) => Pattern.hasUnsupported p) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      obtain ⟨n, p⟩ := f
      simp [Pattern.anyFieldHasUnsupported, List.any_cons, ih]

/-! ## `Term` -/

theorem term_anyHasUnsupported_eq (es : List Term) :
    Term.anyHasUnsupported es = es.any Term.hasUnsupported := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [Term.anyHasUnsupported, List.any_cons, ih]

theorem term_anyFieldHasUnsupported_eq (fs : List (String × Term)) :
    Term.anyFieldHasUnsupported fs = fs.any (fun (_, e) => Term.hasUnsupported e) := by
  induction fs with
  | nil => rfl
  | cons f fs ih =>
      obtain ⟨n, e⟩ := f
      simp [Term.anyFieldHasUnsupported, List.any_cons, ih]

theorem term_optHasUnsupported_eq (g : Option Term) :
    Term.optHasUnsupported g = (g.map Term.hasUnsupported).getD false := by
  cases g <;> rfl

/-- The match-arm fold, including the pattern component. Dropping that
component was a real false-accept bug once (`Syntax.lean`'s regression
tests); this states the arm walk in full so the shape is checked, not
remembered. -/
theorem term_anyArmHasUnsupported_eq (arms : List (Pattern × Option Term × Term)) :
    Term.anyArmHasUnsupported arms
      = arms.any (fun (p, g, e) =>
          Pattern.hasUnsupported p
            || (g.map Term.hasUnsupported).getD false
            || Term.hasUnsupported e) := by
  induction arms with
  | nil => rfl
  | cons a arms ih =>
      obtain ⟨p, g, e⟩ := a
      simp [Term.anyArmHasUnsupported, List.any_cons, ih,
            term_optHasUnsupported_eq, Bool.or_assoc]

theorem anyParamAnnotUnsupported_eq (ps : List (String × Lin × Option Ty)) :
    anyParamAnnotUnsupported ps = ps.any (fun (_, _, a) => optTyHasUnsupported a) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨n, l, a⟩ := p
      simp [anyParamAnnotUnsupported, List.any_cons, ih]

/-! ## `Decl` -/

theorem decl_anyHasUnsupported_eq (ds : List Decl) :
    Decl.anyHasUnsupported ds = ds.any Decl.hasUnsupported := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [Decl.anyHasUnsupported, List.any_cons, ih]

theorem decl_anyCtorHasUnsupported_eq (cs : List CtorSig) :
    Decl.anyCtorHasUnsupported cs
      = cs.any (fun c => c.argTys.any Ty.hasUnsupported || Ty.hasUnsupported c.resultTy) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp [Decl.anyCtorHasUnsupported, List.any_cons, ih, ty_anyHasUnsupported_eq]

/-! ## A property the old definitions could not even state

With the walks structural, `Ty.hasUnsupported` supports genuine induction.
This is the kind of thing P2's whole-checker theorems will need. -/

theorem ty_anyHasUnsupported_append (xs ys : List Ty) :
    Ty.anyHasUnsupported (xs ++ ys)
      = (Ty.anyHasUnsupported xs || Ty.anyHasUnsupported ys) := by
  induction xs with
  | nil => simp [Ty.anyHasUnsupported]
  | cons x xs ih => simp [Ty.anyHasUnsupported, ih, Bool.or_assoc]

theorem decl_anyHasUnsupported_append (xs ys : List Decl) :
    Decl.anyHasUnsupported (xs ++ ys)
      = (Decl.anyHasUnsupported xs || Decl.anyHasUnsupported ys) := by
  induction xs with
  | nil => simp [Decl.anyHasUnsupported]
  | cons x xs ih => simp [Decl.anyHasUnsupported, ih, Bool.or_assoc]

end MarchLean.Calculus.Walks
