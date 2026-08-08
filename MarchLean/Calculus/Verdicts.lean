import MarchLean.CapCheck

/-!
# Verdict algebra

Kernel-checked laws for the two verdict-combination operators the capability
checker folds with: `CapResult.andThen` (`CapCheck.lean`) and
`DivVerdict.join`. What is proved and what is deliberately NOT:

- `andThen` is associative with identity `ok`; `violation` left-absorbs. It
  is NOT commutative — messages are leftmost-wins by design — but the tier
  projection (`tierOf`) IS: `tierOf` is a homomorphism onto `Tier.max`, so
  which verdict *tier* a fold produces never depends on fold order, only
  which *message*. P2's order-independence theorem builds on exactly this.
-/

namespace MarchLean.Calculus
open MarchLean.CapCheck

/-- Verdict severity, forgetting messages: `ok < skip < violation`. -/
inductive Tier where
  | ok | skip | violation
  deriving DecidableEq, Repr

/-- Max in the severity order (violation absorbs, ok is identity). -/
def Tier.max : Tier → Tier → Tier
  | .violation, _ => .violation
  | _, .violation => .violation
  | .skip, _      => .skip
  | _, .skip      => .skip
  | .ok, .ok      => .ok

/-- The tier of a verdict (forget the message). -/
def tierOf : CapResult → Tier
  | .ok          => .ok
  | .skip _      => .skip
  | .violation _ => .violation

theorem ok_andThen (r : CapResult) : CapResult.ok.andThen r = r := by
  cases r <;> rfl
theorem andThen_ok (r : CapResult) : r.andThen .ok = r := by
  cases r <;> rfl
theorem violation_andThen (m : String) (r : CapResult) :
    (CapResult.violation m).andThen r = .violation m := rfl
theorem andThen_assoc (a b c : CapResult) :
    (a.andThen b).andThen c = a.andThen (b.andThen c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem Tier.max_comm (a b : Tier) : a.max b = b.max a := by
  cases a <;> cases b <;> rfl
theorem Tier.max_assoc (a b c : Tier) : (a.max b).max c = a.max (b.max c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem Tier.max_idem (a : Tier) : a.max a = a := by
  cases a <;> rfl
theorem Tier.ok_max (a : Tier) : Tier.ok.max a = a := by
  cases a <;> rfl
theorem Tier.max_ok (a : Tier) : a.max .ok = a := by
  cases a <;> rfl

/-- `tierOf` is a monoid homomorphism `(CapResult, andThen, ok) → (Tier, max, ok)`. -/
theorem tierOf_andThen (a b : CapResult) :
    tierOf (a.andThen b) = (tierOf a).max (tierOf b) := by
  cases a <;> cases b <;> rfl

/-- Tiers are fold-order-independent even though messages are not. -/
theorem tierOf_andThen_comm (a b : CapResult) :
    tierOf (a.andThen b) = tierOf (b.andThen a) := by
  rw [tierOf_andThen, tierOf_andThen, Tier.max_comm]

/-! ## `DivVerdict.join`: a bounded join-semilattice

`safe` is the identity, `divZero` absorbs, and the operator is commutative,
associative, and idempotent — so `joinAll` over a body's division sites is a
pure set operation: `joinAll_perm` below shows traversal order can never
change a division verdict. -/

theorem join_comm (a b : DivVerdict) : a.join b = b.join a := by
  cases a <;> cases b <;> rfl
theorem join_assoc (a b c : DivVerdict) : (a.join b).join c = a.join (b.join c) := by
  cases a <;> cases b <;> cases c <;> rfl
theorem join_idem (a : DivVerdict) : a.join a = a := by
  cases a <;> rfl
theorem safe_join (a : DivVerdict) : DivVerdict.safe.join a = a := by
  cases a <;> rfl
theorem join_safe (a : DivVerdict) : a.join .safe = a := by
  cases a <;> rfl
theorem divZero_join (a : DivVerdict) : DivVerdict.divZero.join a = .divZero := rfl

/-- Fold with any accumulator = accumulator joined onto the fold from `safe`.
The bridge that lets `joinAll` be reasoned about pointwise. -/
theorem foldl_join_shift (l : List DivVerdict) (a : DivVerdict) :
    l.foldl DivVerdict.join a = a.join (DivVerdict.joinAll l) := by
  induction l generalizing a with
  | nil => simp [DivVerdict.joinAll, List.foldl_nil, join_safe]
  | cons x xs ih =>
      simp only [DivVerdict.joinAll, List.foldl_cons]
      rw [ih (a.join x), ih (DivVerdict.safe.join x), safe_join, join_assoc]

/-- `joinAll` is permutation-invariant: division-site verdict joins do not
depend on traversal order. P2's order-independence theorem consumes this. -/
theorem joinAll_perm {l₁ l₂ : List DivVerdict} (h : l₁.Perm l₂) :
    DivVerdict.joinAll l₁ = DivVerdict.joinAll l₂ := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
      simp only [DivVerdict.joinAll, List.foldl_cons]
      rw [foldl_join_shift, foldl_join_shift, ih]
  | swap x y l =>
      simp only [DivVerdict.joinAll, List.foldl_cons]
      congr 1
      cases x <;> cases y <;> rfl
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

end MarchLean.Calculus
