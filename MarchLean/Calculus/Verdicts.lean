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

end MarchLean.Calculus
