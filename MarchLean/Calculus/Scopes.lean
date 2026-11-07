import MarchLean.CapScope
import MarchLean.Calculus.Concrete

/-! Kernel proofs for the lexical scope and capability product orders.
Antisymmetry concerns the segment representation, not original raw strings:
lexically equivalent strings deliberately yield the same scope.
-/
namespace MarchLean.Calculus.Scopes
open MarchLean.CapScope

theorem scopeSubsumes_refl (s : Scope) : scopeSubsumes s s = true := by
  cases s <;> simp [scopeSubsumes, List.isPrefixOf_iff_prefix]

theorem scopeSubsumes_trans {a b c : Scope}
    (hab : scopeSubsumes a b = true) (hbc : scopeSubsumes b c = true) :
    scopeSubsumes a c = true := by
  cases a with
  | unbounded => rfl
  | path aa xs =>
    cases b with
    | unbounded => simp [scopeSubsumes] at hab
    | path ab ys =>
      cases c with
      | unbounded => simp [scopeSubsumes] at hbc
      | path ac zs =>
        simp only [scopeSubsumes, Bool.and_eq_true, beq_iff_eq,
          List.isPrefixOf_iff_prefix] at *
        exact ⟨hab.1.trans hbc.1, hab.2.trans hbc.2⟩

theorem scopeSubsumes_antisymm {a b : Scope}
    (hab : scopeSubsumes a b = true) (hba : scopeSubsumes b a = true) : a = b := by
  cases a <;> cases b <;>
    simp_all [scopeSubsumes, List.isPrefixOf_iff_prefix]
  rename_i aa xs ab ys
  have hs := hab.2.eq_of_length_le hba.length_le
  simp_all

theorem subsumesAuthority_refl (a : Authority) : subsumesAuthority a a = true := by
  simp [subsumesAuthority, Concrete.capSubsumes_refl, scopeSubsumes_refl]

theorem subsumesAuthority_trans {a b c : Authority}
    (hab : subsumesAuthority a b = true) (hbc : subsumesAuthority b c = true) :
    subsumesAuthority a c = true := by
  simp only [subsumesAuthority, Bool.and_eq_true] at *
  exact ⟨Concrete.capSubsumes_trans hab.1 hbc.1, scopeSubsumes_trans hab.2 hbc.2⟩

theorem subsumesAuthority_antisymm {a b : Authority}
    (hab : subsumesAuthority a b = true) (hba : subsumesAuthority b a = true) : a = b := by
  simp only [subsumesAuthority, Bool.and_eq_true] at *
  have hc := Concrete.capSubsumes_antisymm hab.1 hba.1
  have hs := scopeSubsumes_antisymm hab.2 hba.2
  cases a; cases b; simp_all

/-- Executable coverage is precisely an existential grant witness. -/
theorem covered_iff (grants : List Authority) (requirement : Authority) :
    covered grants requirement = true ↔
      ∃ grant ∈ grants, subsumesAuthority grant requirement = true := by
  simp [covered]

/-- Enlarging the grant list preserves this authority coverage judgment. -/
theorem covered_mono {small large : List Authority} (h : small ⊆ large)
    {requirement : Authority} (hc : covered small requirement = true) :
    covered large requirement = true := by
  obtain ⟨grant, hm, hs⟩ := (covered_iff small requirement).mp hc
  exact (covered_iff large requirement).mpr ⟨grant, h hm, hs⟩

#print axioms scopeSubsumes_refl
#print axioms scopeSubsumes_trans
#print axioms scopeSubsumes_antisymm
#print axioms subsumesAuthority_refl
#print axioms subsumesAuthority_trans
#print axioms covered_iff
#print axioms covered_mono
#print axioms subsumesAuthority_antisymm
end MarchLean.Calculus.Scopes
