import MarchLean.GrantCheck
import MarchLean.CapabilityReach
import MarchLean.Calculus.Reachability

/-! General grant theorems about the exact predicate the CLI executes. These
laws do not extend to behavioral capability declarations such as no_extern. -/
namespace MarchLean.Calculus.Grants
open MarchLean.EffectGraph MarchLean.GrantCheck MarchLean.CapLattice
open MarchLean.Calculus.Reachability

theorem uncovered_none_iff (grants caps : List String) :
    uncovered grants caps = none ↔
      ∀ cap ∈ caps, capSubsumes "IO" cap = true → covered grants cap = true := by
  simp [uncovered, List.find?_eq_none, Bool.and_eq_true]

theorem grantCovers_iff (grants caps : List String) :
    grantCovers grants caps = true ↔
      ∀ cap ∈ caps, capSubsumes "IO" cap = true → covered grants cap = true := by
  simp only [grantCovers, Option.isNone_iff_eq_none, uncovered_none_iff]

/-- Acceptance is exactly universal coverage of reachable IO effects. -/
theorem grant_accept_iff (g : Graph) (f : String) (grants : List String) :
    grantCovers grants (lookup (inferReach g) f) = true ↔
      ∀ cap, Reaches g f cap → capSubsumes "IO" cap = true → covered grants cap = true := by
  simp only [grantCovers_iff, inferReach_iff]

/-- Equivalent statement in terms of actual grants and lattice subsumption. -/
theorem grant_accept_iff_subsumes (g : Graph) (f : String) (grants : List String) :
    grantCovers grants (lookup (inferReach g) f) = true ↔
      ∀ cap, Reaches g f cap → capSubsumes "IO" cap = true →
        ∃ grant ∈ grants, capSubsumes grant cap = true := by
  simp only [grant_accept_iff, covered, List.any_eq_true]

theorem covered_mono {small large : List String} (h : small ⊆ large) {cap : String}
    (hc : covered small cap = true) : covered large cap = true := by
  obtain ⟨grant, hg, hs⟩ := List.any_eq_true.mp hc
  exact List.any_eq_true.mpr ⟨grant, h hg, hs⟩

/-- Adding grants cannot turn acceptance into rejection for this judgment. -/
theorem grant_mono {small large caps : List String} (h : small ⊆ large)
    (hc : grantCovers small caps = true) : grantCovers large caps = true := by
  rw [grantCovers_iff] at hc ⊢
  intro cap hm hi
  exact covered_mono h (hc cap hm hi)

theorem uncovered_sound {grants caps : List String} {cap : String}
    (h : uncovered grants caps = some cap) :
    cap ∈ caps ∧ capSubsumes "IO" cap = true ∧ covered grants cap = false := by
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  cases hc : covered grants cap <;> simp_all

/-- A rejection comes with a finite, valid call chain to the uncovered effect;
no compiler-supplied diagnostic is used as evidence. -/
theorem grant_reject_witness {g : Graph} {f cap : String} {grants : List String}
    (h : uncovered grants (lookup (inferReach g) f) = some cap) :
    capSubsumes "IO" cap = true ∧ covered grants cap = false ∧
      ∃ path, findPath g.vertices.length g f cap = some path ∧ Path g f path cap := by
  obtain ⟨hm, hi, hc⟩ := uncovered_sound h
  exact ⟨hi, hc, inferReach_witness hm⟩

/-- The checker result, rather than a parallel specification-only predicate. -/
theorem checkGrant_ok_iff (g : Graph) (f : String) (grants : List String) :
    MarchLean.CapabilityReach.checkGrant g f grants = .ok ↔
      ∀ cap, Reaches g f cap → capSubsumes "IO" cap = true → covered grants cap = true := by
  rw [← grant_accept_iff]
  unfold MarchLean.CapabilityReach.checkGrant grantCovers
  cases h : uncovered grants (lookup (inferReach g) f) <;> simp [h]

/-- Graph extraction preserves the number of row slots used by the old fuel
bound. Duplicates need not be assumed away for the graph theorems. -/
theorem effectGraph_vertices (fs : List MarchLean.CapabilityReach.Function) (entry : String) :
    (MarchLean.CapabilityReach.effectGraph fs entry).vertices = fs.map (·.name) := by
  simp [MarchLean.CapabilityReach.effectGraph, Graph.vertices, names, List.map_map]

/-- The old public closeRows call and the verified graph entry point coincide. -/
theorem executable_bridge (fs : List MarchLean.CapabilityReach.Function) (entry : String) :
    let g := MarchLean.CapabilityReach.effectGraph fs entry
    MarchLean.CapabilityReach.closeRows fs.length g.edges g.initial = inferReach g := by
  simp [inferReach, effectGraph_vertices]

end MarchLean.Calculus.Grants
