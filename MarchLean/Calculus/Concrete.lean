import MarchLean.CapLattice

/-!
# The shipping lattice, discharged

`WellFormedB hierarchy` by kernel `decide` (~1s on this toolchain), then
every abstract theorem of `Calculus/Lattice.lean` instantiated at the
shipping `CapLattice` names.

If march ever adds a duplicate name, a dangling parent, or a cycle to
`cap_lattice.ml` and the port follows, **the `decide` below is what fails** —
loudly, at build time. That failure mode is the point of this file: before
P0 the table's forest-ness was a comment, and a cycle would have made
`capAncestors` silently truncate with no error anywhere.
-/

namespace MarchLean.Calculus.Concrete
open MarchLean.Calculus MarchLean.CapLattice

theorem hierarchy_wellFormed : WellFormedB hierarchy = true := by decide

theorem capSubsumes_refl (c : String) : capSubsumes c c = true :=
  subsumesIn_refl hierarchy c

theorem capSubsumes_trans {a b c : String}
    (h₁ : capSubsumes a b = true) (h₂ : capSubsumes b c = true) :
    capSubsumes a c = true :=
  subsumesIn_trans hierarchy_wellFormed h₁ h₂

theorem capSubsumes_antisymm {p c : String}
    (h₁ : capSubsumes p c = true) (h₂ : capSubsumes c p = true) : p = c :=
  subsumesIn_antisymm hierarchy_wellFormed h₁ h₂

theorem capSiblings_incomparable {p c q : String}
    (hp : capParent p = some q) (hc : capParent c = some q) (hne : p ≠ c) :
    capSubsumes p c = false :=
  siblings_incomparable hierarchy_wellFormed hp hc hne

theorem capAncestors_fuel_adequate {f : Nat} (hf : hierarchy.length ≤ f)
    (c : String) : capAncestorsFuel f c = capAncestors c :=
  ancestorsIn_fuel_adequate hierarchy_wellFormed hf c

theorem normalize_covered (L : List String) (c : String) :
    coveredIn hierarchy (normalize L) c = coveredIn hierarchy L c :=
  coveredIn_normalizeIn hierarchy_wellFormed L c

theorem normalize_idem (L : List String) : normalize (normalize L) = normalize L :=
  normalizeIn_idem hierarchy L

example : capSubsumes "LibC" "LibC" = true := capSubsumes_refl _
example (p : String) : capSubsumes p "LibC" = true ↔ p = "LibC" :=
  subsumesIn_of_absent (by decide)
example : capSubsumes "IO" "LibC" = false := by decide

end MarchLean.Calculus.Concrete

