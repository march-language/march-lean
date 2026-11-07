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

/-- `eraseDups` retains first occurrences, as the OCaml seen-set filter does. -/
theorem eraseDups_first (c : String) (L : List String) :
    (c :: L).eraseDups = c :: (L.filter (fun x => !(x == c))).eraseDups :=
  List.eraseDups_cons

theorem eraseDups_nodup (L : List String) : L.eraseDups.Nodup := by
  induction hn : L.length using Nat.strongRecOn generalizing L with
  | _ n ih =>
    cases L with
    | nil => simp
    | cons c L =>
      rw [eraseDups_first, List.nodup_cons]
      constructor
      · simp [List.mem_eraseDups, List.mem_filter]
      · apply ih _ ?_ _ rfl
        have := List.length_filter_le (fun x => !(x == c)) L
        simp only [List.length_cons] at hn
        omega

theorem eraseDups_eq_self {L : List String} (h : L.Nodup) : L.eraseDups = L := by
  induction L with
  | nil => rfl
  | cons c L ih =>
    rw [List.nodup_cons] at h
    rw [eraseDups_first]
    have hf : L.filter (fun x => !(x == c)) = L := by
      apply List.filter_eq_self.mpr
      intro x hx
      simp only [Bool.not_eq_true', beq_eq_false_iff_ne]
      intro heq
      exact h.1 (heq ▸ hx)
    rw [hf, ih h.2]

/-- A sublist theorem records survivor order, not just set equality. -/
theorem eraseDups_sublist (L : List String) : L.eraseDups.Sublist L := by
  induction hn : L.length using Nat.strongRecOn generalizing L with
  | _ n ih =>
    cases L with
    | nil => simp
    | cons c L =>
      rw [eraseDups_first]
      apply List.Sublist.cons₂
      apply List.Sublist.trans (ih _ ?_ _ rfl) List.filter_sublist
      have := List.length_filter_le (fun x => !(x == c)) L
      simp only [List.length_cons] at hn
      omega

theorem normalize_nodup (L : List String) : (normalize L).Nodup :=
  (eraseDups_nodup L).filter _

theorem normalize_sublist (L : List String) : (normalize L).Sublist L :=
  List.filter_sublist.trans (eraseDups_sublist L)

theorem normalize_covered (L : List String) (c : String) :
    coveredIn hierarchy (normalize L) c = coveredIn hierarchy L c := by
  rw [normalize, coveredIn_normalizeIn hierarchy_wellFormed]
  apply Bool.eq_iff_iff.mpr
  simp only [coveredIn, List.any_eq_true, List.mem_eraseDups]

theorem normalize_idem (L : List String) : normalize (normalize L) = normalize L := by
  change normalizeIn hierarchy (normalize L).eraseDups = normalize L
  rw [eraseDups_eq_self (normalize_nodup L)]
  exact normalizeIn_idem hierarchy L.eraseDups

-- Duplicate-first regression and order witnesses, checked by the kernel.
example : normalize ["LibC", "IO.FileRead", "LibC"] = ["LibC", "IO.FileRead"] := by decide
example : normalize ["LibC", "IO.FileRead", "IO", "LibC", "Db"] = ["LibC", "IO", "Db"] := by decide
example : normalize [] = [] := by decide
-- The historical abstract operation remains explicitly duplicate-preserving.
example : normalizeIn hierarchy ["LibC", "LibC"] = ["LibC", "LibC"] := by decide

#print axioms normalize_nodup
#print axioms normalize_sublist
#print axioms normalize_covered
#print axioms normalize_idem

example : capSubsumes "LibC" "LibC" = true := capSubsumes_refl _
example (p : String) : capSubsumes p "LibC" = true ↔ p = "LibC" :=
  subsumesIn_of_absent (by decide)
example : capSubsumes "IO" "LibC" = false := by decide

end MarchLean.Calculus.Concrete

