/-!
# Abstract capability-lattice theory

`CapLattice.lean`'s five operations, parameterized over the `(name, parent)`
table so their metatheory is proved once for ANY well-formed table and
march's concrete 20-entry `hierarchy` is discharged by `decide`
(`Calculus/Concrete.lean`). The shipping `CapLattice` API is the
specialization of these to `hierarchy`, definition for definition — bodies
here are copied verbatim from the pre-P0 `CapLattice.lean`, table made a
parameter, nothing else changed.
-/
namespace MarchLean.Calculus

/-- A capability table: `(cap_path, parent_path)` rows. -/
abbrev Table := List (String × Option String)

/-- The parent of a capability in `T`, or `none` for a root or an unknown
(FFI) name. -/
def parentIn (T : Table) (c : String) : Option String :=
  match T.find? (fun (n, _) => n == c) with
  | some (_, p) => p
  | none        => none

/-- Fuel-bounded ancestor chain: `c` followed by every ancestor up to the
root, most-specific first. A name absent from `T` returns just itself (the
FFI-cap base case). -/
def ancestorsInFuel (T : Table) : Nat → String → List String
  | 0,        c => [c]
  | fuel + 1, c =>
      match parentIn T c with
      | some p => c :: ancestorsInFuel T fuel p
      | none   => [c]

/-- `ancestorsIn T c` with fuel `T.length` — adequate for any well-formed
table (proved below: `ancestorsIn_fuel_adequate`). -/
def ancestorsIn (T : Table) (c : String) : List String :=
  ancestorsInFuel T T.length c

/-- Is `parent` an ancestor of, or equal to, `child` in `T`? -/
def subsumesIn (T : Table) (parent child : String) : Bool :=
  (ancestorsIn T child).contains parent

/-- Drop any cap subsumed by another cap present, preserving relative order
of survivors. -/
def normalizeIn (T : Table) (caps : List String) : List String :=
  caps.filter (fun c => !caps.any (fun other => other != c && subsumesIn T other c))

/-- Is `used` covered by some declared cap, via subsumption? The abstract
form of `CapCheck.covered` (bridged in P2). -/
def coveredIn (T : Table) (declared : List String) (used : String) : Bool :=
  declared.any (fun need => subsumesIn T need used)

/-! ## Table well-formedness

`CapLattice.lean` asserted in prose that the table "is a finite forest with
no cycles, so `hierarchy.length` is a safe fuel bound". `WellFormedB` makes
that a decidable proposition and `ancestorsIn_fuel_adequate` makes the fuel
claim a theorem; `Calculus/Concrete.lean` discharges the real table. -/

/-- The names (first components) of a table. -/
def namesOf (T : Table) : List String := T.map (·.1)

/-- No two rows share a name (Boolean, so `decide` can discharge it). -/
def nodupNamesB : Table → Bool
  | [] => true
  | (n, _) :: rest => !rest.any (fun (m, _) => m == n) && nodupNamesB rest

/-- Every parent value that occurs is itself a row's name. march's real
table satisfies this; FFI caps are absent from the table entirely, never
dangling parents. -/
def parentClosedB (T : Table) : Bool :=
  T.all (fun (_, p?) => match p? with
    | none => true
    | some p => T.any (fun (n, _) => n == p))

/-- Does the parent chain from `c` reach a parentless node within `fuel`
steps? The acyclicity witness: in a well-formed table every name does so
within `T.length` steps. -/
def reachesRoot (T : Table) : Nat → String → Bool
  | 0, c => (parentIn T c).isNone
  | fuel + 1, c =>
      match parentIn T c with
      | none => true
      | some p => reachesRoot T fuel p

/-- Well-formed table: unique names, closed parents, acyclic. This is what
`CapLattice.lean`'s old prose comment ("the table is a finite forest with no
cycles, so `hierarchy.length` is a safe fuel bound") asserted; here it is a
decidable proposition, discharged for the real table in `Concrete.lean`. -/
def WellFormedB (T : Table) : Bool :=
  nodupNamesB T && parentClosedB T && T.all (fun (n, _) => reachesRoot T T.length n)

theorem ancestorsInFuel_head (T : Table) (fuel : Nat) (c : String) :
    (ancestorsInFuel T fuel c).head? = some c := by
  cases fuel with
  | zero => rfl
  | succ f => simp only [ancestorsInFuel]; cases parentIn T c <;> rfl

theorem self_mem_ancestorsIn (T : Table) (c : String) : c ∈ ancestorsIn T c := by
  have h := ancestorsInFuel_head T T.length c
  unfold ancestorsIn
  cases he : ancestorsInFuel T T.length c with
  | nil => rw [he] at h; simp at h
  | cons x xs => rw [he] at h; simp at h; simp [h]

theorem subsumesIn_refl (T : Table) (c : String) : subsumesIn T c c = true := by
  simp [subsumesIn]
  exact self_mem_ancestorsIn T c

theorem parentIn_eq_none_of_not_mem {T : Table} {c : String}
    (h : c ∉ namesOf T) : parentIn T c = none := by
  unfold parentIn
  cases hf : T.find? (fun (n, _) => n == c) with
  | none => rfl
  | some row =>
      exfalso
      have hmem := List.mem_of_find?_eq_some hf
      have hpred := List.find?_some hf
      have : row.1 = c := by
        cases row; simpa using hpred
      exact h (this ▸ List.mem_map_of_mem hmem)

theorem reachesRoot_mono {T : Table} {c : String} {fuel fuel' : Nat}
    (h : fuel ≤ fuel') (hr : reachesRoot T fuel c = true) :
    reachesRoot T fuel' c = true := by
  induction fuel generalizing c fuel' with
  | zero =>
      have hnone : parentIn T c = none := by
        simpa [reachesRoot, Option.isNone_iff_eq_none] using hr
      cases fuel' with
      | zero => simpa [reachesRoot, Option.isNone_iff_eq_none]
      | succ f => simp [reachesRoot, hnone]
  | succ f ih =>
      cases hp : parentIn T c with
      | none =>
          cases fuel' with
          | zero => simp [reachesRoot, hp]
          | succ f' => simp [reachesRoot, hp]
      | some p =>
          simp only [reachesRoot, hp] at hr
          cases fuel' with
          | zero => omega
          | succ f' =>
              have : f ≤ f' := by omega
              simp only [reachesRoot, hp]
              exact ih this hr

theorem ancestorsInFuel_stable {T : Table} {c : String} {fuel : Nat}
    (h : reachesRoot T fuel c = true) {f : Nat} (hf : fuel ≤ f) :
    ancestorsInFuel T f c = ancestorsInFuel T fuel c := by
  induction fuel generalizing c f with
  | zero =>
      have hnone : parentIn T c = none := by
        simpa [reachesRoot, Option.isNone_iff_eq_none] using h
      cases f with
      | zero => rfl
      | succ f' => simp [ancestorsInFuel, hnone]
  | succ k ih =>
      cases hp : parentIn T c with
      | none =>
          cases f with
          | zero => omega
          | succ f' => simp [ancestorsInFuel, hp]
      | some p =>
          simp only [reachesRoot, hp] at h
          cases f with
          | zero => omega
          | succ f' =>
              have : k ≤ f' := by omega
              simp only [ancestorsInFuel, hp]
              rw [ih h this]

theorem wf_reachesRoot {T : Table} (wf : WellFormedB T = true) (c : String) :
    reachesRoot T T.length c = true := by
  have h3 : T.all (fun (n, _) => reachesRoot T T.length n) = true := by
    unfold WellFormedB at wf
    simp only [Bool.and_eq_true] at wf
    exact wf.2
  by_cases hmem : c ∈ namesOf T
  · obtain ⟨⟨n, p?⟩, hrow, rfl⟩ := List.mem_map.mp hmem
    simpa using List.all_eq_true.mp h3 _ hrow
  · have hnone := parentIn_eq_none_of_not_mem hmem
    cases hl : T.length with
    | zero => simp [reachesRoot, hnone]
    | succ k => simp [reachesRoot, hnone]

theorem ancestorsIn_fuel_adequate {T : Table} (wf : WellFormedB T = true)
    {f : Nat} (hf : T.length ≤ f) (c : String) :
    ancestorsInFuel T f c = ancestorsIn T c :=
  ancestorsInFuel_stable (wf_reachesRoot wf c) hf

theorem ancestorsIn_root {T : Table} {c : String} (h : parentIn T c = none) :
    ancestorsIn T c = [c] := by
  unfold ancestorsIn
  cases T.length with
  | zero => rfl
  | succ k => simp [ancestorsInFuel, h]

theorem ancestorsIn_cons {T : Table} (wf : WellFormedB T = true) {c p : String}
    (h : parentIn T c = some p) : ancestorsIn T c = c :: ancestorsIn T p := by
  have hr := wf_reachesRoot wf c
  have hlen : T.length ≠ 0 := by
    intro hzero
    rw [hzero] at hr
    simp [reachesRoot, h] at hr
  obtain ⟨k, hk⟩ : ∃ k, T.length = k + 1 := by
    cases hl : T.length with
    | zero => exact absurd hl hlen
    | succ k => exact ⟨k, rfl⟩
  have hrp : reachesRoot T k p = true := by
    rw [hk] at hr
    simpa [reachesRoot, h] using hr
  calc ancestorsIn T c
      = ancestorsInFuel T (k + 1) c := by rw [ancestorsIn, hk]
    _ = c :: ancestorsInFuel T k p := by simp [ancestorsInFuel, h]
    _ = c :: ancestorsInFuel T T.length p := by
          rw [ancestorsInFuel_stable hrp (f := T.length) (by omega)]
    _ = c :: ancestorsIn T p := rfl

/-! ## Subsumption is a partial order -/

/-- Bool/Prop bridge used throughout: subsumption IS ancestor membership. -/
theorem subsumesIn_iff_mem {T : Table} {p c : String} :
    subsumesIn T p c = true ↔ p ∈ ancestorsIn T c := by
  simp [subsumesIn]

/-- A suffix at least as long as its host IS its host. -/
private theorem suffix_eq_of_length_le {α} {l₁ l₂ : List α} (h : l₁ <:+ l₂)
    (hlen : l₂.length ≤ l₁.length) : l₁ = l₂ := by
  obtain ⟨t, ht⟩ := h
  have hl := congrArg List.length ht
  simp [List.length_append] at hl
  have ht0 : t = [] := by
    have : t.length = 0 := by omega
    simpa using this
  simpa [ht0] using ht

/-- The workhorse: an ancestor's chain is a suffix of the descendant's. -/
theorem mem_ancestorsIn_suffix {T : Table} (wf : WellFormedB T = true) {p c : String}
    (h : p ∈ ancestorsIn T c) : ancestorsIn T p <:+ ancestorsIn T c := by
  induction hn : (ancestorsIn T c).length using Nat.strongRecOn generalizing c with
  | _ n ih =>
    by_cases hpc : p = c
    · subst hpc; exact List.suffix_refl _
    · cases hpar : parentIn T c with
      | none =>
          rw [ancestorsIn_root hpar] at h
          simp at h
          exact absurd h hpc
      | some q =>
          rw [ancestorsIn_cons wf hpar] at h ⊢
          rcases List.mem_cons.mp h with heq | hq
          · exact absurd heq hpc
          · have hlt : (ancestorsIn T q).length < n := by
              rw [← hn, ancestorsIn_cons wf hpar]
              simp
            exact (ih _ hlt hq rfl).trans (List.suffix_cons _ _)

theorem subsumesIn_trans {T : Table} (wf : WellFormedB T = true) {a b c : String}
    (h₁ : subsumesIn T a b = true) (h₂ : subsumesIn T b c = true) :
    subsumesIn T a c = true := by
  rw [subsumesIn_iff_mem] at h₁ h₂ ⊢
  exact (mem_ancestorsIn_suffix wf h₂).subset h₁

theorem subsumesIn_antisymm {T : Table} (wf : WellFormedB T = true) {p c : String}
    (h₁ : subsumesIn T p c = true) (h₂ : subsumesIn T c p = true) : p = c := by
  rw [subsumesIn_iff_mem] at h₁ h₂
  have s₁ := mem_ancestorsIn_suffix wf h₁
  have s₂ := mem_ancestorsIn_suffix wf h₂
  have heq : ancestorsIn T p = ancestorsIn T c :=
    suffix_eq_of_length_le s₁ s₂.length_le
  have hp : (ancestorsIn T p).head? = some p := ancestorsInFuel_head T T.length p
  have hc : (ancestorsIn T c).head? = some c := ancestorsInFuel_head T T.length c
  rw [heq] at hp
  rw [hp] at hc
  injection hc

theorem no_self_parent {T : Table} (wf : WellFormedB T = true) {p : String} :
    parentIn T p ≠ some p := by
  intro hp
  have hfalse : ∀ f, reachesRoot T f p = false := by
    intro f
    induction f with
    | zero => simp [reachesRoot, hp]
    | succ k ih => simp [reachesRoot, hp, ih]
  have := wf_reachesRoot wf p
  rw [hfalse] at this
  exact Bool.false_ne_true this

theorem siblings_incomparable {T : Table} (wf : WellFormedB T = true) {p c q : String}
    (hp : parentIn T p = some q) (hc : parentIn T c = some q) (hne : p ≠ c) :
    subsumesIn T p c = false := by
  cases hs : subsumesIn T p c with
  | false => rfl
  | true =>
      exfalso
      rw [subsumesIn_iff_mem] at hs
      rw [ancestorsIn_cons wf hc] at hs
      rcases List.mem_cons.mp hs with heq | hq
      · exact hne heq
      · have h₁ : subsumesIn T p q = true := subsumesIn_iff_mem.mpr hq
        have h₂ : subsumesIn T q p = true := by
          rw [subsumesIn_iff_mem, ancestorsIn_cons wf hp]
          exact List.mem_cons_of_mem _ (self_mem_ancestorsIn T q)
        have hpq : p = q := subsumesIn_antisymm wf h₁ h₂
        subst hpq
        exact no_self_parent wf hp

theorem subsumesIn_of_absent {T : Table} {c p : String} (h : parentIn T c = none) :
    subsumesIn T p c = true ↔ p = c := by
  rw [subsumesIn_iff_mem, ancestorsIn_root h]
  simp

theorem parentIn_some_mem_names {T : Table} (wf : WellFormedB T = true) {x q : String}
    (h : parentIn T x = some q) : q ∈ namesOf T := by
  have h2 : parentClosedB T = true := by
    unfold WellFormedB at wf
    simp only [Bool.and_eq_true] at wf
    exact wf.1.2
  unfold parentIn at h
  cases hf : T.find? (fun (n, _) => n == x) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some row =>
      rw [hf] at h
      obtain ⟨n, p?⟩ := row
      simp only at h
      have hrow := List.mem_of_find?_eq_some hf
      have hcl := List.all_eq_true.mp h2 _ hrow
      rw [h] at hcl
      simp only at hcl
      obtain ⟨⟨n', p?'⟩, hrow', hq⟩ := List.any_eq_true.mp hcl
      simp only [beq_iff_eq] at hq
      exact hq ▸ List.mem_map_of_mem hrow'

theorem mem_ancestorsIn_names {T : Table} (wf : WellFormedB T = true) {a x : String}
    (h : a ∈ ancestorsIn T x) : a = x ∨ a ∈ namesOf T := by
  induction hn : (ancestorsIn T x).length using Nat.strongRecOn generalizing x with
  | _ n ih =>
    cases hpar : parentIn T x with
    | none =>
        rw [ancestorsIn_root hpar] at h
        simp at h
        exact Or.inl h
    | some q =>
        rw [ancestorsIn_cons wf hpar] at h
        rcases List.mem_cons.mp h with heq | hq
        · exact Or.inl heq
        · have hlt : (ancestorsIn T q).length < n := by
            rw [← hn, ancestorsIn_cons wf hpar]
            simp
          rcases ih _ hlt hq rfl with heq' | hmem
          · exact Or.inr (heq' ▸ parentIn_some_mem_names wf hpar)
          · exact Or.inr hmem

theorem absent_subsumesIn {T : Table} (wf : WellFormedB T = true) {c x : String}
    (hc : c ∉ namesOf T) (h : subsumesIn T c x = true) : x = c := by
  rw [subsumesIn_iff_mem] at h
  rcases mem_ancestorsIn_names wf h with heq | hmem
  · exact heq.symm
  · exact absurd hmem hc

/-! ## Coverage and normalization -/

theorem coveredIn_mono {T : Table} {L L' : List String} {c : String}
    (hsub : ∀ x ∈ L, x ∈ L') (h : coveredIn T L c = true) :
    coveredIn T L' c = true := by
  simp only [coveredIn, List.any_eq_true] at h ⊢
  obtain ⟨need, hmem, hsubm⟩ := h
  exact ⟨need, hsub need hmem, hsubm⟩

theorem coveredIn_of_subsumes {T : Table} {p c : String}
    (h : subsumesIn T p c = true) : coveredIn T [p] c = true := by
  simp [coveredIn, h]

theorem normalizeIn_subset (T : Table) (L : List String) :
    ∀ x ∈ normalizeIn T L, x ∈ L := by
  intro x hx
  exact (List.mem_filter.mp hx).1

/-- A PROPER ancestor's chain is strictly shorter — the measure the
`exists_survivor` descent recurses on. -/
theorem ancestors_length_lt {T : Table} (wf : WellFormedB T = true) {p c : String}
    (hmem : p ∈ ancestorsIn T c) (hne : p ≠ c) :
    (ancestorsIn T p).length < (ancestorsIn T c).length := by
  have hsuf := mem_ancestorsIn_suffix wf hmem
  rcases Nat.lt_or_ge (ancestorsIn T p).length (ancestorsIn T c).length with hlt | hge
  · exact hlt
  · exfalso
    have heq := suffix_eq_of_length_le hsuf hge
    have hp : (ancestorsIn T p).head? = some p := ancestorsInFuel_head T T.length p
    have hc : (ancestorsIn T c).head? = some c := ancestorsInFuel_head T T.length c
    rw [heq] at hp
    rw [hp] at hc
    exact hne (by injection hc)

/-- Every dropped cap is covered by a survivor: the strict-descent argument
through the "subsumed by" order, terminating because ancestor chains
strictly shorten. -/
theorem exists_survivor {T : Table} (wf : WellFormedB T = true) {L : List String}
    {need : String} (hmem : need ∈ L) :
    ∃ m, m ∈ normalizeIn T L ∧ subsumesIn T m need = true := by
  induction hn : (ancestorsIn T need).length using Nat.strongRecOn generalizing need with
  | _ n ih =>
    by_cases hkeep : need ∈ normalizeIn T L
    · exact ⟨need, hkeep, subsumesIn_refl T need⟩
    · have hdrop : ∃ other, other ∈ L ∧ other ≠ need ∧ subsumesIn T other need = true := by
        rw [normalizeIn] at hkeep
        cases hany : L.any (fun other => other != need && subsumesIn T other need) with
        | true =>
            obtain ⟨other, homem, hcond⟩ := List.any_eq_true.mp hany
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
            exact ⟨other, homem, hcond.1, hcond.2⟩
        | false =>
            exact absurd (List.mem_filter.mpr ⟨hmem, by simp [hany]⟩) hkeep
      obtain ⟨other, homem, hone, hosub⟩ := hdrop
      have homem' : other ∈ ancestorsIn T need := subsumesIn_iff_mem.mp hosub
      have hlt : (ancestorsIn T other).length < n :=
        hn ▸ ancestors_length_lt wf homem' hone
      obtain ⟨m, hmkeep, hmsub⟩ := ih _ hlt homem rfl
      exact ⟨m, hmkeep, subsumesIn_trans wf hmsub hosub⟩

/-- `normalize` never changes what is covered — THE lemma that licenses
applying it to a `needs` list at all (P2 consumes this; it fails without
antisymmetry, i.e. on a cyclic table). -/
theorem coveredIn_normalizeIn {T : Table} (wf : WellFormedB T = true)
    (L : List String) (c : String) :
    coveredIn T (normalizeIn T L) c = coveredIn T L c := by
  cases hL : coveredIn T L c with
  | true =>
      simp only [coveredIn, List.any_eq_true] at hL ⊢
      obtain ⟨need, hmem, hsubm⟩ := hL
      obtain ⟨m, hmkeep, hmsub⟩ := exists_survivor wf hmem
      exact ⟨m, hmkeep, subsumesIn_trans wf hmsub hsubm⟩
  | false =>
      cases hN : coveredIn T (normalizeIn T L) c with
      | false => rfl
      | true =>
          rw [coveredIn_mono (normalizeIn_subset T L) hN] at hL
          exact hL

/-- `normalize` is a fixpoint after one application (no well-formedness
needed: it follows from survivors being a subset). -/
theorem normalizeIn_idem (T : Table) (L : List String) :
    normalizeIn T (normalizeIn T L) = normalizeIn T L := by
  apply List.filter_eq_self.mpr
  intro s hs
  have hs' := hs
  rw [normalizeIn, List.mem_filter] at hs'
  obtain ⟨hsL, hpred⟩ := hs'
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, List.any_eq_false] at hpred ⊢
  intro other homem
  exact hpred other (normalizeIn_subset T L other homem)

end MarchLean.Calculus
