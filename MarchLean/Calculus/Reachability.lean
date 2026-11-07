import MarchLean.EffectGraph

namespace MarchLean.Calculus.Reachability
open MarchLean.EffectGraph

@[simp] theorem names_step (edges rows : Table) : names (step edges rows) = names rows := by
  simp [names, step, List.map_map]

@[simp] theorem lookup_cons (n : String) (caps : List String) (rows : Table) (x : String) :
    lookup ((n, caps) :: rows) x = if n = x then caps else lookup rows x := by
  by_cases h : n = x <;> simp [lookup, h]

@[simp] theorem lookup_nil (x : String) : lookup [] x = [] := rfl

theorem lookup_absent {rows : Table} {x : String} (h : x ∉ names rows) :
    lookup rows x = [] := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rcases r with ⟨n, cs⟩
    simp only [names, List.map_cons, List.mem_cons, not_or] at h
    rw [lookup_cons, if_neg (Ne.symm h.1)]
    exact ih h.2

theorem lookup_map {rows : Table} {x : String}
    (f : String → List String → List String) (h : x ∈ names rows) :
    lookup (rows.map fun (n, cs) => (n, f n cs)) x = f x (lookup rows x) := by
  induction rows with
  | nil => simp [names] at h
  | cons r rs ih =>
    rcases r with ⟨n, cs⟩
    simp only [names, List.map_cons, List.mem_cons] at h
    simp only [List.map_cons, lookup_cons]
    by_cases hn : n = x
    · subst n; simp
    · simp only [hn, ↓reduceIte]
      exact ih (h.resolve_left (Ne.symm hn))

theorem lookup_step {edges rows : Table} {x : String} (h : x ∈ names rows) :
    lookup (step edges rows) x =
      (lookup rows x ++ (lookup edges x).flatMap (lookup rows)).eraseDups :=
  lookup_map (fun n cs => (cs ++ (lookup edges n).flatMap (lookup rows)).eraseDups) h

theorem mem_step {edges rows : Table} {x cap : String} (h : x ∈ names rows) :
    cap ∈ lookup (step edges rows) x ↔
      cap ∈ lookup rows x ∨ ∃ y ∈ lookup edges x, cap ∈ lookup rows y := by
  rw [lookup_step h]
  simp only [List.mem_eraseDups, List.mem_append, List.mem_flatMap]

@[simp] theorem names_rounds (n : Nat) (edges rows : Table) :
    names (rounds n edges rows) = names rows := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [rounds] using ih

theorem rounds_step (n : Nat) (edges rows : Table) :
    rounds n edges (step edges rows) = step edges (rounds n edges rows) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rounds, ih]

theorem closeRows_eq_rounds (n : Nat) (edges rows : Table) :
    closeRows n edges rows = rounds n edges rows := by
  induction n generalizing rows with
  | zero => rfl
  | succ n ih => simp only [closeRows, ih, rounds_step, rounds]

/-- Domain membership matters: no rows are invented for dangling names. -/
theorem mem_lookup_domain {rows : Table} {x cap : String}
    (h : cap ∈ lookup rows x) : x ∈ names rows := by
  by_cases hn : x ∈ names rows
  · exact hn
  · rw [lookup_absent hn] at h
    simp at h

/-- Set inclusion, deliberately ignoring row and capability list order. -/
def Included (a b : Table) : Prop := ∀ x cap, cap ∈ lookup a x → cap ∈ lookup b x

theorem step_inflationary (edges rows : Table) : Included rows (step edges rows) := by
  intro x c hc
  exact (mem_step (mem_lookup_domain hc)).mpr (Or.inl hc)

theorem step_monotone {edges a b : Table} (domains : names a = names b)
    (h : Included a b) : Included (step edges a) (step edges b) := by
  intro x c hc
  have hx : x ∈ names a := by simpa using mem_lookup_domain hc
  have hb : x ∈ names b := domains ▸ hx
  rcases (mem_step hx).mp hc with hc | ⟨y, hy, hc⟩
  · exact (mem_step hb).mpr (.inl (h x c hc))
  · exact (mem_step hb).mpr (.inr ⟨y, hy, h y c hc⟩)

theorem rounds_mono_fuel {n m : Nat} (h : n ≤ m) (edges rows : Table) :
    Included (rounds n edges rows) (rounds m edges rows) := by
  induction h with
  | refl => intro x c hc; exact hc
  | @step m h ih =>
    intro x c hc
    exact step_inflationary edges _ x c (ih x c hc)

theorem rounds_monotone {edges a b : Table} (domains : names a = names b)
    (h : Included a b) (n : Nat) : Included (rounds n edges a) (rounds n edges b) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    apply step_monotone _ ih
    simpa using domains

/-- Reachability on the finite function domain. A dangling name has no function
row and therefore cannot acquire an effect. No unique-key assumption is hidden. -/
inductive Reaches (g : Graph) : String → String → Prop where
  | direct {f cap} : cap ∈ lookup g.initial f → Reaches g f cap
  | call {f next cap} : f ∈ g.vertices → next ∈ lookup g.edges f →
      Reaches g next cap → Reaches g f cap

/-- A concrete nonempty call path, ending at a direct effect. -/
inductive Path (g : Graph) : String → List String → String → Prop where
  | direct {f cap} : cap ∈ lookup g.initial f → Path g f [f] cap
  | call {f next path cap} : f ∈ g.vertices → next ∈ lookup g.edges f →
      Path g next path cap → Path g f (f :: path) cap

theorem Path.reaches {g : Graph} {f cap : String} {path : List String}
    (h : Path g f path cap) : Reaches g f cap := by
  induction h with
  | direct hc => exact .direct hc
  | call hf he _ ih => exact .call hf he ih

theorem Path.nonempty {g : Graph} {f cap : String} {path : List String}
    (h : Path g f path cap) : 0 < path.length := by cases h <;> simp

theorem Path.domain {g : Graph} {f cap : String} {path : List String}
    (h : Path g f path cap) : path ⊆ g.vertices := by
  induction h with
  | direct hc =>
    intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact mem_lookup_domain hc
  | call hf he h ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hf
    · exact ih hx

/-- Cut a path at a repeated vertex. This is the cycle-erasure step. -/
theorem Path.suffix {g : Graph} {f cap x : String} {path : List String}
    (h : Path g f path cap) (hx : x ∈ path) :
    ∃ tail, Path g x tail cap ∧ tail.Sublist path := by
  induction h with
  | direct hc =>
    simp only [List.mem_singleton] at hx
    subst x
    exact ⟨_, .direct hc, .refl _⟩
  | @call f next path cap hf he hp ih =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨_, .call hf he hp, .refl _⟩
    · obtain ⟨tail, ht, hs⟩ := ih hx
      exact ⟨tail, ht, hs.cons _⟩

theorem simple_path {g : Graph} {f cap : String} (h : Reaches g f cap) :
    ∃ path, Path g f path cap ∧ path.Nodup := by
  induction h with
  | direct hc => exact ⟨_, .direct hc, by simp⟩
  | @call f next cap hf he hr ih =>
    obtain ⟨path, hp, hn⟩ := ih
    by_cases hx : f ∈ path
    · obtain ⟨tail, ht, hs⟩ := hp.suffix hx
      exact ⟨tail, ht, hs.nodup hn⟩
    · exact ⟨f :: path, .call hf he hp, List.nodup_cons.mpr ⟨hx, hn⟩⟩

/-- A duplicate-free list injects into any containing list. The containing
list may itself have duplicates, so the executable's raw row count is safe. -/
theorem nodup_length_le {xs ys : List String} (hn : xs.Nodup) (hs : xs ⊆ ys) :
    xs.length ≤ ys.length := by
  induction xs generalizing ys with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := List.nodup_cons.mp hn
    have hm : x ∈ ys := hs (by simp)
    have hs' : xs ⊆ ys.erase x := by
      intro y hy
      apply (List.mem_erase_of_ne (by intro h; subst y; exact hx hy)).mpr
      exact hs (by simp [hy])
    have hi := ih ht hs'
    have hl := List.length_erase_of_mem hm
    have hp : 0 < ys.length := List.length_pos_of_mem hm
    simp only [List.length_cons]
    omega

theorem bounded_simple_path {g : Graph} {f cap : String} (h : Reaches g f cap) :
    ∃ path, Path g f path cap ∧ path.Nodup ∧ path.length ≤ g.vertices.length := by
  obtain ⟨path, hp, hn⟩ := simple_path h
  exact ⟨path, hp, hn, nodup_length_le hn hp.domain⟩

theorem rounds_sound {g : Graph} {f cap : String} {n : Nat}
    (hc : cap ∈ lookup (rounds n g.edges g.initial) f) : Reaches g f cap := by
  induction n generalizing f with
  | zero => exact .direct hc
  | succ n ih =>
    have hf : f ∈ names (rounds n g.edges g.initial) := by
      simpa [rounds] using mem_lookup_domain hc
    rcases (mem_step hf).mp hc with hc | ⟨next, he, hc⟩
    · exact ih hc
    · exact .call (by simpa [Graph.vertices] using hf) he (ih hc)

theorem path_in_rounds {g : Graph} {f cap : String} {path : List String} {n : Nat}
    (hp : Path g f path cap) (hlen : path.length ≤ n + 1) :
    cap ∈ lookup (rounds n g.edges g.initial) f := by
  induction n generalizing f path with
  | zero =>
    cases hp with
    | direct hc => exact hc
    | call hf he tail =>
      have hpos := tail.nonempty
      simp only [List.length_cons] at hlen
      omega
  | succ n ih =>
    cases hp with
    | direct hc => exact rounds_mono_fuel (Nat.zero_le _) _ _ _ _ hc
    | call hf he tail =>
      apply (mem_step (by simpa [Graph.vertices] using hf)).mpr
      exact .inr ⟨_, he, ih tail (by simpa using Nat.le_of_succ_le_succ hlen)⟩

theorem inferReach_sound {g : Graph} {f cap : String}
    (h : cap ∈ lookup (inferReach g) f) : Reaches g f cap := by
  rw [inferReach, closeRows_eq_rounds] at h
  exact rounds_sound h

theorem inferReach_complete {g : Graph} {f cap : String} (h : Reaches g f cap) :
    cap ∈ lookup (inferReach g) f := by
  obtain ⟨path, hp, _, hlen⟩ := bounded_simple_path h
  rw [inferReach, closeRows_eq_rounds]
  exact path_in_rounds hp (by omega)

theorem inferReach_iff (g : Graph) (f cap : String) :
    cap ∈ lookup (inferReach g) f ↔ Reaches g f cap :=
  ⟨inferReach_sound, inferReach_complete⟩

/-- Stabilization is extensional: list ordering and redundant entries are not
part of an effect set's meaning. Every fuel at least the vertex count suffices. -/
theorem fuel_adequate {g : Graph} {n : Nat} (hn : g.vertices.length ≤ n)
    (f cap : String) :
    cap ∈ lookup (closeRows n g.edges g.initial) f ↔ Reaches g f cap := by
  rw [closeRows_eq_rounds]
  constructor
  · exact rounds_sound
  · intro h
    have hc := inferReach_complete h
    rw [inferReach, closeRows_eq_rounds] at hc
    exact rounds_mono_fuel hn _ _ _ _ hc

def Closed (g : Graph) (rows : Table) : Prop :=
  ∀ f ∈ g.vertices, ∀ next ∈ lookup g.edges f,
    ∀ cap ∈ lookup rows next, cap ∈ lookup rows f

theorem inferReach_closed (g : Graph) : Closed g (inferReach g) := by
  intro f hf next he cap hc
  exact inferReach_complete (.call hf he (inferReach_sound hc))

theorem inferReach_contains_initial (g : Graph) : Included g.initial (inferReach g) := by
  intro f cap hc
  exact inferReach_complete (.direct hc)

theorem inferReach_least {g : Graph} {rows : Table}
    (initial : Included g.initial rows) (closed : Closed g rows) :
    Included (inferReach g) rows := by
  intro f cap hc
  have hr := inferReach_sound hc
  clear hc
  induction hr with
  | direct h => exact initial _ _ h
  | call hf he _ ih => exact closed _ hf _ he _ ih

theorem inferReach_fixed (g : Graph) (f cap : String) :
    cap ∈ lookup (step g.edges (inferReach g)) f ↔ cap ∈ lookup (inferReach g) f := by
  constructor
  · intro hc
    have hf : f ∈ names (inferReach g) := by simpa using mem_lookup_domain hc
    rcases (mem_step hf).mp hc with hc | ⟨next, he, hc⟩
    · exact hc
    · apply inferReach_closed g f _ next he cap hc
      simpa [inferReach, closeRows_eq_rounds, Graph.vertices] using hf
  · exact step_inflationary _ _ f cap

/-- The accumulated self-row can be replaced by the original seeds: retaining
an effect adds no new reachability beyond the predecessor rows. -/
theorem mem_rounds_succ {g : Graph} {f cap : String} (hf : f ∈ g.vertices) (n : Nat) :
    cap ∈ lookup (rounds (n + 1) g.edges g.initial) f ↔
      cap ∈ lookup g.initial f ∨
        ∃ next ∈ lookup g.edges f, cap ∈ lookup (rounds n g.edges g.initial) next := by
  induction n with
  | zero => exact mem_step hf
  | succ n ih =>
    rw [rounds, mem_step (by simpa [Graph.vertices] using hf)]
    constructor
    · intro h
      rcases h with h | h
      · rcases ih.mp h with h | ⟨next, he, hc⟩
        · exact .inl h
        · exact .inr ⟨next, he, step_inflationary _ _ _ _ hc⟩
      · exact .inr h
    · intro h
      rcases h with h | h
      · exact .inl (ih.mpr (.inl h))
      · exact .inr h

/-- The cache contains the actual synchronous rounds, not an approximation. -/
@[simp] theorem buildHistory_current (n : Nat) (edges rows : Table) :
    (buildHistory n edges rows).1 = rounds n edges rows := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [buildHistory, ih, rounds]

@[simp] theorem history_zero (edges rows : Table) : history 0 edges rows = [] := rfl

theorem history_succ (n : Nat) (edges rows : Table) :
    history (n + 1) edges rows = rounds n edges rows :: history n edges rows := by
  simp [history, buildHistory]

theorem history_length (n : Nat) (edges rows : Table) :
    (history n edges rows).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [history_succ, List.length_cons, ih]

@[simp] theorem findPath_zero (g : Graph) (f cap : String) :
    findPath 0 g f cap =
      if (lookup g.initial f).contains cap then some [f] else none := rfl

/-- The cached executable satisfies the original witness recurrence exactly;
edge-order tie-breaking is preserved, not just existence of some path. -/
theorem findPath_succ (n : Nat) (g : Graph) (f cap : String) :
    findPath (n + 1) g f cap =
      if (lookup g.initial f).contains cap then some [f]
      else if g.vertices.contains f then
        match (lookup g.edges f).find? (fun next =>
            (lookup (rounds n g.edges g.initial) next).contains cap) with
        | none => none
        | some next => (findPath n g next cap).map (f :: ·)
      else none := by
  simp only [findPath, history_succ, pathFromHistory]
  rfl

theorem findPath_sound {n : Nat} {g : Graph} {f cap : String} {path : List String}
    (h : findPath n g f cap = some path) : Path g f path cap := by
  induction n generalizing f path with
  | zero =>
    simp only [findPath_zero] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst path
      exact .direct (List.contains_iff_mem.mp hc)
    · contradiction
  | succ n ih =>
    simp only [findPath_succ] at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst path
      exact .direct (List.contains_iff_mem.mp hc)
    · split at h
      · rename_i hf
        split at h
        · contradiction
        · rename_i next he
          obtain ⟨tail, ht, hp⟩ := Option.map_eq_some_iff.mp h
          subst path
          exact .call (List.contains_iff_mem.mp hf)
            (List.mem_of_find?_eq_some he) (ih ht)
      · contradiction

theorem findPath_complete {n : Nat} {g : Graph} {f cap : String}
    (hc : cap ∈ lookup (rounds n g.edges g.initial) f) :
    ∃ path, findPath n g f cap = some path := by
  induction n generalizing f with
  | zero => exact ⟨[f], by simp [findPath_zero, rounds] at *; assumption⟩
  | succ n ih =>
    by_cases hd : cap ∈ lookup g.initial f
    · exact ⟨[f], by simp [findPath_succ, hd]⟩
    · have hf : f ∈ g.vertices := by
        simpa [Graph.vertices] using mem_lookup_domain hc
      have hex := ((mem_rounds_succ hf n).mp hc).resolve_left hd
      let pred := fun next => (lookup (rounds n g.edges g.initial) next).contains cap
      have hs : ((lookup g.edges f).find? pred).isSome = true := by
        apply List.find?_isSome.mpr
        obtain ⟨next, he, hc⟩ := hex
        exact ⟨next, he, List.contains_iff_mem.mpr hc⟩
      cases he : (lookup g.edges f).find? pred with
      | none => simp [he] at hs
      | some next =>
        have hn : cap ∈ lookup (rounds n g.edges g.initial) next := by
          simpa [pred] using List.find?_some he
        obtain ⟨path, hp⟩ := ih hn
        refine ⟨f :: path, ?_⟩
        simp only [findPath_succ, List.contains_iff_mem, hd, hf, ↓reduceIte]
        change (match (lookup g.edges f).find? pred with
          | none => none
          | some next => (findPath n g next cap).map (f :: ·)) = some (f :: path)
        rw [he]
        simp [hp]

/-- Every reported reachable effect has an executable, checked call-path
witness, with the same finite bound used by closure. -/
theorem inferReach_witness {g : Graph} {f cap : String}
    (hc : cap ∈ lookup (inferReach g) f) :
    ∃ path, findPath g.vertices.length g f cap = some path ∧ Path g f path cap := by
  rw [inferReach, closeRows_eq_rounds] at hc
  obtain ⟨path, hp⟩ := findPath_complete hc
  exact ⟨path, hp, findPath_sound hp⟩

end MarchLean.Calculus.Reachability
