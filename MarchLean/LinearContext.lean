import MarchLean.Perceus

/-!
# Linear Context Splitting

Formalizes the context-splitting rules for March's substructural type system.

The OCaml implementation (`typecheck.ml` §12) uses mutable "used" flags.
We use the standard theoretical presentation — context splitting — which is
equivalent but produces cleaner proofs.

Key results:
- `Split.comm`: splitting is commutative
- `Split.lin_preserved`: `Lin` entries are never dropped — they go to at least one side
- `Split.unr_in_both`: `Unr` entries go to both sides (contraction is allowed)
- `Split.weaken_aff`: `Aff` entries CAN be dropped (weakening)
- `Split.lin_countIf`: splitting preserves the count of Lin entries exactly
- `Split.fbip_uniqueness`: a singleton Lin entry goes to EXACTLY one half —
  the no-aliasing property that makes Perceus FBIP in-place memory reuse sound

Together with `Perceus.lin_drop_is_free`, these establish:
  Lin in type system → unique reference → `EFree` is safe (no other live reference)
  → in-place memory reuse is sound (FBIP)
-/

-- ---------------------------------------------------------------------------
-- § 1  Typing contexts
-- ---------------------------------------------------------------------------

/-- A typing context entry: variable name, type, and linearity qualifier. -/
structure Entry where
  name : String
  ty   : Ty
  lin  : Linearity
  deriving Repr

/-- A typing context is a list of entries. -/
abbrev Ctx := List Entry

-- ---------------------------------------------------------------------------
-- § 2  The Split relation
-- ---------------------------------------------------------------------------

/-- `Split Γ Γ₁ Γ₂` means the context `Γ` can be partitioned into `Γ₁` and `Γ₂`
    respecting linearity:

    - **Unr** entries go to BOTH sides (contraction is allowed)
    - **Lin** entries go to exactly ONE side (no contraction, no weakening)
    - **Aff** entries go to at most ONE side (no contraction, weakening IS allowed)

    This is the standard substructural presentation (Wadler, Girard). -/
inductive Split : Ctx → Ctx → Ctx → Prop where
  | nil      : Split [] [] []
  | unr      : Split Γ Γ₁ Γ₂ →
               Split (⟨n, τ, .Unr⟩ :: Γ) (⟨n, τ, .Unr⟩ :: Γ₁) (⟨n, τ, .Unr⟩ :: Γ₂)
  | lin_l    : Split Γ Γ₁ Γ₂ →
               Split (⟨n, τ, .Lin⟩ :: Γ) (⟨n, τ, .Lin⟩ :: Γ₁) Γ₂
  | lin_r    : Split Γ Γ₁ Γ₂ →
               Split (⟨n, τ, .Lin⟩ :: Γ) Γ₁ (⟨n, τ, .Lin⟩ :: Γ₂)
  | aff_l    : Split Γ Γ₁ Γ₂ →
               Split (⟨n, τ, .Aff⟩ :: Γ) (⟨n, τ, .Aff⟩ :: Γ₁) Γ₂
  | aff_r    : Split Γ Γ₁ Γ₂ →
               Split (⟨n, τ, .Aff⟩ :: Γ) Γ₁ (⟨n, τ, .Aff⟩ :: Γ₂)
  | aff_drop : Split Γ Γ₁ Γ₂ →
               Split (⟨n, τ, .Aff⟩ :: Γ) Γ₁ Γ₂

-- ---------------------------------------------------------------------------
-- § 3  Structural properties
-- ---------------------------------------------------------------------------

/-- Splitting is commutative: swap Γ₁ and Γ₂. -/
theorem Split.comm : Split Γ Γ₁ Γ₂ → Split Γ Γ₂ Γ₁
  | .nil        => .nil
  | .unr s      => .unr s.comm
  | .lin_l s    => .lin_r s.comm
  | .lin_r s    => .lin_l s.comm
  | .aff_l s    => .aff_r s.comm
  | .aff_r s    => .aff_l s.comm
  | .aff_drop s => .aff_drop s.comm

-- ---------------------------------------------------------------------------
-- § 4  Linear safety: Lin entries are never dropped
-- ---------------------------------------------------------------------------

/-- A `Lin` entry in Γ must appear in at least one half of any split.
    There is no `lin_drop` rule — unlike `Aff`, linear resources cannot
    be silently discarded. This is the key property that guarantees
    every linear value is consumed exactly once. -/
theorem Split.lin_preserved (s : Split Γ Γ₁ Γ₂)
    {e : Entry} (he : e.lin = .Lin) (hmem : e ∈ Γ) :
    e ∈ Γ₁ ∨ e ∈ Γ₂ := by
  induction s with
  | nil => simp at hmem
  | unr _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction                -- Unr ≠ Lin
    · exact (ih hmem).imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)
  | lin_l _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · exact .inl List.mem_cons_self
    · exact (ih hmem).imp (List.mem_cons_of_mem _) id
  | lin_r _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · exact .inr List.mem_cons_self
    · exact (ih hmem).imp id (List.mem_cons_of_mem _)
  | aff_l _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction                -- Aff ≠ Lin
    · exact (ih hmem).imp (List.mem_cons_of_mem _) id
  | aff_r _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction
    · exact (ih hmem).imp id (List.mem_cons_of_mem _)
  | aff_drop _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction
    · exact ih hmem

-- ---------------------------------------------------------------------------
-- § 5  Unrestricted contraction: Unr entries appear in both halves
-- ---------------------------------------------------------------------------

/-- An `Unr` entry in Γ appears in BOTH halves of any split.
    This is contraction: unrestricted values can be freely duplicated.
    Contrast with `Lin` (exactly one side) and `Aff` (at most one side). -/
theorem Split.unr_in_both (s : Split Γ Γ₁ Γ₂)
    {e : Entry} (he : e.lin = .Unr) (hmem : e ∈ Γ) :
    e ∈ Γ₁ ∧ e ∈ Γ₂ := by
  induction s with
  | nil => simp at hmem
  | unr _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · exact ⟨List.mem_cons_self, List.mem_cons_self⟩
    · have ⟨h₁, h₂⟩ := ih hmem
      exact ⟨List.mem_cons_of_mem _ h₁, List.mem_cons_of_mem _ h₂⟩
  | lin_l _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction                -- Lin ≠ Unr
    · have ⟨h₁, h₂⟩ := ih hmem
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩
  | lin_r _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction
    · have ⟨h₁, h₂⟩ := ih hmem
      exact ⟨h₁, List.mem_cons_of_mem _ h₂⟩
  | aff_l _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction                -- Aff ≠ Unr
    · have ⟨h₁, h₂⟩ := ih hmem
      exact ⟨List.mem_cons_of_mem _ h₁, h₂⟩
  | aff_r _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction
    · have ⟨h₁, h₂⟩ := ih hmem
      exact ⟨h₁, List.mem_cons_of_mem _ h₂⟩
  | aff_drop _ ih =>
    simp only [List.mem_cons] at hmem
    obtain rfl | hmem := hmem
    · contradiction
    · exact ih hmem

-- ---------------------------------------------------------------------------
-- § 6  Affine weakening: Aff entries CAN be dropped
-- ---------------------------------------------------------------------------

/-- Any split can be extended by dropping an `Aff` entry from both halves.
    This is weakening: affine values may be silently discarded.
    Note: there is NO corresponding `lin_drop` rule — that's the point. -/
theorem Split.weaken_aff (s : Split Γ Γ₁ Γ₂) (n : String) (τ : Ty) :
    Split (⟨n, τ, .Aff⟩ :: Γ) Γ₁ Γ₂ :=
  .aff_drop s

-- ---------------------------------------------------------------------------
-- § 7  FBIP uniqueness: Lin values have unique ownership
-- ---------------------------------------------------------------------------
--
-- The deeper safety claim behind Perceus FBIP (Functional But In-Place):
-- when a Lin-typed value is matched/consumed, it has NO other live reference
-- in the context. This guarantees RC=1 at runtime, so in-place memory reuse
-- is sound — the compiler can overwrite the matched value's storage rather
-- than allocating fresh memory.
--
-- Formally, this manifests as a count-preservation property: splitting a
-- context preserves the count of Lin-qualified entries exactly (unlike Unr,
-- which is duplicated by contraction, or Aff, which may be dropped).

/-- Count entries satisfying a predicate. We parameterize by `p : Entry → Bool`
    rather than equality to avoid needing `DecidableEq` on `Ty` (whose nested
    `List Ty` makes structural derivation awkward). In practice, `p` is
    instantiated to "matches this name" or "matches this specific entry". -/
def Ctx.countIf (p : Entry → Bool) : Ctx → Nat
  | []      => 0
  | x :: xs => (if p x then 1 else 0) + Ctx.countIf p xs

/-- Helper: if `p e = true → e.lin = Lin`, then `p` rejects any non-Lin entry. -/
private theorem Ctx.p_rejects_non_lin (p : Entry → Bool)
    (hp : ∀ e, p e = true → e.lin = .Lin)
    (e : Entry) (hne : e.lin ≠ .Lin) : p e = false := by
  cases h : p e
  · rfl
  · exact absurd (hp e h) hne

/-- **Count preservation for Lin-only predicates.**

    If `p` only selects `Lin` entries, then splitting preserves the count:
    `|Γ|_p = |Γ₁|_p + |Γ₂|_p`.

    Contrast with:
    - `Unr`: splitting *doubles* the count (contraction — entry in both halves)
    - `Aff`: splitting *bounds* the count (weakening — entry may be dropped)

    This is the key structural property underlying FBIP memory reuse. -/
theorem Split.lin_countIf (s : Split Γ Γ₁ Γ₂)
    (p : Entry → Bool) (hp : ∀ e, p e = true → e.lin = .Lin) :
    Ctx.countIf p Γ = Ctx.countIf p Γ₁ + Ctx.countIf p Γ₂ := by
  induction s with
  | nil => rfl
  | @unr Γ Γ₁ Γ₂ n τ _ ih =>
    -- Unr entry: p rejects it
    have : p ⟨n, τ, .Unr⟩ = false :=
      Ctx.p_rejects_non_lin p hp _ (by simp)
    simp [Ctx.countIf, this]; omega
  | @lin_l Γ Γ₁ Γ₂ n τ _ ih =>
    -- Lin entry added to Γ and Γ₁. Case split on whether p accepts it.
    simp [Ctx.countIf]; split <;> omega
  | @lin_r Γ Γ₁ Γ₂ n τ _ ih =>
    simp [Ctx.countIf]; split <;> omega
  | @aff_l Γ Γ₁ Γ₂ n τ _ ih =>
    have : p ⟨n, τ, .Aff⟩ = false :=
      Ctx.p_rejects_non_lin p hp _ (by simp)
    simp [Ctx.countIf, this]; omega
  | @aff_r Γ Γ₁ Γ₂ n τ _ ih =>
    have : p ⟨n, τ, .Aff⟩ = false :=
      Ctx.p_rejects_non_lin p hp _ (by simp)
    simp [Ctx.countIf, this]; omega
  | @aff_drop Γ Γ₁ Γ₂ n τ _ ih =>
    have : p ⟨n, τ, .Aff⟩ = false :=
      Ctx.p_rejects_non_lin p hp _ (by simp)
    simp [Ctx.countIf, this]; omega

/-- **FBIP uniqueness lemma.**

    If a `Lin` entry appears exactly once in `Γ`, then any split of `Γ` places
    it in EXACTLY ONE of `Γ₁`, `Γ₂` — never both, never neither.

    This is the no-aliasing guarantee that makes Perceus FBIP in-place reuse
    sound: when we pattern-match on a Lin variable, no other binding in scope
    can reach the same heap cell. Runtime RC is guaranteed to be 1, so the
    allocator can reuse the memory rather than calling `malloc`+`free`.

    The predicate form is more general than equality on `Entry`: any Lin-selecting
    predicate (e.g. "matches this name") has this exclusivity property. -/
theorem Split.fbip_uniqueness (s : Split Γ Γ₁ Γ₂)
    (p : Entry → Bool) (hp : ∀ e, p e = true → e.lin = .Lin)
    (h_one : Ctx.countIf p Γ = 1) :
    (Ctx.countIf p Γ₁ = 1 ∧ Ctx.countIf p Γ₂ = 0) ∨
    (Ctx.countIf p Γ₁ = 0 ∧ Ctx.countIf p Γ₂ = 1) := by
  have h := s.lin_countIf p hp
  omega
