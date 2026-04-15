/-!
# Perceus RC Insertion: Lin-typed Bindings Get `EFree`, Not `EDecRC`

Formalizes the key invariant from `lib/tir/perceus.ml` lines 438–446:
when a variable is dead and its linearity is `Lin` (or `Aff`), Perceus
inserts `EFree` rather than `EDecRC`.

OCaml source (perceus.ml:438-446):
```ocaml
if v.v_lin = Unr && needs_rc v.v_ty then
  ESeq (decrc_for v (AVar v), e2')
else if v.v_lin = Lin || v.v_lin = Aff then
  if needs_rc v.v_ty then ESeq (EFree (AVar v), e2')
  else e2'
else e2'
```

The claim: a `Lin`-typed binding with a heap-allocated type always takes
the `EFree` branch, never the `EDecRC` branch.
-/

-- ---------------------------------------------------------------------------
-- § 1  Syntax — types and terms
-- ---------------------------------------------------------------------------

/-- Linearity qualifiers (mirrors `type linearity = Lin | Aff | Unr` in tir.ml). -/
inductive Linearity where
  | Lin  -- used exactly once
  | Aff  -- used at most once
  | Unr  -- unrestricted
  deriving DecidableEq, Repr

/-- A subset of TIR types — just enough for `needs_rc`. -/
inductive Ty where
  | TInt | TFloat | TBool | TUnit
  | TString
  | TCon   : String → List Ty → Ty   -- named algebraic type (heap-allocated unless "Atom")
  | TPtr   : Ty → Ty
  | TVar   : String → Ty
  | TTuple : List Ty → Ty
  | TFn    : Ty → Ty → Ty
  deriving Repr

/-- TIR variable with linearity annotation (mirrors `type var = { v_name; v_ty; v_lin }`). -/
structure Var where
  v_name : String
  v_ty   : Ty
  v_lin  : Linearity
  deriving Repr

/-- TIR atoms (variable reference or literal). -/
inductive Atom where
  | AVar : Var → Atom
  | AInt : Int  → Atom
  deriving Repr

/-- TIR expressions — only the RC-relevant constructors Perceus can emit. -/
inductive Expr where
  | ESeq   : Expr → Expr → Expr
  | EFree  : Atom → Expr   -- unconditional dealloc for Lin/Aff values
  | EDecRC : Atom → Expr   -- RC decrement for Unr values
  | EIncRC : Atom → Expr
  | EHole  : Expr           -- placeholder for "the rest of the program"
  deriving Repr

-- ---------------------------------------------------------------------------
-- § 2  `needs_rc` — which types need reference counting?
-- ---------------------------------------------------------------------------

/-- Mirrors `perceus.ml` lines 137–144.
    Returns `true` for heap-allocated types that require RC operations. -/
def needs_rc : Ty → Bool
  | .TInt | .TFloat | .TBool | .TUnit => false
  | .TString   => true
  | .TPtr _    => true
  | .TVar _    => false
  | .TTuple _  => false
  | .TFn _ _   => false
  | .TCon n _  => !("Atom" == n)  -- "Atom" is an i64 scalar, not heap-allocated

-- ---------------------------------------------------------------------------
-- § 3  `drop_var` — Perceus drop decision
-- ---------------------------------------------------------------------------

/-- Given a dead variable `v`, emit the appropriate cleanup and then `e`.

    This is a direct transcription of `perceus.ml` lines 438–446.
    The full Perceus pass wraps this in a liveness analysis; here we
    model just the cleanup-emission decision. -/
def drop_var (v : Var) (e : Expr) : Expr :=
  if v.v_lin == .Unr && needs_rc v.v_ty then
    .ESeq (.EDecRC (.AVar v)) e     -- Unr: reference-counted drop
  else if v.v_lin == .Lin || v.v_lin == .Aff then
    if needs_rc v.v_ty then
      .ESeq (.EFree (.AVar v)) e    -- Lin/Aff: ownership is unique → free directly
    else
      e                              -- scalar: no cleanup needed
  else
    e

-- ---------------------------------------------------------------------------
-- § 4  Theorems
-- ---------------------------------------------------------------------------

/-- **Main theorem**: for a `Lin`-typed dead variable with a heap-allocated type,
    `drop_var` emits `EFree`, not `EDecRC`.

    This is the Lean mechanization of the claim in `specs/lean4-metatheory-plan.md` §2.4:
    "For a `Lin`-typed binding, Perceus inserts `free` (not `decRC`)" -/
theorem lin_drop_is_free (v : Var) (e : Expr)
    (h_lin : v.v_lin = .Lin)
    (h_rc  : needs_rc v.v_ty = true) :
    drop_var v e = .ESeq (.EFree (.AVar v)) e := by
  obtain ⟨name, ty, lin⟩ := v
  subst h_lin
  simp [drop_var, h_rc]

/-- **Corollary**: `Aff`-typed bindings behave identically — also get `EFree`. -/
theorem aff_drop_is_free (v : Var) (e : Expr)
    (h_aff : v.v_lin = .Aff)
    (h_rc  : needs_rc v.v_ty = true) :
    drop_var v e = .ESeq (.EFree (.AVar v)) e := by
  obtain ⟨name, ty, lin⟩ := v
  subst h_aff
  simp [drop_var, h_rc]

/-- **Contrapositive**: `EDecRC` is only emitted for `Unr`-typed variables. -/
theorem decrc_implies_unr (v : Var) (e : Expr)
    (h_rc : needs_rc v.v_ty = true)
    (h    : drop_var v e = .ESeq (.EDecRC (.AVar v)) e) :
    v.v_lin = .Unr := by
  obtain ⟨name, ty, lin⟩ := v
  simp only [] at *
  cases lin with
  | Lin =>
    simp [drop_var, h_rc] at h   -- reduces to EFree = EDecRC → contradiction
  | Aff =>
    simp [drop_var, h_rc] at h   -- reduces to EFree = EDecRC → contradiction
  | Unr =>
    rfl

/-- **No-op case**: when `needs_rc` is false, `drop_var` is a no-op regardless
    of linearity. Scalars require no cleanup. -/
theorem drop_scalar_noop (v : Var) (e : Expr)
    (h_rc : needs_rc v.v_ty = false) :
    drop_var v e = e := by
  simp [drop_var, h_rc]
