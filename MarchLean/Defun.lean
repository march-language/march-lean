import MarchLean.Perceus

/-!
# Defunctionalization Preserves Captured-Variable Linearity

Formalizes the invariant that the bug-fix commit `71d18400` (march)
restored: **closure capture must preserve `v_lin` on free variables.**

## The bug (in prose)

From the commit message:

> Free variables were collected as `(string * Tir.ty)` pairs, dropping the
> `v_lin` field entirely. Every captured variable was then reconstructed
> with `v_lin = Unr`, regardless of whether the original was Lin or Aff.
>
> This means a Lin variable captured by a closure would appear Unr inside
> the lifted apply function and at the EAlloc site, causing Perceus to skip
> the RC operations it would generate for a linearly-typed binding.

This is a direct violation of the invariant in `Perceus.lin_drop_is_free`:
a `Lin` binding must be dropped via `EFree`, not `EDecRC`. If defun silently
relabels it as `Unr`, Perceus emits `EDecRC` — and worse, may leave the cell
never freed, or double-free when the closure is freed separately.

## What this file proves

Two models of the capture pipeline:

1. `lift_body` — the **correct** transformation (propagates full `Var`)
2. `lift_body_unr_stamped` — the **buggy** transformation (stamps `Unr`)

And the theorems:

- `lift_preserves_fvs` — correct transformation recovers the original
  free variable list exactly (including `v_lin`) when we read back the
  binders of the lifted body.
- `lift_preserves_linearity` — corollary: linearity is preserved.
- `buggy_lift_loses_linearity` — **counterexample** showing the buggy
  variant does NOT preserve linearity: given a `Lin`-typed free variable,
  the buggy lifter produces an `Unr` binder. This is exactly the bug
  that caused the downstream Perceus misbehavior.

## Scope

This is a pure structural property of the transformation. It doesn't require
operational semantics — it's about what the transformation *writes*, not
what the program *does* at runtime. That makes the proof short, but also
means it catches bugs only at the level of "defun produces correct syntax,"
not "defun preserves semantic behavior." For most defun bugs (including the
one we're mechanizing), syntax-level is exactly where the bug manifests.
-/

-- ---------------------------------------------------------------------------
-- § 1  Minimal expression model for defun
-- ---------------------------------------------------------------------------

/-- A minimal expression type tailored to the defun concern.

    The real TIR has many more constructors, but for reasoning about the
    fold-of-ELets wrapper that defun generates, we only need `DLet` (the
    outer wrapper) and `DHole` (an opaque "rest of body"). -/
inductive DExpr where
  | DHole : DExpr                          -- opaque "original body"
  | DLet  : Var → DExpr → DExpr            -- `let v = ...load... in rest`
  deriving Repr

-- ---------------------------------------------------------------------------
-- § 2  The correct capture transformation
-- ---------------------------------------------------------------------------

/-- The correct `lift_body`. Mirrors `defun.ml` lines 357–361:

    ```ocaml
    List.fold_right (fun (i, (fv : Tir.var)) acc ->
        let load_expr = Tir.EField (Tir.AVar clo_param, field_name) in
        Tir.ELet (fv, load_expr, acc)
      ) (List.mapi (fun i fv -> (i, fv)) fvs) fn.Tir.fn_body
    ```

    Key property: the binder `fv` is the **original** `Var`, carrying its
    original `v_lin`. No reconstruction, no relabeling. -/
def lift_body (fvs : List Var) (body : DExpr) : DExpr :=
  fvs.foldr (fun fv acc => .DLet fv acc) body

-- ---------------------------------------------------------------------------
-- § 3  The buggy capture transformation (what 71d18400 fixed)
-- ---------------------------------------------------------------------------

/-- Replace a variable's linearity with `Unr`, preserving name and type.
    This is what the buggy reconstruction did. -/
def Var.stampUnr (v : Var) : Var :=
  { v_name := v.v_name, v_ty := v.v_ty, v_lin := .Unr }

/-- The **buggy** lift — drops `v_lin` during collection and reconstructs
    with `Unr`. Mirrors the pre-fix behavior where `free_vars_of_expr`
    returned `(string * Ty)` pairs and the reconstruction stamped `Unr`. -/
def lift_body_unr_stamped (fvs : List Var) (body : DExpr) : DExpr :=
  fvs.foldr (fun fv acc => .DLet fv.stampUnr acc) body

-- ---------------------------------------------------------------------------
-- § 4  Reading back: extract binders from a lifted body
-- ---------------------------------------------------------------------------

/-- Peel the outer `DLet` binders off a lifted expression, returning their
    binding variables in order. Stops at the first non-`DLet`. -/
def outerBinders : DExpr → List Var
  | .DLet v rest => v :: outerBinders rest
  | .DHole       => []

-- ---------------------------------------------------------------------------
-- § 5  Main theorem: correct lift preserves free variables exactly
-- ---------------------------------------------------------------------------

/-- **Correct defun preserves free variables.**

    Reading back the outer binders of `lift_body fvs DHole` recovers `fvs`
    exactly — with every field (name, ty, **and v_lin**) intact.

    The `DHole` body is what makes this clean: the real body of a lambda
    may itself contain `DLet`s, but we only claim correctness for the
    *wrapper* generated by the fold, not for any pre-existing lets
    in the body. -/
theorem lift_preserves_fvs (fvs : List Var) :
    outerBinders (lift_body fvs .DHole) = fvs := by
  induction fvs with
  | nil => rfl
  | cons hd tl ih =>
    show outerBinders (.DLet hd (lift_body tl .DHole)) = hd :: tl
    simp [outerBinders, ih]

/-- **Corollary: linearity is preserved.**

    Every captured free variable ends up bound with its original `v_lin`. -/
theorem lift_preserves_linearity (fvs : List Var) :
    (outerBinders (lift_body fvs .DHole)).map Var.v_lin
      = fvs.map Var.v_lin := by
  rw [lift_preserves_fvs]

-- ---------------------------------------------------------------------------
-- § 6  Counterexample: the buggy lift does NOT preserve linearity
-- ---------------------------------------------------------------------------

/-- Helper: `stampUnr` always yields `Unr`. -/
@[simp] theorem Var.stampUnr_lin (v : Var) : v.stampUnr.v_lin = .Unr := rfl

/-- **The buggy lift loses linearity.**

    Given a free variable list with a `Lin` entry, the buggy lifter produces
    a binder with `v_lin = Unr` — exactly the corruption that caused
    downstream Perceus misbehavior (emitting `EDecRC` where `EFree` was
    correct, violating `Perceus.lin_drop_is_free`).

    The theorem exhibits a *concrete* free variable whose linearity is
    dropped — not an existential, a specific construction. -/
theorem buggy_lift_loses_linearity
    (v : Var) (h_lin : v.v_lin = .Lin) :
    ∃ v' ∈ outerBinders (lift_body_unr_stamped [v] .DHole),
      v'.v_lin ≠ v.v_lin := by
  refine ⟨v.stampUnr, ?_, ?_⟩
  · -- v.stampUnr appears in the outer binders
    simp [lift_body_unr_stamped, outerBinders]
  · -- v.stampUnr.v_lin = Unr ≠ Lin = v.v_lin
    rw [Var.stampUnr_lin, h_lin]
    intro h
    contradiction

-- ---------------------------------------------------------------------------
-- § 7  Connection: the correct lift upholds the Perceus precondition
-- ---------------------------------------------------------------------------

/-- **Bridge to Perceus.**

    For a `Lin` free variable captured by `lift_body`, the re-bound variable
    satisfies the precondition of `Perceus.lin_drop_is_free`: its `v_lin`
    is still `Lin`, so when Perceus drops it, the result is `EFree` — not
    `EDecRC`.

    Combined with `buggy_lift_loses_linearity`, this pinpoints the bug:
    the buggy lift violated this precondition, causing Perceus to take the
    wrong branch. -/
theorem correct_lift_preserves_lin_precondition
    (v : Var) (rest : List Var) (h_lin : v.v_lin = .Lin) :
    ∃ v' ∈ outerBinders (lift_body (v :: rest) .DHole),
      v'.v_lin = .Lin := by
  refine ⟨v, ?_, h_lin⟩
  simp [lift_body, outerBinders]
