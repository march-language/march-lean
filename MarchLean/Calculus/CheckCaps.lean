import MarchLean.Calculus.Concrete
import MarchLean.Calculus.Verdicts
import MarchLean.CapCheck

/-!
# Whole-checker properties, and where they stop being true

Two properties that sound like they should hold of `CapCheck.checkCaps`:

1. **Normalize-stability** — replacing `needs L` by `needs (normalize L)`
   never changes the verdict.
2. **IO-cap monotonicity** — adding a capability to `needs` never flips
   accept into reject.

Both are **true for the subsumption-coverage core** (Checks 1/4/5, whose only
cap reasoning is `covered declared c`) and **false for the full checker**. The
boundary is the behavioral-cap layer in both cases, and it is the same
mechanism twice: `cap no_extern` reads the `needs` list for a *property of the
list itself* (`hasForeignNeed`) rather than asking what the list covers. A
check that inspects the syntax of a declaration set, rather than its
denotation, is not stable under any operation that preserves only the
denotation — and `normalize` is exactly such an operation
(`Calculus.coveredIn_normalizeIn`).

So the counterexamples are not curiosities to be worked around. They say:
**`normalize` may never be applied to a `needs` list before a behavioral-cap
check runs.** Nothing in the checker does that today; these theorems are what
make it a checked invariant rather than an accident.

Each pair below is stated so the *mechanism* is kernel-checked (`decide` over
`CapLattice` and `hasForeignNeed`, both total), with the end-to-end
`checkCaps` verdict pinned separately by `native_decide` — `checkCaps` runs
through `partial def`s and so has no equation lemmas for the kernel to unfold.
The mechanism is the part that generalizes; the end-to-end pin is the part
that proves the mechanism actually reaches a verdict.
-/

namespace MarchLean.Calculus.CheckCaps

open MarchLean.Calculus MarchLean.CapLattice MarchLean.CapCheck MarchLean.Syntax

/-! ## 1. Normalize-stability

Positive direction, already proved for any well-formed table:
`Calculus.coveredIn_normalizeIn` — normalizing a declared set never changes
what it covers. Instantiated at the shipping lattice as
`Concrete.normalize_covered`. That is the whole coverage core. -/

/-- Restated here so the pair reads together: on the coverage core,
normalizing `needs` is invisible. -/
theorem coverage_core_normalize_stable (L : List String) (c : String) :
    coveredIn hierarchy (normalize L) c = coveredIn hierarchy L c :=
  Concrete.normalize_covered L c

/-! ### The counterexample

`IO.Foreign`'s parent is `IO`, so `normalize` absorbs it. -/

theorem normalize_absorbs_foreign : normalize ["IO", "IO.Foreign"] = ["IO"] := by
  decide

/-- …and `hasForeignNeed` — which `cap no_extern` consults — cannot see the
absorbed entry, because it tests the *spelling* of each path rather than what
the set covers. This is the whole defect in two lines. -/
theorem foreign_need_lost_by_normalize :
    (["IO", "IO.Foreign"].any hasForeignNeed) = true ∧
    ((normalize ["IO", "IO.Foreign"]).any hasForeignNeed) = false := by
  -- `native_decide` rather than `decide`: `hasForeignNeed` splits on ".",
  -- and `String.splitOn` does not reduce in the kernel. The lattice half of
  -- this counterexample (`normalize_absorbs_foreign`) IS kernel-checked.
  native_decide

/-- The same two `needs` lists are coverage-equivalent, which is precisely why
this is a defect and not merely a difference: no coverage-based check could
tell them apart, and `no_extern` is not a coverage-based check. -/
theorem normalize_foreign_coverage_equivalent (c : String) :
    coveredIn hierarchy ["IO", "IO.Foreign"] c
      = coveredIn hierarchy (normalize ["IO", "IO.Foreign"]) c :=
  (coverage_core_normalize_stable ["IO", "IO.Foreign"] c).symm

/-- End-to-end: the un-normalized module violates `no_extern`… -/
private def foreignNeedUnnormalized : Module := {
  decls := [Decl.dmod "NoFFI" [
    Decl.dopts ["no_extern"],
    Decl.dneeds ["IO", "IO.Foreign"],
    Decl.dfn "ping" [("host", Lin.unrestricted, some (Ty.con "String" []))] none
      (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }

/-- …and the normalized one does not. -/
private def foreignNeedNormalized : Module := {
  decls := [Decl.dmod "NoFFI" [
    Decl.dopts ["no_extern"],
    Decl.dneeds (normalize ["IO", "IO.Foreign"]),
    Decl.dfn "ping" [("host", Lin.unrestricted, some (Ty.con "String" []))] none
      (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }

/-- **Normalize-stability is FALSE for the full checker.** Same module, same
coverage, `needs` replaced by its own normalization — and the verdict tier
moves from `violation` to `ok`. -/
theorem normalize_not_verdict_preserving :
    tierOf (checkCaps foreignNeedUnnormalized) = .violation ∧
    tierOf (checkCaps foreignNeedNormalized) = .ok := by
  native_decide

/-! ## 2. IO-cap monotonicity

Positive direction, already proved for any well-formed table:
`Calculus.coveredIn_mono` — enlarging the declared set never removes
coverage, so no coverage-core check can turn accept into reject. -/

/-- Restated at the shipping lattice: on the coverage core, adding a `needs`
entry only ever helps. -/
theorem coverage_core_monotone {L L' : List String} {c : String}
    (hsub : ∀ x ∈ L, x ∈ L') (h : coveredIn hierarchy L c = true) :
    coveredIn hierarchy L' c = true :=
  coveredIn_mono hsub h

/-! ### The counterexample -/

private def noExternPlain : Module := {
  decls := [Decl.dmod "NoFFI" [
    Decl.dopts ["no_extern"],
    Decl.dneeds ["IO"],
    Decl.dfn "ping" [("host", Lin.unrestricted, some (Ty.con "String" []))] none
      (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }

private def noExternPlusForeign : Module := {
  decls := [Decl.dmod "NoFFI" [
    Decl.dopts ["no_extern"],
    Decl.dneeds ["IO", "IO.Foreign"],
    Decl.dfn "ping" [("host", Lin.unrestricted, some (Ty.con "String" []))] none
      (Term.lit (Lit.int 1) (Ty.con "Int" []))]],
  schemes := [], insts := [], moduleCaps := [] }

/-- **IO-cap monotonicity is FALSE for the full checker.** `["IO"]` is a
subset of `["IO", "IO.Foreign"]`, the added cap is already covered by `IO`
(so it grants no new authority whatsoever), and yet the verdict flips
`ok → violation`.

Declaring a capability is itself observable behavior at the behavioral layer:
`no_extern` objects to the *declaration* of foreign authority, not to holding
it. That is why monotonicity has no chance here, and why the coverage-core
theorem above is the strongest true form of it. -/
theorem monotonicity_fails_at_behavioral_layer :
    tierOf (checkCaps noExternPlain) = .ok ∧
    tierOf (checkCaps noExternPlusForeign) = .violation := by
  native_decide

/-- The added capability is redundant for coverage — `IO` already subsumes
`IO.Foreign` — so the flip above cannot be explained as new authority. -/
theorem added_cap_was_already_covered :
    coveredIn hierarchy ["IO"] "IO.Foreign" = true := by
  decide

end MarchLean.Calculus.CheckCaps
