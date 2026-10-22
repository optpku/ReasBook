/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_28
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_5

open SubtypeFirmness

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace

noncomputable section

universe u v

namespace ERealFunction

section PrimalSolutionsViaDualSolutions

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/- Source/core/bridge triage:
- `source-facing`: Corollary 19.7 is the fixed-point reformulation of the equality-constrained
  proximal problem.
- `core/canonical`: Proposition 19.5 packages the underlying primal/dual pair through
  `proximalCompositePerturbationFunction`, together with the canonical proximal owner
  `Prox[φ, hφ]`.
- `bridge/view`: `proximalConstraintDualMap` is the source-facing fixed-point map whose fixed
  points encode the equality constraint on the associated proximal point. -/

/-- The dual fixed-point map associated with the linearly constrained proximal problem from
Corollary 19.7. -/
def proximalConstraintDualMap
    (φ : H → Set.Ioi (⊥ : EReal)) (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) : K → K :=
  fun v ↦
    r + v - L (Prox[φ, hφ] (z - L.adjoint v))

-- Proof sketch: unfold `proximalConstraintDualMap`, rewrite fixed-point membership as
-- `r + v - L (Prox_φ (z - L^* v)) = v`, and rearrange the equality.
/-- A vector is a fixed point of the Corollary 19.7 dual map exactly when its associated proximal
point satisfies the linear constraint `Lx = r`. -/
theorem mem_fixedPoints_proximalConstraintDualMap_iff
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) {v : K} :
    v ∈ Function.fixedPoints (proximalConstraintDualMap φ hφ z r L) ↔
      L (Prox[φ, hφ] (z - L.adjoint v)) = r := sorry

-- Proof sketch: `Prox_φ` is firmly nonexpansive by Proposition 12.28. Corollary 4.13 transfers
-- that firm nonexpansiveness through the adjoint compression determined by `L`, and Proposition
-- 4.4 then identifies the displayed fixed-point operator with the corresponding residual map,
-- up to the harmless affine translation by `r`.
/-- Corollary 19.7 (1): if `φ ∈ Γ₀(ℋ)` and `‖L‖ ≤ 1`, then the map
`v ↦ r + v - L (Prox_φ (z - L^* v))` is firmly nonexpansive. -/
theorem proximalConstraintDualMap_firmlyNonexpansive_of_mem_gammaZero
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) :
    FirmlyNonexpansive (proximalConstraintDualMap φ hφ z r L) := sorry

-- Proof sketch: specialize Proposition 19.5 to the indicator of `{0}`. The regularity condition
-- becomes `r ∈ sri (L '' effectiveDomain φ)`, and the dual solution set is identified with the
-- fixed-point set through `mem_fixedPoints_proximalConstraintDualMap_iff`.
/-- Corollary 19.7 (2): if `φ ∈ Γ₀(ℋ)` and `r ∈ sri (L (dom φ))`, then the fixed-point set of
`v ↦ r + v - L (Prox_φ (z - L^* v))` is nonempty. -/
theorem fixedPoints_proximalConstraintDualMap_nonempty_of_mem_sri_image_effectiveDomain
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K)
    (hsri : r ∈ sri (L '' effectiveDomain φ)) :
    (Function.fixedPoints (proximalConstraintDualMap φ hφ z r L)).Nonempty := sorry

-- Proof sketch: again specialize Proposition 19.5 to the indicator of `{0}`. A fixed point gives
-- the feasibility relation `L (Prox_φ (z - L^* v)) = r` by
-- `mem_fixedPoints_proximalConstraintDualMap_iff`, and Proposition 19.5 then identifies the
-- constrained minimizer set with the singleton containing that proximal point.
/-- Corollary 19.7 (3): for every fixed point `v` of `v ↦ r + v - L (Prox_φ (z - L^* v))`, the
unique minimizer of `φ(x) + (1 / 2) ‖x - z‖²` subject to `Lx = r` is
`Prox_φ (z - L^* v)`. -/
theorem argminOn_eq_singleton_proximityOperator_of_mem_fixedPoints_proximalConstraintDualMap
    {φ : H → Set.Ioi (⊥ : EReal)} (hφ : φ ∈ Γ₀(H))
    (z : H) (r : K) (L : H →L[ℝ] K) {v : K}
    (hv : v ∈ Function.fixedPoints (proximalConstraintDualMap φ hφ z r L)) :
    Argmin[L ⁻¹' ({r} : Set K)]
      (fun x : H ↦ (φ x : EReal) + ((((1 / 2 : ℝ) * ‖x - z‖ ^ 2 : ℝ) : EReal))) =
        ({Prox[φ, hφ] (z - L.adjoint v)} :
          Set H) := sorry

end PrimalSolutionsViaDualSolutions

end ERealFunction
