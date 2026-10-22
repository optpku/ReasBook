/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Definition_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section PartialInfimumSubdifferential

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: unfold both subdifferential memberships into the defining affine-minorant
-- inequalities. In the forward direction, test the marginal subgradient inequality at the first
-- coordinate of a pair and dominate the marginal value there by the chosen fiber value. In the
-- reverse direction, test the product-space subgradient inequality on every pair `(x', y')` and
-- take the infimum over the second coordinate.
/-- Proposition 16.59: if the marginal function of `F` over the second variable is attained at
`(x, y)`, then `u` belongs to the subdifferential of that marginal at `x` exactly when `(u, 0)`
belongs to the product-space subdifferential of `F` at `(x, y)`. -/
theorem mem_subdifferential_marginalFunction_iff_mem_subdifferential_zeroSecond_of_value_eq
    (F : H × K → Set.Ioi (⊥ : EReal)) (x : H) (y : K)
    (hxy : marginalFunction F x = (F (x, y) : EReal))
    (u : H) :
    u ∈ (∂ marginalFunction F) x ↔
      (u, (0 : K)) ∈ (∂ F) (x, y) := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hu p
    rcases p with ⟨x', y'⟩
    have hux :
        (⟪x' - x, u⟫_ℝ : EReal) + marginalFunction F x ≤ marginalFunction F x' :=
      hu x'
    have hFy : marginalFunction F x' ≤ (F (x', y') : EReal) := marginalFunction_le F x' y'
    change
      (((⟪x' - x, u⟫_ℝ + ⟪y' - y, (0 : K)⟫_ℝ : ℝ) : EReal) + (F (x, y) : EReal) ≤
        (F (x', y') : EReal))
    simpa [hxy] using le_trans hux hFy
  · intro hu x'
    change
      (⟪x' - x, u⟫_ℝ : EReal) + marginalFunction F x ≤
        sInf (Set.range fun y' : K ↦ (F (x', y') : EReal))
    refine le_sInf ?_
    rintro _ ⟨y', rfl⟩
    have hxy' := hu (x', y')
    change
      (((⟪x' - x, u⟫_ℝ + ⟪y' - y, (0 : K)⟫_ℝ : ℝ) : EReal) + (F (x, y) : EReal) ≤
        (F (x', y') : EReal)) at hxy'
    simpa [hxy] using hxy'

end PartialInfimumSubdifferential

end

end ERealFunction
