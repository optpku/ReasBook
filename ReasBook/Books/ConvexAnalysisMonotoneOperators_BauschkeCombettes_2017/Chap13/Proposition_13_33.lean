/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_35
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap13.Definition_13_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace

universe u v

namespace ERealFunction

noncomputable section

section PartialInfimum

variable {H : Type u} {K : Type v}

/-- Specializing the canonical infimal postcomposition `Prod.fst ▷ F` recovers the partial
infimum of `F` over the second variable. -/
theorem infimalPostcomposition_fst_apply (F : H × K → EReal) (x : H) :
    (Prod.fst ▷ F) x = ⨅ y : K, F (x, y) := by
  change sInf (F '' (Prod.fst ⁻¹' ({x} : Set H))) = _
  rw [show F '' (Prod.fst ⁻¹' ({x} : Set H)) = Set.range (fun y : K ↦ F (x, y)) by
    ext z
    constructor
    · rintro ⟨⟨a, b⟩, ha, rfl⟩
      refine ⟨b, ?_⟩
      simp at ha
      simp [ha]
    · rintro ⟨y, rfl⟩
      exact ⟨(x, y), by simp, rfl⟩]
  exact sInf_range

/-- The source-facing marginal function is the infimal postcomposition of `F` along the first
projection. -/
theorem marginalFunction_eq_infimalPostcomposition_fst
    (F : H × K → Set.Ioi (⊥ : EReal)) :
    marginalFunction F = Prod.fst ▷ F := by
  funext x
  simpa [marginalFunction] using (infimalPostcomposition_fst_apply F.asEReal x).symm

end PartialInfimum

section PartialInfimumConjugation

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax

variable {H : Type u} {K : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]

attribute [local instance] ERealFunction.prod_pseudoMetricSpace_l2
attribute [local instance] ERealFunction.prod_normedAddCommGroup_l2
attribute [local instance] ERealFunction.prod_normedSpace_l2
attribute [local instance] ERealFunction.prod_innerProductSpace_l2

-- Proof sketch: expand both conjugates. The left-hand side becomes a supremum over `x` of
-- `⟪x, u⟫ - inf_y F (x, y)`, which is the same as the supremum over pairs `(x, y)` of
-- `⟪x, u⟫ + ⟪y, 0⟫ - F (x, y)`. This is exactly the product-space conjugate of `F` at `(u, 0)`.
/-- Proposition 13.33: if `f(x) = inf_{y ∈ K} F(x, y)`, then the conjugate of `f` equals the
canonical Hilbert-product conjugate of `F` along the slice `u ↦ (u, 0)`. -/
theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond
    (F : H × K → EReal) :
    (Prod.fst ▷ F)∗ =
      fun u ↦ F∗ (u, (0 : K)) := sorry

/-- Evaluating Proposition 13.33 at `u` recovers the pointwise conjugacy formula. -/
theorem conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond_apply
    (F : H × K → EReal) (u : H) :
    (Prod.fst ▷ F)∗ u =
      F∗ (u, (0 : K)) := by
  simpa using
    congrFun (conjugate_infimalPostcomposition_fst_eq_conjugate_zeroSecond F) u

end PartialInfimumConjugation

end

end ERealFunction
