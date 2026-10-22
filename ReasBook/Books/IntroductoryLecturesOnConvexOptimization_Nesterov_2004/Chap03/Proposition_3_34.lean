/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped PointwiseGrowthFunction

/- Proposition 3.34 lies in the chapter's pointwise-growth / local-modulus domain.

Primary mathematical domain:
- supremal growth profiles of a real-valued function around a base point on a metric space.

Sampled owner-style declarations:
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, the chapter owner for `ω_f(xBar; t)`;
- `pointwiseGrowthFunction_eq_zero_of_neg` in `Lemma_3_2_1`, the owner negative-radius
  simplification;
- `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`, the first comparison
  theorem derived from the same owner;
- `bestFunctionValueGapUpTo_le_modulusAtBestRadius` in `Lemma_3_2_2`, a downstream theorem that
  consumes a monotone modulus owner directly.

Best owner abstraction:
- `pointwiseGrowthFunction`

Primitive data:
- a real-valued function `f : X → ℝ`;
- a base point `xBar : X`;
- a radius parameter `t : ℝ`.

Derived API:
- the nonpositive-radius vanishing formula;
- monotonicity in the radius parameter;
- the pointwise increment bound at radius `dist x xBar`.

Source/core/bridge triage:
- source-facing: Proposition 3.34's three elementary facts about the textbook growth profile
  `ω_f(xBar; t)`;
- core/canonical: `pointwiseGrowthFunction`;
- bridge/view: the radius-zero simplification and the closed-ball membership
  `x ∈ Metric.closedBall xBar (dist x xBar)`.

This file stays at the derived-API layer over the owner `pointwiseGrowthFunction`. The previous
pipeline stub already had the correct owner-facing statement shapes, so the refinement is to prove
those consequences directly from the owner definition rather than introducing any parallel local
modulus wrapper.
-/

section

variable {X : Type u} [MetricSpace X]

/-- Proposition 3.34 (1): the pointwise growth function `ω_f(xBar; t)` vanishes for every
nonpositive radius `t`. -/
-- Proof sketch: if `t < 0`, this is exactly the negative-radius clause in the definition of
-- `pointwiseGrowthFunction`. If `t = 0`, the closed ball of radius `0` is `{xBar}`, so the
-- defining supremum is the singleton value `f xBar - f xBar = 0`.
theorem pointwiseGrowthFunction_eq_zero_of_nonpos
    (f : X → ℝ) (xBar : X) (t : ℝ) (ht : t ≤ 0) :
    ω[f; xBar] t = 0 := by
  by_cases hneg : t < 0
  · exact pointwiseGrowthFunction_eq_zero_of_neg hneg
  · have ht0 : t = 0 := le_antisymm ht (le_of_not_gt hneg)
    subst ht0
    simp [pointwiseGrowthFunction]

/-- Proposition 3.34 (2): the function `t ↦ ω_f(xBar; t)` is monotone nondecreasing in the
radius parameter. -/
-- Proof sketch: for `t₁ ≤ t₂`, the closed ball `Metric.closedBall xBar t₁` is contained in
-- `Metric.closedBall xBar t₂`, so taking the supremum of `f y - f xBar` over the larger set can
-- only increase the value. The nonpositive-radius case is handled by the previous zero formula.
theorem pointwiseGrowthFunction_monotone
    (f : X → ℝ) (xBar : X) :
    Monotone (ω[f; xBar]) := by
  let S : ℝ → Set (WithTop ℝ) :=
    fun t ↦ (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ)) '' Metric.closedBall xBar t
  intro t₁ t₂ ht
  by_cases ht₁_nonneg : 0 ≤ t₁
  · have ht₂_nonneg : 0 ≤ t₂ := le_trans ht₁_nonneg ht
    rw [pointwiseGrowthFunction, if_pos ht₁_nonneg, pointwiseGrowthFunction, if_pos ht₂_nonneg]
    change sSup (S t₁) ≤ sSup (S t₂)
    refine csSup_le_csSup ?_ ?_ ?_
    · exact ⟨⊤, fun _ _ ↦ le_top⟩
    · refine ⟨0, ?_⟩
      simpa [S] using Set.mem_image_of_mem
        (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
        (Metric.mem_closedBall_self ht₁_nonneg)
    · rintro _ ⟨y, hy, rfl⟩
      exact Set.mem_image_of_mem _ (Metric.closedBall_subset_closedBall ht hy)
  · rw [pointwiseGrowthFunction_eq_zero_of_nonpos f xBar t₁ (le_of_not_ge ht₁_nonneg)]
    by_cases ht₂_nonneg : 0 ≤ t₂
    · rw [pointwiseGrowthFunction, if_pos ht₂_nonneg]
      have hzero_mem : (0 : WithTop ℝ) ∈ S t₂ := by
        simpa [S] using Set.mem_image_of_mem
          (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
          (Metric.mem_closedBall_self ht₂_nonneg)
      exact le_csSup ⟨⊤, fun _ _ ↦ le_top⟩ hzero_mem
    · rw [pointwiseGrowthFunction_eq_zero_of_nonpos f xBar t₂ (le_of_not_ge ht₂_nonneg)]

/-- Proposition 3.34 (3): every increment `f x - f xBar` is bounded above by the pointwise growth
function evaluated at the distance from `x` to `xBar`. -/
-- Proof sketch: with `t = dist x xBar`, the point `x` belongs to `Metric.closedBall xBar t`, so
-- the defining supremum of `pointwiseGrowthFunction f xBar t` is at least the value
-- `f x - f xBar`.
theorem sub_le_pointwiseGrowthFunction_dist
    (f : X → ℝ) (xBar x : X) :
    f x - f xBar ≤ ω[f; xBar] (dist x xBar) := by
  rw [pointwiseGrowthFunction, if_pos dist_nonneg]
  have hx : x ∈ Metric.closedBall xBar (dist x xBar) := by
    simp [Metric.mem_closedBall]
  exact
    le_csSup
      ⟨⊤, fun _ _ ↦ le_top⟩
      (Set.mem_image_of_mem
        (fun y : X ↦ ((f y - f xBar : ℝ) : WithTop ℝ))
        hx)

end
