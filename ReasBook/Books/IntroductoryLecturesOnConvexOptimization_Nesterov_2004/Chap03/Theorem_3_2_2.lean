/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_34

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped PointwiseGrowthFunction SubgradientLocalizationMeasure

universe u

/- Theorem 3.2.2 lies in the chapter's subgradient-localization / best-sampled-gap domain.

Primary mathematical domain:
- real-valued convex analysis on a real inner-product space, organized around the owner
  localization measure `v[g; xStar]`, the owner growth profile `ω[f; xStar]`, and the owner
  finite prefix infimum `bestFunctionValueUpTo`.

Sampled owner-style declarations:
- `subgradientLocalizationMeasure` and
  `sub_le_pointwiseGrowthFunction_of_localizationMeasure` in `Lemma_3_2_1`;
- `bestFunctionValueGapUpTo_le_modulusAtBestRadius` in `Lemma_3_2_2`, the chapter owner theorem
  for passing pointwise bounds to a bound at the best sampled radius;
- `pointwiseGrowthFunction_monotone` in `Proposition_3_34`;
- `bestRadiusUpTo` / `bestFunctionValueUpTo` in `Definition_3_55`.

Best owner abstraction:
- source-facing: the sampled objective-gap estimate of Theorem 3.2.2;
- core/canonical: `pointwiseGrowthFunction` plus
  `bestFunctionValueGapUpTo_le_modulusAtBestRadius`;
- bridge/view: the source-facing sampled minimum `bestFunctionValueUpTo` and sampled localization
  radius `bestRadiusUpTo`.

Primitive data:
- a real-valued function `f`;
- a chosen subgradient selection `g`;
- a sample sequence `xSeq`;
- a minimizer `xStar`, outer radius `R`, Lipschitz constant `M`, and stage `k`.

Derived API:
- the best sampled gap bound.

This item does not use coordinates or finite-dimensional structure, so the ambient space is the
intrinsic real inner-product-space owner rather than the concrete model `EuclideanSpace ℝ (Fin n)`.
The positivity hypothesis on the stepsizes is also redundant here: the theorem only consumes the
already-packaged radius bound `hvk`, so the public API keeps that canonical hypothesis and drops
the unused extra guard.
-/

section

variable {X : Type u} [MetricSpace X]

/-- If `f` is `M`-Lipschitz on the closed ball `Metric.closedBall xStar R`, then the pointwise
growth function at every radius `r ∈ [0, R]` is bounded by `(M : ℝ) * r`. -/
theorem pointwiseGrowthFunction_le_lipschitz_mul_of_le_radius
    {f : X → ℝ} {xStar : X} {r R : ℝ} {M : NNReal}
    (hLip : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hr_nonneg : 0 ≤ r) (hrR : r ≤ R) :
    ω[f; xStar] r ≤ (((M : ℝ) * r : ℝ) : WithTop ℝ) := by
  rw [pointwiseGrowthFunction, if_pos hr_nonneg]
  refine csSup_le ?_ ?_
  · refine ⟨0, ?_⟩
    simpa using Set.mem_image_of_mem
      (fun y : X ↦ ((f y - f xStar : ℝ) : WithTop ℝ))
      (Metric.mem_closedBall_self hr_nonneg)
  · rintro _ ⟨y, hy, rfl⟩
    have hyR : y ∈ Metric.closedBall xStar R :=
      Metric.closedBall_subset_closedBall hrR hy
    have hxStarR : xStar ∈ Metric.closedBall xStar R :=
      Metric.mem_closedBall_self (le_trans hr_nonneg hrR)
    have hy_dist : dist y xStar ≤ r := by
      simpa [Metric.mem_closedBall] using hy
    have hy_gap : f y - f xStar ≤ (M : ℝ) * r := by
      have hy_lip : f y ≤ f xStar + (M : ℝ) * dist y xStar :=
        hLip.le_add_mul hyR hxStarR
      have hy_mul : (M : ℝ) * dist y xStar ≤ (M : ℝ) * r :=
        mul_le_mul_of_nonneg_left hy_dist M.2
      linarith
    change ((f y - f xStar : ℝ) : WithTop ℝ) ≤
        (((M : ℝ) * r : ℝ) : WithTop ℝ)
    exact_mod_cast hy_gap

end

section

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Theorem 3.2.2: if `xStar` is a global minimizer of `f`, `f` is `M`-Lipschitz on the closed
Euclidean ball `B₂(xStar, R)`, `‖x₀ - xStar‖ ≤ R`, and the minimum localization measure
`v_k^* = bestRadiusUpTo (fun i ↦ v_f(xStar; xᵢ)) k` satisfies the standard
projected-subgradient estimate
`v_k^* ≤ (R^2 + ∑_{i=0}^k h_i^2) / (2 ∑_{i=0}^k h_i)`, then the best objective gap up to step `k`
satisfies `f_k^* - f^* ≤ M * (R^2 + ∑_{i=0}^k h_i^2) / (2 ∑_{i=0}^k h_i)`, where
`f_k^* = bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k`. -/
-- Proof sketch: apply Lemma 3.2.1 pointwise to the chosen subgradient selection and then take the
-- best-so-far value over `i = 0, ..., k`, obtaining `f_k^* - f^* ≤ ω_f(xStar; v_k^*)`. Since
-- `v_k^* ≤ v_0 ≤ ‖x₀ - xStar‖ ≤ R`, the growth function on that radius is bounded by the
-- Lipschitz estimate `(M : ℝ) * v_k^*`. Substitute the assumed upper bound on `v_k^*`.
theorem bestFunctionValueGapUpTo_le_lipschitz_mul_stepsize_ratio
    {f : V → ℝ} {g : V → V}
    (hg : ∀ x : V, IsSubgradientAt (fun y ↦ (f y : WithTop ℝ)) x (g x))
    (xSeq : ℕ → V) {xStar : V} (hxStar : IsMinOn f Set.univ xStar)
    (h : ℕ → ℝ) (k : ℕ) {R : ℝ} {M : NNReal}
    (hLip : LipschitzOnWith M f (Metric.closedBall xStar R))
    (hR : ‖xSeq 0 - xStar‖ ≤ R)
    (hvk :
      bestRadiusUpTo
          (fun i ↦ v[g; xStar] (xSeq i)) k ≤
        (R ^ (2 : ℕ) + ∑ i : Fin (k + 1), (h i) ^ (2 : ℕ)) /
          (2 * ∑ i : Fin (k + 1), h i)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
      (M : ℝ) *
        ((R ^ (2 : ℕ) + ∑ i : Fin (k + 1), (h i) ^ (2 : ℕ)) /
          (2 * ∑ i : Fin (k + 1), h i)) := by
  let v : ℕ → ℝ := fun i ↦ v[g; xStar] (xSeq i)
  let rStar : ℝ := bestRadiusUpTo v k
  let ratio : ℝ :=
    (R ^ (2 : ℕ) + ∑ i : Fin (k + 1), (h i) ^ (2 : ℕ)) /
      (2 * ∑ i : Fin (k + 1), h i)
  have hxStar_le : ∀ x : V, f xStar ≤ f x := isMinOn_univ_iff.mp hxStar
  have hbest :
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) ≤
        ω[f; xStar] rStar := by
    simpa [v, rStar] using
      bestFunctionValueGapUpTo_le_modulusAtBestRadius
        f
        (ω[f; xStar])
        (pointwiseGrowthFunction_monotone f xStar)
        xSeq
        xStar
        v
        k
        (fun i ↦
          sub_le_pointwiseGrowthFunction_of_localizationMeasure
            xStar
            (xSeq i)
            (hg (xSeq i)))
  have hv_nonneg (i : Fin (k + 1)) : 0 ≤ v i := by
    dsimp [v]
    exact
      subgradientLocalizationMeasure_nonneg_of_isSubgradientAt
        (hg (xSeq i))
        (hxStar_le (xSeq i))
  have hrStar_nonneg : 0 ≤ rStar := by
    dsimp [rStar, bestRadiusUpTo]
    exact le_ciInf hv_nonneg
  have hv0_le : v 0 ≤ ‖xSeq 0 - xStar‖ := by
    dsimp [v]
    by_cases hzero : g (xSeq 0) = 0
    · simp [subgradientLocalizationMeasure, hzero]
    · rw [subgradientLocalizationMeasure_eq_inner_div_norm_of_ne_zero hzero]
      have hinner_le :
          inner ℝ (g (xSeq 0)) (xSeq 0 - xStar) ≤
            ‖g (xSeq 0)‖ * ‖xSeq 0 - xStar‖ := by
        exact le_trans (le_abs_self _) (abs_real_inner_le_norm _ _)
      have hnorm_pos : 0 < ‖g (xSeq 0)‖ := norm_pos_iff.mpr hzero
      exact
        (div_le_iff₀ hnorm_pos).2 <|
          by simpa [mul_comm] using hinner_le
  have hrStar_le_v0 : rStar ≤ v 0 := by
    have : bestFunctionValueUpTo v k ≤ v 0 := bestFunctionValueUpTo_le 0
    simpa [rStar] using this
  have hrStar_le_R : rStar ≤ R :=
    hrStar_le_v0.trans (hv0_le.trans hR)
  have hω_le :
      ω[f; xStar] rStar ≤ (((M : ℝ) * rStar : ℝ) : WithTop ℝ) := by
    exact pointwiseGrowthFunction_le_lipschitz_mul_of_le_radius hLip hrStar_nonneg hrStar_le_R
  have hrStar_le_ratio : rStar ≤ ratio := by
    simpa [v, rStar, ratio] using hvk
  have hmain :
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) ≤
        (((M : ℝ) * ratio : ℝ) : WithTop ℝ) := by
    calc
      ((bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar : ℝ) : WithTop ℝ) ≤
          ω[f; xStar] rStar := hbest
      _ ≤ (((M : ℝ) * rStar : ℝ) : WithTop ℝ) := hω_le
      _ ≤ (((M : ℝ) * ratio : ℝ) : WithTop ℝ) := by
        exact_mod_cast mul_le_mul_of_nonneg_left hrStar_le_ratio M.2
  have hmain_real :
      bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
        (M : ℝ) * ratio := by
    exact_mod_cast hmain
  simpa [ratio] using hmain_real

end
