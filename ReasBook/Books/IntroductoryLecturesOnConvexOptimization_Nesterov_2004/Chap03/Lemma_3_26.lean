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

open scoped PointwiseGrowthFunction

universe u

section

variable {X : Type u} [MetricSpace X] {Q : Set X}

/- Lemma 3.26 lies in the chapter's pointwise-growth / best-value-gap domain.

Sampled owner-style declarations:
- `pointwiseGrowthFunction` in `Lemma_3_2_1`, the owner growth profile on a metric space
- `pointwiseGrowthFunction_monotone` in `Proposition_3_34`, the radius-monotonicity theorem for
  the owner growth profile
- `sub_le_pointwiseGrowthFunction_dist` in `Proposition_3_34`, the owner pointwise comparison at
  the metric distance
- `bestRadiusUpTo` in `Theorem_3_2_10`, the chapter source-facing owner for the best sampled
  radius
- `bestFunctionValueGapUpTo_le_modulusAtBestRadius` in `Lemma_3_2_2`, the owner best-value
  comparison for a monotone modulus

Best owner abstraction:
- `pointwiseGrowthFunction`

Primitive data:
- a restricted objective `f : ↥Q → ℝ`
- a subtype-valued sample history `xSeq : ℕ → ↥Q`
- a reference point `xStar : ↥Q`

Derived API:
- the best-value bound obtained by applying the owner theorem directly to the subtype `↥Q`
- the pointwise comparison `sub_le_pointwiseGrowthFunction_dist` specialized to `↥Q`

Source/core/bridge triage:
- source-facing: Lemma 3.26's best sampled-value gap bound on the feasible set `Q`, stated for an
  arbitrary reference point and hence specializing to the textbook minimizer case
- core/canonical: `pointwiseGrowthFunction` and
  `bestFunctionValueGapUpTo_le_modulusAtBestRadius`
- bridge/view: the specialization of the owner growth profile to the subtype `↥Q`

This file specializes the owner theorem
`bestFunctionValueGapUpTo_le_modulusAtBestRadius` directly to the subtype metric space `↥Q`. Its
public surface is just that source-facing specialization, stated with the canonical owner
expression `pointwiseGrowthFunction f xStar` and no redundant local wrapper or extra optimality
binder.
-/

/-- Lemma 3.26: for any reference point `xStar ∈ Q`, the best objective-value gap above `f xStar`
among the sample points `x₀, …, x_k` is bounded by the pointwise growth function of the
restricted objective, evaluated at the best sampled distance to `xStar`. The growth function is
`WithTop ℝ`-valued so that unbounded ball-growth is represented by `⊤`. In particular, this
recovers the textbook minimizer formulation when `xStar` is optimal on `Q`. -/
-- Proof sketch: apply `bestFunctionValueGapUpTo_le_modulusAtBestRadius` directly on the subtype
-- `↥Q`, with modulus `pointwiseGrowthFunction f xStar` and radius sequence
-- `i ↦ dist (xSeq i) xStar`. The required pointwise bound is exactly
-- `sub_le_pointwiseGrowthFunction_dist` on the subtype metric space.
theorem bestFunctionValueUpTo_sub_le_pointwiseGrowthFunction_at_bestRadius
    (f : ↥Q → ℝ) (xSeq : ℕ → ↥Q) (xStar : ↥Q) (k : ℕ) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) k - f xStar ≤
      ω[f; xStar] (bestRadiusUpTo (fun i ↦ dist (xSeq i) xStar) k) := by
  simpa using
    bestFunctionValueGapUpTo_le_modulusAtBestRadius
      f
      (ω[f; xStar])
      (pointwiseGrowthFunction_monotone f xStar)
      xSeq xStar (fun i ↦ dist (xSeq i) xStar) k
      (fun i ↦ sub_le_pointwiseGrowthFunction_dist f xStar (xSeq i))

end

end
