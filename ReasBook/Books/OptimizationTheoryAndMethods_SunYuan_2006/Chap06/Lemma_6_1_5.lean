/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Lemma_6_1_4

noncomputable section

open scoped Matrix.Norms.L2Operator

variable {n : ℕ}

namespace TrustRegionSubproblem

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-
Chapter 6 already owns the trust-region subproblem data, the quadratic model `q^(k)`,
the feasible set, the Cauchy point, and the operator norm `‖B_k‖₂` through
`Definition_6_1_extra_1`, `Definition_6_1_extra_3`, and `Lemma_6_1_4`. This file keeps only the
source-facing approximate-solution predicates from Lemma 6.1.5 and states the lower bound on
that canonical owner surface.
-/

/-- A step satisfies branch `(6.1.38)` when its quadratic-model value is no larger than at the
Cauchy point. Equivalently, its predicted reduction is at least the Cauchy predicted reduction. -/
def hasCauchyModelUpperBound (P : TrustRegionSubproblem n) (step : Point) : Prop :=
  P step ≤ P P.cauchyPoint

/-- A step has a fraction `β₂` of the Cauchy predicted reduction when its model decrease is at
least `β₂` times the predicted reduction at the Cauchy point; this is the branch corresponding to
`(6.1.39)`. -/
def hasFractionCauchyDecrease
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point) : Prop :=
  β₂ * P.predictedReduction P.cauchyPoint ≤ P.predictedReduction step

/-- A source-facing approximate trust-region step is feasible and satisfies `(6.1.38)` or
`(6.1.39)`. -/
def isApproximateSolution
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point) : Prop :=
  step ∈ P.feasibleSet ∧
    (P.hasCauchyModelUpperBound step ∨ P.hasFractionCauchyDecrease β₂ step)

/-- The approximate-solution condition is exactly feasibility together with branch `(6.1.38)` or
branch `(6.1.39)`. -/
theorem isApproximateSolution_iff
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point) :
    P.isApproximateSolution β₂ step ↔
      step ∈ P.feasibleSet ∧
        (P.hasCauchyModelUpperBound step ∨ P.hasFractionCauchyDecrease β₂ step) :=
  Iff.rfl

/-- Branch `(6.1.38)` says that the predicted reduction at `step` is at least the predicted
reduction at the Cauchy point. -/
theorem predictedReduction_cauchyPoint_le_of_hasCauchyModelUpperBound
    (P : TrustRegionSubproblem n) (step : Point)
    (hstep : P.hasCauchyModelUpperBound step) :
    P.predictedReduction P.cauchyPoint ≤ P.predictedReduction step := by
  simpa [hasCauchyModelUpperBound, TrustRegionSubproblem.predictedReduction_eq] using
    sub_le_sub_left hstep (P 0)

/-- Chapter06 Lemma 6.1.5: if `step` is an approximate solution of `(6.1.1)`, then its predicted
reduction satisfies
`Pred_k = q^(k) 0 - q^(k) step ≥ (1 / 2) * β₂ * ‖g_k‖ * min {Δ_k, ‖g_k‖ / ‖B_k‖₂}`,
where `‖B_k‖₂` is `P.hessianOperatorNorm`. To avoid Lean's `/ 0 = 0` convention from silently
weakening the source statement, the `‖B_k‖₂ = 0` branch is stated explicitly as in
`Chapter06 Lemma 6.1.4`. -/
theorem predictedReductionLowerBound_of_hasFractionCauchyDecrease
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point)
    (hβ₂ : β₂ ∈ Set.Ioc (0 : ℝ) 1)
    (hstep : P.hasFractionCauchyDecrease β₂ step) :
    (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) ≤
      P.predictedReduction step := by
  have hscaled :
      (if hB : P.hessianOperatorNorm = 0 then
          (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius
        else
          (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ *
            min P.radius (‖P.gradient‖ / P.hessianOperatorNorm)) ≤
        P.predictedReduction step :=
    le_trans (P.cauchyPointPredictedReductionLowerBoundScaled β₂ hβ₂.1.le) hstep
  by_cases hB : P.hessianOperatorNorm = 0
  · have hnonneg :
        0 ≤ (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius :=
      mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) hβ₂.1.le) (norm_nonneg _))
        P.radius_pos.le
    have hmin :
        min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) = 0 := by
      rw [hB, div_zero]
      exact min_eq_right P.radius_pos.le
    calc
      (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * min P.radius (‖P.gradient‖ / P.hessianOperatorNorm)
          = 0 := by rw [hmin]; simp
      _ ≤ (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius := hnonneg
      _ ≤ P.predictedReduction step := by simpa [hB] using hscaled
  · simpa [hB] using hscaled

/-- Chapter06 Lemma 6.1.5: if `step` is an approximate solution of `(6.1.1)`, then its predicted
reduction satisfies
`Pred_k = q^(k) 0 - q^(k) step ≥ (1 / 2) * β₂ * ‖g_k‖ * min {Δ_k, ‖g_k‖ / ‖B_k‖₂}`,
where `‖B_k‖₂` is `P.hessianOperatorNorm`. To avoid Lean's `/ 0 = 0` convention from silently
weakening the source statement, the `‖B_k‖₂ = 0` branch is stated explicitly as in
`Chapter06 Lemma 6.1.4`. -/
theorem predictedReductionLowerBound_ofApproximateSolution
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point)
    (hβ₂ : β₂ ∈ Set.Ioc (0 : ℝ) 1)
    (hstep : P.isApproximateSolution β₂ step) :
    P.predictedReduction step ≥
      if _ : P.hessianOperatorNorm = 0 then
        (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius
      else
        (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ *
          min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
  have hcauchy_lower_nonneg :
      0 ≤
        if hB : P.hessianOperatorNorm = 0 then
          (1 / 2 : ℝ) * ‖P.gradient‖ * P.radius
        else
          (1 / 2 : ℝ) * ‖P.gradient‖ *
            min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
    by_cases hB : P.hessianOperatorNorm = 0
    · simpa [hB] using
        mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (norm_nonneg _))
          P.radius_pos.le
    · have hnormB_nonneg : 0 ≤ P.hessianOperatorNorm := by
        simp [TrustRegionSubproblem.hessianOperatorNorm_eq]
      have hquot_nonneg : 0 ≤ ‖P.gradient‖ / P.hessianOperatorNorm :=
        div_nonneg (norm_nonneg _) hnormB_nonneg
      have hmin_nonneg :
          0 ≤ min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) :=
        le_min P.radius_pos.le hquot_nonneg
      simpa [hB] using
        mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (1 / 2 : ℝ)) (norm_nonneg _))
          hmin_nonneg
  have hcauchy_nonneg : 0 ≤ P.predictedReduction P.cauchyPoint :=
    le_trans hcauchy_lower_nonneg P.cauchyPointPredictedReductionLowerBound
  have hβ₂_mul_cauchy_le :
      β₂ * P.predictedReduction P.cauchyPoint ≤ P.predictedReduction P.cauchyPoint := by
    simpa using mul_le_mul_of_nonneg_right hβ₂.2 hcauchy_nonneg
  rcases hstep with ⟨_, hstep | hstep⟩
  · exact le_trans
      (P.cauchyPointPredictedReductionLowerBoundScaled β₂ hβ₂.1.le)
      (le_trans hβ₂_mul_cauchy_le <|
        P.predictedReduction_cauchyPoint_le_of_hasCauchyModelUpperBound step hstep)
  · exact le_trans
      (P.cauchyPointPredictedReductionLowerBoundScaled β₂ hβ₂.1.le) hstep

/-- Under the nondegenerate hypotheses `0 < β₂` and `‖g_k‖ > 0`, an approximate trust-region
step has strictly positive predicted reduction. -/
theorem predictedReduction_pos_of_isApproximateSolution
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point)
    (hβ₂ : β₂ ∈ Set.Ioc (0 : ℝ) 1)
    (hgrad : 0 < ‖P.gradient‖)
    (hstep : P.isApproximateSolution β₂ step) :
    0 < P.predictedReduction step := by
  have hbound := P.predictedReductionLowerBound_ofApproximateSolution β₂ step hβ₂ hstep
  have hlower_pos :
      0 <
        if hB : P.hessianOperatorNorm = 0 then
          (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius
        else
          (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ *
            min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) := by
    by_cases hB : P.hessianOperatorNorm = 0
    · simpa [hB] using
        mul_pos
          (mul_pos (mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) hβ₂.1) hgrad)
          P.radius_pos
    · have hnormB_nonneg : 0 ≤ P.hessianOperatorNorm := by
        simp [TrustRegionSubproblem.hessianOperatorNorm_eq]
      have hnormB_pos : 0 < P.hessianOperatorNorm :=
        lt_of_le_of_ne hnormB_nonneg (Ne.symm hB)
      have hquot_pos : 0 < ‖P.gradient‖ / P.hessianOperatorNorm :=
        div_pos hgrad hnormB_pos
      have hmin_pos : 0 < min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) :=
        lt_min P.radius_pos hquot_pos
      simpa [hB] using
        mul_pos
          (mul_pos (mul_pos (by norm_num : 0 < (1 / 2 : ℝ)) hβ₂.1) hgrad)
          hmin_pos
  exact lt_of_lt_of_le hlower_pos hbound

/-- The split source-facing hypotheses of Lemma 6.1.5 package into
`P.isApproximateSolution β₂ step`. -/
theorem predictedReductionLowerBound_of_feasible_and_branch
    (P : TrustRegionSubproblem n) (β₂ : ℝ) (step : Point)
    (hβ₂ : β₂ ∈ Set.Ioc (0 : ℝ) 1)
    (hstep_feasible : step ∈ P.feasibleSet)
    (hstep_branch :
      P.hasCauchyModelUpperBound step ∨ P.hasFractionCauchyDecrease β₂ step) :
    P.predictedReduction step ≥
      if _ : P.hessianOperatorNorm = 0 then
        (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ * P.radius
      else
        (1 / 2 : ℝ) * β₂ * ‖P.gradient‖ *
          min P.radius (‖P.gradient‖ / P.hessianOperatorNorm) :=
  P.predictedReductionLowerBound_ofApproximateSolution β₂ step hβ₂
    ⟨hstep_feasible, hstep_branch⟩

end TrustRegionSubproblem
