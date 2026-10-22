/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_3_extra_1

namespace InteriorPointPenaltyProblem

variable {Point : Type*} {ι : Type*} [Fintype ι]

-- Semantic recall: `IsMinOn` is the canonical mathlib minimizer API, and
-- `Definition_10_3_extra_1` now owns the strict-feasible and penalty-function surfaces.

section

variable (problem : InteriorPointPenaltyProblem Point ι) (x : ℝ → Point)

private theorem barrierSum_nonneg
    (hpositive : problem.HasPositiveBarrierValues)
    {x : Point} (hx : x ∈ problem.strictFeasibleSet) :
    0 ≤ problem.barrierSum x := by
  classical
  rw [problem.barrierSum_apply]
  exact Finset.sum_nonneg fun i _ ↦ le_of_lt (hpositive (hx i))

/-- If the barrier stays positive on the positive half-line and `x σ` minimizes the Chapter 10
interior-point penalty subproblem for every `σ > 0`, then the attained penalty value
`problem.penaltyFunction σ (x σ)` is antitone in the barrier parameter. -/
theorem penaltyValue_antitone
    (hpositive : problem.HasPositiveBarrierValues)
    (hx : ∀ {σ : ℝ}, 0 < σ →
      x σ ∈ problem.strictFeasibleSet ∧
        IsMinOn (problem.penaltyFunction σ) problem.strictFeasibleSet (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    problem.penaltyFunction σ₂ (x σ₂) ≤ problem.penaltyFunction σ₁ (x σ₁) := by
  have hσ₂ : 0 < σ₂ := lt_trans hσ₁ hσ₁₂
  have hmin₂₁ :=
    (isMinOn_iff.mp (hx hσ₂).2) (x σ₁) (hx hσ₁).1
  have hmin₂₁' :
      problem.objective (x σ₂) + (1 / σ₂) * problem.barrierSum (x σ₂) ≤
        problem.objective (x σ₁) + (1 / σ₂) * problem.barrierSum (x σ₁) := by
    simpa [InteriorPointPenaltyProblem.penaltyFunction] using hmin₂₁
  have hbarrier :
      (1 / σ₂) * problem.barrierSum (x σ₁) ≤
        (1 / σ₁) * problem.barrierSum (x σ₁) := by
    have h_inv : 1 / σ₂ ≤ 1 / σ₁ := (one_div_lt_one_div_of_lt hσ₁ hσ₁₂).le
    exact mul_le_mul_of_nonneg_right h_inv
      (barrierSum_nonneg problem hpositive (hx hσ₁).1)
  change problem.objective (x σ₂) + (1 / σ₂) * problem.barrierSum (x σ₂) ≤
      problem.objective (x σ₁) + (1 / σ₁) * problem.barrierSum (x σ₁)
  linarith

/-- Chapter10 Lemma 10.3.1 (2): under the same interior-point penalty minimizer hypotheses, the
source barrier sum `problem.barrierSum (x σ)` is monotone in the opposite direction, so
`problem.barrierSum (x σ₂) ≥ problem.barrierSum (x σ₁)` whenever `0 < σ₁ < σ₂`. -/
theorem barrierSum_monotone
    (hx : ∀ {σ : ℝ}, 0 < σ →
      x σ ∈ problem.strictFeasibleSet ∧
        IsMinOn (problem.penaltyFunction σ) problem.strictFeasibleSet (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    problem.barrierSum (x σ₂) ≥ problem.barrierSum (x σ₁) := by
  have hσ₂ : 0 < σ₂ := lt_trans hσ₁ hσ₁₂
  have hmin₁₂ :=
    (isMinOn_iff.mp (hx hσ₁).2) (x σ₂) (hx hσ₂).1
  have hmin₂₁ :=
    (isMinOn_iff.mp (hx hσ₂).2) (x σ₁) (hx hσ₁).1
  have hmin₁₂' :
      problem.objective (x σ₁) + (1 / σ₁) * problem.barrierSum (x σ₁) ≤
        problem.objective (x σ₂) + (1 / σ₁) * problem.barrierSum (x σ₂) := by
    simpa [InteriorPointPenaltyProblem.penaltyFunction] using hmin₁₂
  have hmin₂₁' :
      problem.objective (x σ₂) + (1 / σ₂) * problem.barrierSum (x σ₂) ≤
        problem.objective (x σ₁) + (1 / σ₂) * problem.barrierSum (x σ₁) := by
    simpa [InteriorPointPenaltyProblem.penaltyFunction] using hmin₂₁
  have hproduct :
      0 ≤
        (1 / σ₁ - 1 / σ₂) *
          (problem.barrierSum (x σ₂) - problem.barrierSum (x σ₁)) := by
    nlinarith
  have hcoeff : 0 < 1 / σ₁ - 1 / σ₂ := by
    have h_inv : 1 / σ₂ < 1 / σ₁ := one_div_lt_one_div_of_lt hσ₁ hσ₁₂
    linarith
  nlinarith

/-- Chapter10 Lemma 10.3.1 (1): if `x σ` minimizes the Chapter 10 interior-point penalty
subproblem for every `σ > 0`, then `problem.objective (x σ)` is antitone in the barrier
parameter, so `problem.objective (x σ₂) ≤ problem.objective (x σ₁)` whenever
`0 < σ₁ < σ₂`. -/
theorem objective_antitone
    (hx : ∀ {σ : ℝ}, 0 < σ →
      x σ ∈ problem.strictFeasibleSet ∧
        IsMinOn (problem.penaltyFunction σ) problem.strictFeasibleSet (x σ))
    {σ₁ σ₂ : ℝ} (hσ₁ : 0 < σ₁) (hσ₁₂ : σ₁ < σ₂) :
    problem.objective (x σ₂) ≤ problem.objective (x σ₁) := by
  have hσ₂ : 0 < σ₂ := lt_trans hσ₁ hσ₁₂
  have hbarrier :=
    barrierSum_monotone problem x hx hσ₁ hσ₁₂
  have hmin₂₁ :=
    (isMinOn_iff.mp (hx hσ₂).2) (x σ₁) (hx hσ₁).1
  have hmin₂₁' :
      problem.objective (x σ₂) + (1 / σ₂) * problem.barrierSum (x σ₂) ≤
        problem.objective (x σ₁) + (1 / σ₂) * problem.barrierSum (x σ₁) := by
    simpa [InteriorPointPenaltyProblem.penaltyFunction] using hmin₂₁
  have hscaled :
      (1 / σ₂) * problem.barrierSum (x σ₁) ≤
        (1 / σ₂) * problem.barrierSum (x σ₂) := by
    have hσ₂_inv_nonneg : 0 ≤ 1 / σ₂ := by positivity
    exact mul_le_mul_of_nonneg_left hbarrier hσ₂_inv_nonneg
  linarith

end

end InteriorPointPenaltyProblem
