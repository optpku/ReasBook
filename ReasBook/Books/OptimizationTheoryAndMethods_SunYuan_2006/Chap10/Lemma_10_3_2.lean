/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_3_extra_1

namespace InteriorPointPenaltyProblem

variable {Point : Type*} {ι : Type*} [Fintype ι]

-- Semantic recall: `IsMinOn` is the canonical minimizer API, while
-- `Definition_10_3_extra_1` now owns the barrier sum and strict-feasible-region surfaces.

/-- Chapter10 Lemma 10.3.2: if `δ = problem.barrierSum xσ` for a solution `xσ` of the
interior-point penalty subproblem with parameter `σ > 0`, and if the budget condition
`problem.barrierSum x ≤ δ` forces strict feasibility, then `xσ` also solves
`min problem.objective x` subject to `problem.barrierSum x ≤ δ`. -/
theorem isMinOnObjectiveOnBarrierBudgetSet
    (problem : InteriorPointPenaltyProblem Point ι)
    {σ : ℝ} (hσ : 0 < σ) (xσ : Point)
    (hxσ : IsMinOn (problem.penaltyFunction σ) problem.strictFeasibleSet xσ)
    (h_budget_strict :
      ∀ ⦃x : Point⦄,
        problem.barrierSum x ≤ problem.barrierSum xσ → x ∈ problem.strictFeasibleSet) :
    IsMinOn
      problem.objective
      {x | problem.barrierSum x ≤ problem.barrierSum xσ}
      xσ := by
  refine isMinOn_iff.mpr ?_
  intro x hx
  have hpenalty := (isMinOn_iff.mp hxσ) x (h_budget_strict hx)
  have hpenalty' :
      problem.objective xσ + (1 / σ) * problem.barrierSum xσ ≤
        problem.objective x + (1 / σ) * problem.barrierSum x := by
    simpa [InteriorPointPenaltyProblem.penaltyFunction] using hpenalty
  have hscaled :
      (1 / σ) * problem.barrierSum x ≤ (1 / σ) * problem.barrierSum xσ := by
    have hσ_inv_nonneg : 0 ≤ 1 / σ := by
      positivity
    exact mul_le_mul_of_nonneg_left hx hσ_inv_nonneg
  linarith

end InteriorPointPenaltyProblem
