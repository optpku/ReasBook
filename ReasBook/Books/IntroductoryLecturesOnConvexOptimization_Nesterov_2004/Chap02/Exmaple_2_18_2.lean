/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin

/- This item is source-facing in one-dimensional constrained optimization.

Sampled owner-style declarations:
* `argmin[Q] f` and `mem_constrainedArgmin_iff`
* `Set.Ici`
* `IsMinOn`
* `deriv`
* `deriv_id`

Best owner abstraction:
* source-facing: the boundary-point minimizer and derivative facts for the concrete problem
  `min_{x ≥ 0} x`
* core/canonical: `0 ∈ argmin[Set.Ici 0] (id : ℝ → ℝ)` and `deriv (id : ℝ → ℝ) 0`
* bridge/view: `mem_constrainedArgmin_iff`, `isMinOn_iff`, and `deriv_id`

The example is not introducing a new optimization wrapper; it is recording a concrete feasible
set, objective, minimizer, and derivative behavior. -/

/-- Helper for Exmaple 2.18.2: the boundary point `0` minimizes the identity objective on the
feasible ray `Set.Ici 0`, i.e. `0 ∈ argmin[Set.Ici 0] (id : ℝ → ℝ)`. -/
theorem nonnegativeLinearProblem_zero_mem_argmin :
    0 ∈ argmin[Set.Ici 0] (id : ℝ → ℝ) := by
  -- Rewrite argmin membership into feasibility plus the global minimizing property on `Set.Ici 0`.
  rw [mem_constrainedArgmin_iff]
  constructor
  · simp
  -- On the feasible ray, every point `y` satisfies `0 ≤ y`, so the identity objective is minimal at `0`.
  · simp [isMinOn_iff]

/-- Helper for Exmaple 2.18.2: the argmin statement for `\min_{x \ge 0} x` yields the usual
`IsMinOn` formulation on the feasible ray. -/
theorem nonnegativeLinearProblem_zero_isMinOn :
    IsMinOn (id : ℝ → ℝ) (Set.Ici 0) 0 := by
  -- Extract the minimizing-property component from the argmin membership characterization.
  exact (mem_constrainedArgmin_iff.mp nonnegativeLinearProblem_zero_mem_argmin).2

/-- Helper for Exmaple 2.18.2: at the boundary minimizer of `\min_{x \ge 0} x`, the derivative
of the identity objective is still strictly positive. -/
theorem nonnegativeLinearProblem_deriv_pos_at_zero :
    0 < deriv (id : ℝ → ℝ) 0 := by
  -- The objective is the identity map, whose derivative is constantly `1`.
  norm_num [deriv_id]

/-- Exmaple 2.18.2: for the constrained problem `\min_{x \ge 0} x`, the boundary point `0`
belongs to the constrained minimizer set even though the derivative there is strictly positive. -/
theorem nonnegativeLinearProblem_zero_mem_argmin_and_deriv_pos :
    0 ∈ argmin[Set.Ici 0] (id : ℝ → ℝ) ∧ 0 < deriv (id : ℝ → ℝ) 0 := by
  -- Combine the constrained minimizer fact with the derivative computation from the source proof.
  exact ⟨nonnegativeLinearProblem_zero_mem_argmin, nonnegativeLinearProblem_deriv_pos_at_zero⟩
