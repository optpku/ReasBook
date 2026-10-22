/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace LagrangianProblem

variable {Q : Type u} {m : ℕ}

/- Primary domain: parameter-shift bounds for the auxiliary max-violation optimal-value function
of an inequality-constrained problem.

Owner declarations sampled before refining:
* `LagrangianProblem` in `Definition_1_10_2`, the owner carrying the primitive objective and
  constraint family on the ambient type `Q`;
* `LagrangianProblem.constrainedAuxiliaryObjective` in `Lemma_2_21`, the owner max-violation
  objective `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`;
* `LagrangianProblem.constrainedAuxiliaryOptimalValue` in `Lemma_2_21`, the owner extended-real
  value function attached to that auxiliary objective;
* `SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le` and
  `SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le` in
  `Definition_1_3_7`, the canonical feasible-set infimum comparison theorems;
* `LagrangianProblem.constrainedAuxiliaryObjective_shift_le` and
  `LagrangianProblem.constrainedAuxiliaryObjective_sub_le_shift` in `Lemma_2_21`, the pointwise
  parameter-shift bounds for the auxiliary objective.

Best owner abstraction:
* the source-facing value `f^*(t)` is the owner value
  `problem.constrainedAuxiliaryOptimalValue t`.

Primitive data:
* the owner problem `problem : LagrangianProblem Q m`;
* the scalar parameters `t` and `Δ`.

Derived API:
* the owner pointwise shift comparisons
  `problem.constrainedAuxiliaryObjective_shift_le hΔ x` and
  `problem.constrainedAuxiliaryObjective_sub_le_shift hΔ x`;
* the source-facing owner value comparison
  `problem.constrainedAuxiliaryOptimalValue_shift_bounds hΔ`.

Source/core/bridge triage:
* source-facing: Lemma 2.22's inequality between the owner values `f^*(t)` and
  `f^*(t + Δ)`;
* core/canonical: `problem.constrainedAuxiliaryOptimalValue t`;
* bridge/view: the pointwise bounds on
  `problem.constrainedAuxiliaryObjective (t + Δ)` and
  `problem.constrainedAuxiliaryObjective t`, which pass to the owner infima through the Chapter 1
  comparison theorems for `SetConstrainedMinimizationProblem.optimalValue`.

Lemma 2.22 therefore records the shift comparison directly at the owner value-function layer and
reuses the Chapter 1 optimal-value owner API instead of reproving the underlying `sInf`
monotonicity locally.
-/

/-- Lemma 2.22: increasing the parameter by `Δ ≥ 0` lowers the owner auxiliary optimal value by
at most `Δ` and never increases it. For the source value notation `f^*(t)` attached to
`x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}`, one has
`f^*(t) - Δ ≤ f^*(t + Δ) ≤ f^*(t)` at the canonical
`problem.constrainedAuxiliaryOptimalValue` level. -/
-- Proof sketch: view the two auxiliary objectives as unconstrained
-- `SetConstrainedMinimizationProblem`s on the fixed feasible set `Set.univ`. Then apply the
-- Chapter 1 comparison theorems for `optimalValue` to the pointwise bounds from `Lemma_2_21`.
theorem constrainedAuxiliaryOptimalValue_shift_bounds
    (problem : LagrangianProblem Q m) {t Δ : ℝ} (hΔ : 0 ≤ Δ) :
    problem.constrainedAuxiliaryOptimalValue t - Δ ≤
        problem.constrainedAuxiliaryOptimalValue (t + Δ) ∧
      problem.constrainedAuxiliaryOptimalValue (t + Δ) ≤
        problem.constrainedAuxiliaryOptimalValue t := by
  constructor
  · simpa [constrainedAuxiliaryOptimalValue] using
      (SetConstrainedMinimizationProblem.optimalValue_sub_le_optimalValue_of_forall_sub_le
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective t))
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective (t + Δ)))
        rfl
        (fun x _ ↦ problem.constrainedAuxiliaryObjective_sub_le_shift hΔ x))
  · simpa [constrainedAuxiliaryOptimalValue] using
      (SetConstrainedMinimizationProblem.optimalValue_le_optimalValue_of_forall_le
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective (t + Δ)))
        (SetConstrainedMinimizationProblem.unconstrained
          (problem.constrainedAuxiliaryObjective t))
        rfl
        (fun x _ ↦ problem.constrainedAuxiliaryObjective_shift_le hΔ x))

end LagrangianProblem
