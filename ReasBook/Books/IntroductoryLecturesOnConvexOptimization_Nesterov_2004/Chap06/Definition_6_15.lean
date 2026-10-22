/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Remark_6_1_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Text_6_1_4_2_Population_Interpretation

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

/- Definition 6.15 lies in the continuous-location / constrained-minimization domain.

Sampled owner declarations:
- `SetConstrainedMinimizationProblem`, the Chapter 1 owner of a feasible set together with a
  real-valued objective;
- `ContinuousLocationWeights`, the chapter owner of the positive masses `m_j`;
- `Metric.closedBall`, the canonical owner of the Euclidean constraint `‖x‖ ≤ r̄`;
- `mem_closedBall_zero_iff`, the canonical bridge from origin-centered closed-ball membership to
  a norm bound.

Best owner abstraction:
- source-facing: the weighted Euclidean location objective together with the radius-constrained
  minimization problem;
- core/canonical: `SetConstrainedMinimizationProblem` and `Metric.closedBall`;
- bridge/view: the objective expansion and the closed-ball membership rewrite
  `‖x‖ ≤ r̄`.

Primitive data:
- the number `p` of demand points and the dimension `n`;
- positive weights `m_j`, packaged as `ContinuousLocationWeights (Fin p)`;
- centers `c_j : ℝ^n`;
- a radius bound `r̄ : ℝ≥0`.

Derived API:
- the source-facing objective `x ↦ ∑ j, m_j ‖x - c_j‖`;
- the constrained minimization problem on the closed Euclidean ball;
- the feasible-set membership view `‖x‖ ≤ r̄`.
-/

section

variable {p n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The weighted Euclidean objective `f(x) = ∑_{j=1}^p m_j ‖x - c_j‖` of the continuous location
problem. -/
def continuousLocationObjective
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) :
    E → ℝ :=
  fun x ↦ ∑ j, (weights j : ℝ) * ‖x - centers j‖

-- Proof sketch: unfold `continuousLocationObjective`.
/-- Evaluating `continuousLocationObjective` recovers the weighted sum
`∑_{j=1}^p m_j ‖x - c_j‖`. -/
@[simp] theorem continuousLocationObjective_apply
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (x : E) :
    continuousLocationObjective weights centers x =
      ∑ j, (weights j : ℝ) * ‖x - centers j‖ := by
  -- Expand the source-facing objective definition at the evaluation point `x`.
  rfl

/-- Definition 6.15 [Chapter6_2.json:39]: the constrained location problem is the constrained
minimization problem with objective `f(x) = ∑_{j=1}^p m_j ‖x - c_j‖` over the Euclidean closed
ball `‖x‖ ≤ r̄`. -/
def continuousLocationProblem
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    SetConstrainedMinimizationProblem E :=
  { feasibleSet := Metric.closedBall (0 : E) (rBar : ℝ)
    objective := continuousLocationObjective weights centers }

/-- The feasible set of `continuousLocationProblem` is the closed Euclidean ball of radius `r̄`
centered at the origin. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_feasibleSet
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    (continuousLocationProblem weights centers rBar).feasibleSet =
      Metric.closedBall (0 : E) (rBar : ℝ) := by
  -- Read off the feasible-set field from the packaged constrained problem.
  rfl

/-- The objective field of `continuousLocationProblem` is the weighted sum-of-distances objective
`continuousLocationObjective`. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_objective
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    (continuousLocationProblem weights centers rBar).objective =
      continuousLocationObjective weights centers := by
  -- Read off the objective field from the packaged constrained problem.
  rfl

/-- Unfolding `continuousLocationProblem` recovers the closed Euclidean ball together with the
continuous-location objective. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_def
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    continuousLocationProblem weights centers rBar =
      { feasibleSet := Metric.closedBall (0 : E) (rBar : ℝ)
        objective := continuousLocationObjective weights centers } := by
  -- Unfold the owner definition to recover the textbook feasible set and objective.
  rfl

/-- Coercing `continuousLocationProblem` to a function recovers the weighted sum-of-distances
objective `continuousLocationObjective`. -/
-- Proof sketch: unfold `continuousLocationProblem`.
@[simp] theorem continuousLocationProblem_coe
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) :
    ⇑(continuousLocationProblem weights centers rBar) =
      continuousLocationObjective weights centers := by
  -- Coercing the owner to a function exposes its objective field.
  rfl

/-- Evaluating `continuousLocationProblem` at a point `x` recovers the source-facing continuous-
location objective `continuousLocationObjective weights centers x`. -/
-- Proof sketch: apply `continuousLocationProblem_objective`.
@[simp] theorem continuousLocationProblem_spec
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E)
    (rBar : NNReal) (x : E) :
    continuousLocationProblem weights centers rBar x =
      continuousLocationObjective weights centers x := by
  -- Evaluate the constrained problem through the objective-field coercion.
  rfl

/-- Evaluating `continuousLocationProblem` recovers the formula
`∑_{j=1}^p m_j ‖x - c_j‖`. -/
-- Proof sketch: combine `continuousLocationProblem_objective` with
-- `continuousLocationObjective_apply`.
@[simp] theorem continuousLocationProblem_apply
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E) (rBar : NNReal) (x : E) :
    continuousLocationProblem weights centers rBar x =
      ∑ j, (weights j : ℝ) * ‖x - centers j‖ := by
  -- Reduce evaluation of the packaged problem to the explicit objective formula.
  rw [continuousLocationProblem_spec, continuousLocationObjective_apply]

/-- A point is feasible for `continuousLocationProblem` exactly when its Euclidean norm is at most
`r̄`. -/
-- Proof sketch: rewrite the feasible set using `continuousLocationProblem_feasibleSet`, then
-- apply `mem_closedBall_zero_iff`.
@[simp] theorem continuousLocationProblem_mem_feasibleSet_iff
    (weights : ContinuousLocationWeights (Fin p)) (centers : Fin p → E)
    (rBar : NNReal) (x : E) :
    x ∈ (continuousLocationProblem weights centers rBar).feasibleSet ↔ ‖x‖ ≤ (rBar : ℝ) := by
  -- Rewrite feasibility to origin-centered closed-ball membership and apply the norm criterion.
  rw [continuousLocationProblem_feasibleSet]
  exact mem_closedBall_zero_iff

end

end
