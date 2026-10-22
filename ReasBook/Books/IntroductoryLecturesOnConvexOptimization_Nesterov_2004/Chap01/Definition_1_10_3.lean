/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace

local notation "X" => EuclideanSpace ℝ (Fin 2)

/- Primary domain: finite-dimensional Lagrangian duality for a single inequality-constrained
example on `ℝ²`.

Sampled owner declarations before refining this file:
* `LagrangianProblem` together with its primitive fields `objective` and `constraints` in
  `Definition_1_10_2`;
* the derived owner API `LagrangianProblem.constraintVector`, `LagrangianProblem.lagrangian`,
  `LagrangianProblem.lagrangian_single_eq`, and `LagrangianProblem.feasibleSet` in
  `Definition_1_10_2`;
* the direct downstream owner usage in `Proposition_1_10_5`, which treats
  `lagrangianRelaxationExample : LagrangianProblem (EuclideanSpace ℝ (Fin 2)) 1` as the primary
  object.

Best owner abstraction:
`lagrangianRelaxationExample : LagrangianProblem X 1`.

Primitive data in this file:
* the objective function;
* the single scalar constraint.

No additional public bridge/view API is kept here: the textbook scalar-multiplier Lagrangian
formula already follows from the owner theorem `LagrangianProblem.lagrangian_single_eq` by
specializing to `lagrangianRelaxationExample` and unfolding the structure literal. The pointwise
objective and constraint formulas are likewise available directly from the owner declaration. -/

/-- Definition 1.10.3: The example constrained optimization problem on `ℝ²` has objective
`f₀(x) = (1 / 2) ‖x - (1,1)‖²` and the single inequality constraint
`f₁(x) = x₁ - (1 / 2) x₂² ≤ 0`. -/
def lagrangianRelaxationExample : LagrangianProblem X 1 where
  objective x := (1 / 2 : ℝ) * ‖x - WithLp.toLp 2 ![(1 : ℝ), 1]‖ ^ 2
  constraints _ x := x 0 - (1 / 2 : ℝ) * x 1 ^ 2

/-- Evaluating the example problem recovers its quadratic objective formula. -/
@[simp] theorem lagrangianRelaxationExample_apply (x : X) :
    lagrangianRelaxationExample x =
      (1 / 2 : ℝ) * ‖x - WithLp.toLp 2 ![(1 : ℝ), 1]‖ ^ 2 :=
  rfl

/-- The unique scalar constraint of the example is `x₁ - (1 / 2) x₂²`. -/
@[simp] theorem lagrangianRelaxationExample_constraint_apply (x : X) :
    lagrangianRelaxationExample.constraints 0 x =
      x 0 - (1 / 2 : ℝ) * x 1 ^ 2 :=
  rfl
