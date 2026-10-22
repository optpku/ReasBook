/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_2_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_4_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Definition 4.4.16 lies in the unconstrained modified-Newton problem domain.

Primary domain:
* unconstrained strongly convex objectives with globally Lipschitz second derivative on real
  normed spaces

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem.unconstrained`, the chapter owner for a whole-space
  objective viewed as a canonical minimization problem
* `StrongConvexOn Set.univ σ f`, the chapter/mathlib owner for whole-space strong convexity
* `HasLipschitzContinuousHessian L f`, written on theorem surfaces as `f ∈ C22[L]`, the chapter
  owner for global `C²` second-derivative Lipschitz regularity, with the Hilbert Hessian surface
  recovered only in downstream files
* `StrongConvexOn.eq_of_isMinOn` in `Chap03/Corollary_3_2_3`, the chapter owner for uniqueness of
  a minimizer of a positive strongly convex objective
* `modifiedNewtonCharacteristicQuantity` in `Proposition_4_4_10`, the chapter owner for the
  scalar quantity `L ‖x₀ - x*‖ / σ`

Best owner abstraction:
* source-facing: the bundled modified Gauss--Newton problem data in this file
* core/canonical: `SetConstrainedMinimizationProblem.unconstrained problem.objective`,
  `StrongConvexOn Set.univ σ problem.objective`, and `problem.objective ∈ C22[L]`
* bridge/view: `problem.toSetConstrainedMinimizationProblem` and `problem.characteristicQuantity`

Primitive data:
* the objective `f`, strong-convexity modulus `σ`, Hessian-Lipschitz constant `L`, minimizer
  `xStar`, and initial point `x0`
* positive strong convexity, the whole-space strong-convexity owner, the whole-space
  second-derivative Lipschitz owner, and the chosen global minimizer

Derived API:
* the canonical whole-space minimization owner `problem.toSetConstrainedMinimizationProblem`
* coercion to the underlying objective via that owner
* `ContDiff ℝ 2 problem.objective`, supplied directly by `problem.objective_mem.contDiff`
* uniqueness of the chosen minimizer, supplied by `StrongConvexOn.eq_of_isMinOn`
* `initialDistance`
* `characteristicQuantity`, defined by direct reuse of the canonical modified-Newton owner
-/

/- Definition 4.4.16: a modified Gauss--Newton problem consists of a whole-space objective `f`
on a real normed space, a positive strong-convexity modulus `σ`, a global second-derivative
Lipschitz constant `L`, the canonical owner hypotheses `StrongConvexOn Set.univ σ f` and
`f ∈ C22[L]`, a chosen global minimizer `xStar`, and an initial point `x0`. The ambient
whole-space minimization problem is recovered by the bridge
`problem.toSetConstrainedMinimizationProblem`, while convexity, `C²` regularity, and uniqueness
of the minimizer are derived from the owner fields rather than stored as extra primitive data. -/
structure ModifiedGaussNewtonProblem where
  objective : E → ℝ
  σ : ℝ
  L : NNReal
  xStar : E
  x0 : E
  sigma_pos : 0 < σ
  objective_strongConvex : StrongConvexOn Set.univ σ objective
  objective_mem : objective ∈ C22[L]
  xStar_isMin : IsMinOn objective Set.univ xStar

namespace ModifiedGaussNewtonProblem

variable {E}

/-- Forgetting the extra strong-convexity and regularity data gives the canonical whole-space
minimization problem with objective `problem.objective`. -/
abbrev toSetConstrainedMinimizationProblem
    (problem : ModifiedGaussNewtonProblem E) : SetConstrainedMinimizationProblem E :=
  .unconstrained problem.objective

/-- The feasible set of the canonical whole-space bridge is all of `E`. -/
@[simp] theorem toSetConstrainedMinimizationProblem_feasibleSet
    (problem : ModifiedGaussNewtonProblem E) :
    problem.toSetConstrainedMinimizationProblem.feasibleSet = Set.univ :=
  rfl

/-- Evaluating the canonical whole-space bridge recovers the underlying objective. -/
@[simp] theorem toSetConstrainedMinimizationProblem_apply
    (problem : ModifiedGaussNewtonProblem E) (x : E) :
    problem.toSetConstrainedMinimizationProblem x = problem.objective x :=
  rfl

/-- A modified Gauss--Newton problem can be evaluated as its underlying objective function. -/
instance : CoeFun (ModifiedGaussNewtonProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- The objective of a modified Gauss--Newton problem is `C²`. -/
theorem contDiff (problem : ModifiedGaussNewtonProblem E) :
    ContDiff ℝ 2 problem.objective :=
  problem.objective_mem.contDiff

/-- The chosen minimizer of a modified Gauss--Newton problem is the unique global minimizer. -/
theorem eq_xStar_of_isMinOn
    (problem : ModifiedGaussNewtonProblem E) {y : E} (hy : IsMinOn problem Set.univ y) :
    y = problem.xStar :=
  problem.objective_strongConvex.eq_of_isMinOn
    problem.sigma_pos (by simp) hy (by simp) problem.xStar_isMin

/-- The initial distance `D = ‖x₀ - x*‖` attached to a modified Gauss--Newton problem. -/
def initialDistance (problem : ModifiedGaussNewtonProblem E) : ℝ :=
  ‖problem.x0 - problem.xStar‖

/-- The characteristic quantity `ξ = L D / σ` attached to a modified Gauss--Newton problem. -/
abbrev characteristicQuantity (problem : ModifiedGaussNewtonProblem E) : ℝ :=
  modifiedNewtonCharacteristicQuantity problem.σ problem.L problem.x0 problem.xStar

/-- Expanding `initialDistance` gives the textbook definition `D = ‖x₀ - x*‖`. -/
@[simp] theorem initialDistance_def (problem : ModifiedGaussNewtonProblem E) :
    problem.initialDistance = ‖problem.x0 - problem.xStar‖ :=
  rfl

/-- Expanding `characteristicQuantity` gives the textbook definition `ξ = L D / σ`. -/
@[simp] theorem characteristicQuantity_def (problem : ModifiedGaussNewtonProblem E) :
    problem.characteristicQuantity = (problem.L : ℝ) * problem.initialDistance / problem.σ :=
  rfl

end ModifiedGaussNewtonProblem
