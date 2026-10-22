/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

variable {n m : ℕ}

/-
Definition 5.0.1 lies in the convex constrained minimization domain.

Sampled owner declarations:
- `LagrangianProblem` and `LagrangianProblem.feasibleSet` in `Chap01/Definition_1_10_2`, the
  project owner for the primitive objective-and-constraint data and its derived inequality
  feasible set;
- `GeneralConvexMinimizationProblem` and `GeneralConvexMinimizationProblem.ofReal` in
  `Chap03/Definition_3_1_1_1`, the chapter owner for ambient convex inequality-constrained
  minimization and the canonical real-valued whole-space bridge;
- `SmoothFunctionalConstraintsMinimizationProblem` in `Chap02/Definition_2_44`, the local project
  pattern of extending `LagrangianProblem` and adding only the extra regularity data specific to
  the refined source-facing notion.

Best owner abstraction:
- source-facing: `ConvexInequalityConstrainedMinimizationProblem n m`, the textbook whole-space
  real-valued specialization on `ℝⁿ`;
- core/canonical: `LagrangianProblem (EuclideanSpace ℝ (Fin n)) m` for the primitive functional
  data, together with `GeneralConvexMinimizationProblem (EuclideanSpace ℝ (Fin n)) m` for the
  convex-analysis owner;
- bridge/view: the inherited parent projection `toLagrangianProblem` and the Chapter 3 bridge
  `toGeneralConvexMinimizationProblem`.

Primitive data:
- the inherited real-valued objective and constraint family from `LagrangianProblem`;
- the whole-space convexity witnesses.

Derived API:
- the coercion to the objective function;
- the inherited `LagrangianProblem` feasible-set and feasibility API;
- the explicit Chapter 3 bridge `toGeneralConvexMinimizationProblem`.
-/

/-- Definition 5.0.1: a convex minimization problem with inequality constraints on `ℝⁿ`
consists of a real-valued objective function `f₀` and constraint functions `fⱼ`, `j = 1, …, m`,
all convex on the whole space, representing the problem of minimizing `f₀(x)` subject to the
inequalities `fⱼ(x) ≤ 0`. -/
structure ConvexInequalityConstrainedMinimizationProblem (n m : ℕ)
    extends LagrangianProblem (EuclideanSpace ℝ (Fin n)) m where
  /-- The objective is convex on all of `ℝⁿ`. -/
  objective_convex : ConvexOn ℝ Set.univ objective
  /-- Each constraint function is convex on all of `ℝⁿ`. -/
  constraints_convex (j : Fin m) : ConvexOn ℝ Set.univ (constraints j)

/-- A convex minimization problem with inequality constraints can be used as its objective
function. -/
instance :
    CoeFun (ConvexInequalityConstrainedMinimizationProblem n m)
      (fun _ ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe problem := problem.objective

namespace ConvexInequalityConstrainedMinimizationProblem

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The Chapter 3 owner view of a whole-space real-valued convex inequality problem. -/
def toGeneralConvexMinimizationProblem
    (problem : ConvexInequalityConstrainedMinimizationProblem n m) :
    GeneralConvexMinimizationProblem E m :=
  GeneralConvexMinimizationProblem.ofReal
    (SetConstrainedMinimizationProblem.unconstrained problem)
    problem.constraints isClosed_univ convex_univ
    problem.objective_convex problem.constraints_convex

@[simp] theorem toGeneralConvexMinimizationProblem_apply
    (problem : ConvexInequalityConstrainedMinimizationProblem n m) (x : E) :
    problem.toGeneralConvexMinimizationProblem x = problem x :=
  rfl

@[simp] theorem toGeneralConvexMinimizationProblem_feasibleSet
    (problem : ConvexInequalityConstrainedMinimizationProblem n m) :
    problem.toGeneralConvexMinimizationProblem.feasibleSet = Set.univ :=
  rfl

end ConvexInequalityConstrainedMinimizationProblem

end
