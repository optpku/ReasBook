/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_7

-- Declarations for this item will be appended below by the statement pipeline.

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

/-
Definition 1.1.4.8 lies in the quadratic constrained-optimization domain.

Sampled owner-side declarations in this domain:
* `Set.QuadraticOn`
* `FunctionalConstraintsMinimizationProblem
  .constraintVector_quadraticOn_iff_forall_constraint_quadraticOn`
* `FunctionalConstraintsMinimizationProblem.constraint_isQuadratic`
* `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`
* `Set.QuadraticOn` for quadratic data on `problem.basicFeasibleSet`

Source/core/bridge triage:
* `source-facing`:
  `FunctionalConstraintsMinimizationProblem.IsQuadraticallyConstrainedQuadraticProblem`
* `core/canonical`: `Set.QuadraticOn` on the owner objective and packaged constraint vector
* `bridge/view`: the scalar-constraint expansion and the earlier owner
  `FunctionalConstraintsMinimizationProblem.IsQuadraticOptimizationProblem`

Primitive data:
* quadratic objective data
* quadratic packaged constraint-vector data

Derived API:
* scalar quadratic constraints derived from the packaged owner constraint vector
* the bridge from linearly constrained quadratic optimization to the present owner
-/

/-- Definition 1.1.4.8: a quadratically constrained quadratic problem is a minimization problem
whose objective function and packaged constraint vector, equivalently every scalar constraint, are
quadratic on the basic feasible set. -/
def IsQuadraticallyConstrainedQuadraticProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective ∧
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector

/-- A quadratic optimization problem is, in particular, quadratically constrained quadratic. -/
theorem IsQuadraticOptimizationProblem.isQuadraticallyConstrainedQuadraticProblem
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsQuadraticOptimizationProblem) :
    problem.IsQuadraticallyConstrainedQuadraticProblem := by
  refine ⟨h.objective_isQuadratic, ⟨0, ?_⟩⟩
  simpa using h.isLinearlyConstrained.constraintVector_isAffine

variable {problem : FunctionalConstraintsMinimizationProblem X m}

/-- Unfolding the owner-style definition recovers the scalar-constraint formulation. -/
theorem isQuadraticallyConstrainedQuadraticProblem_iff :
    problem.IsQuadraticallyConstrainedQuadraticProblem ↔
      Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective ∧
        ∀ j : Fin m, Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) := by
  rw [IsQuadraticallyConstrainedQuadraticProblem,
    problem.constraintVector_quadraticOn_iff_forall_constraint_quadraticOn]

/-- A quadratically constrained quadratic problem has a quadratic objective function. -/
theorem IsQuadraticallyConstrainedQuadraticProblem.objective_isQuadratic
    (h : problem.IsQuadraticallyConstrainedQuadraticProblem) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.objective :=
  h.1

/-- A quadratically constrained quadratic problem has a quadratic packaged constraint vector. -/
theorem IsQuadraticallyConstrainedQuadraticProblem.constraintVector_isQuadratic
    (h : problem.IsQuadraticallyConstrainedQuadraticProblem) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ problem.constraintVector :=
  h.2

/-- Every scalar constraint of a quadratically constrained quadratic problem is quadratic. -/
theorem IsQuadraticallyConstrainedQuadraticProblem.constraint_isQuadratic
    (h : problem.IsQuadraticallyConstrainedQuadraticProblem) (j : Fin m) :
    Set.QuadraticOn problem.basicFeasibleSet ℝ (problem.constraints j) :=
  problem.constraint_isQuadratic h.2 j

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.8 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsQuadraticallyConstrainedQuadraticProblem`. -/
#check problem.IsQuadraticallyConstrainedQuadraticProblem

end GeneralMinimizationProblem
