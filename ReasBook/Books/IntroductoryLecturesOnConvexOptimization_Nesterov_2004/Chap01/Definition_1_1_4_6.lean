/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} [AddCommGroup X] [Module ℝ X] {m : ℕ}

/-
Definition 1.1.4.6 lies in the affine/linearly constrained optimization domain.

Sampled owner-side declarations in this domain:
* `Set.AffineOn`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained.constraint_isAffine`
* `FunctionalConstraintsMinimizationProblem.isLinearlyConstrained_iff`

Owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`
* `Set.AffineOn` for affine objective data on the basic feasible set
* `problem.IsLinearlyConstrained` for the constraint side

Source/core/bridge triage:
* `source-facing`: the textbook `GeneralMinimizationProblem n m` specialization
* `core/canonical`: `FunctionalConstraintsMinimizationProblem.IsLinearOptimizationProblem`
* `bridge/view`: `GeneralMinimizationProblem n m` as the Euclidean specialization

Primitive data for the core owner notion:
* affine objective data on `problem.basicFeasibleSet`
* linearly constrained constraint data

Derived API:
* the textbook expansion through `problem.isLinearOptimizationProblem_iff`
* the owner-side consequences
  `IsLinearOptimizationProblem.objective_isAffine` and
  `IsLinearOptimizationProblem.isLinearlyConstrained`

Nothing in the definition uses coordinates on `ℝⁿ`; the Euclidean ambient space is only the
textbook specialization of this owner-level notion.
-/

/-- Definition 1.1.4.6: a linear optimization problem is a minimization problem whose objective
function is affine and which is linearly constrained in the sense of
Definition 1.1.4.5. -/
def IsLinearOptimizationProblem (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  Set.AffineOn problem.basicFeasibleSet ℝ problem.objective ∧ problem.IsLinearlyConstrained

/-- Expanding the owner formulation gives the textbook condition that the objective and every
functional constraint are affine and the basic feasible set is polyhedral. -/
theorem isLinearOptimizationProblem_iff
    (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.IsLinearOptimizationProblem ↔
      Set.AffineOn problem.basicFeasibleSet ℝ problem.objective ∧
        (∀ j : Fin m, Set.AffineOn problem.basicFeasibleSet ℝ (problem.constraints j)) ∧
        problem.basicFeasibleSet.IsPolyhedron := by
  rw [IsLinearOptimizationProblem, problem.isLinearlyConstrained_iff]

/-- A linear optimization problem has an affine objective function. -/
theorem IsLinearOptimizationProblem.objective_isAffine
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearOptimizationProblem) :
    Set.AffineOn problem.basicFeasibleSet ℝ problem.objective :=
  h.1

/-- A linear optimization problem is, in particular, linearly constrained. -/
theorem IsLinearOptimizationProblem.isLinearlyConstrained
    {problem : FunctionalConstraintsMinimizationProblem X m}
    (h : problem.IsLinearOptimizationProblem) :
    problem.IsLinearlyConstrained :=
  h.2

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.6 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsLinearOptimizationProblem`. -/
#check problem.IsLinearOptimizationProblem

end GeneralMinimizationProblem
