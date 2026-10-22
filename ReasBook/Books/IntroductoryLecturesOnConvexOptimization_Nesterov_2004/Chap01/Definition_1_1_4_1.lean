/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type*} {m : ℕ}

/- Definition 1.1.4.1 lies in the feasible-set domain of constrained optimization.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem X m` and `problem.feasibleSet` in
  `Chap01/Definition_1_1_3`
* `FunctionalConstraintsMinimizationProblem.StrictlyFeasible` in `Chap01/Definition_1_1_2`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained` in
  `Chap01/Definition_1_1_4_5`
* `Set.ssubset_univ_iff` and `Set.ne_univ_iff_exists_notMem`

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `problem.basicFeasibleSet`
* `problem.constraints`
* `problem.senses`

Derived API:
* `problem.feasibleSet`
* `problem.IsConstrained`
* the whole-space and nonmembership reformulations below

Source/core/bridge triage:
* source-facing: `problem.IsConstrained`
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the textbook Euclidean specialization

Constrainedness depends only on whether the feasible set fills the ambient type, so the owner lives
on `FunctionalConstraintsMinimizationProblem X m`; the `ℝⁿ` formulation is only its specialization.
-/

/-- Definition 1.1.4.1: a minimization problem is constrained when its feasible set is a proper
subset of the ambient space. -/
def IsConstrained (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  (problem.feasibleSet : Set X) ⊂ Set.univ

/-- A minimization problem is constrained exactly when its feasible set does not fill the ambient
space. -/
theorem isConstrained_iff_feasibleSet_ne_univ
    {problem : FunctionalConstraintsMinimizationProblem X m} :
    problem.IsConstrained ↔ (problem.feasibleSet : Set X) ≠ Set.univ := by
  rw [IsConstrained, Set.ssubset_univ_iff]

/-- A minimization problem is unconstrained exactly when its feasible set fills the ambient
space. -/
theorem not_isConstrained_iff_feasibleSet_eq_univ
    {problem : FunctionalConstraintsMinimizationProblem X m} :
    ¬ problem.IsConstrained ↔ (problem.feasibleSet : Set X) = Set.univ := by
  rw [isConstrained_iff_feasibleSet_ne_univ]
  constructor <;> simp

/-- A constrained problem is equivalently one for which some ambient point lies outside the
feasible set. -/
theorem isConstrained_iff_exists_not_mem_feasibleSet
    {problem : FunctionalConstraintsMinimizationProblem X m} :
    problem.IsConstrained ↔ ∃ x : X, x ∉ (problem.feasibleSet : Set X) := by
  rw [isConstrained_iff_feasibleSet_ne_univ]
  simpa using Set.ne_univ_iff_exists_notMem (problem.feasibleSet : Set X)

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ}

variable (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.1 in the textbook Euclidean ambient space is the specialization of the owner
predicate `FunctionalConstraintsMinimizationProblem.IsConstrained`. -/
#check problem.IsConstrained

end GeneralMinimizationProblem
