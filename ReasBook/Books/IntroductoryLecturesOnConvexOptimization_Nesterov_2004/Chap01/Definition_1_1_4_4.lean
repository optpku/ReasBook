/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Primary domain: differentiability of the objective/constraint family of a general minimization
problem.

Sampled owner-style declarations before refining:
* `FunctionalConstraintsMinimizationProblem.IsSmooth` in `Definition_1_1_4_3`, the ambient owner
  predicate whose Euclidean specialization gives the textbook nonsmoothness notion
* `FunctionalConstraintsMinimizationProblem.constraintVector_differentiableOn_iff` in
  `Definition_1_1_4_3`, the canonical bridge from packaged constraint-map differentiability to
  scalar constraints
* `FunctionalConstraintsMinimizationProblem.constraintVector` in `Definition_1_1_1`, the upstream
  packaged owner for the scalar constraint family
* `¬ problem.IsConstrained` together with `not_isConstrained_iff_feasibleSet_eq_univ` in
  `Definition_1_1_4_1`, the matching earlier chapter pattern for recall-only negated predicates

Layer classification:
* source-facing: the recall-only negated owner expression `¬ problem.IsSmooth`
* core/canonical: `problem.IsSmooth`
* bridge/view: the explicit objective/constraint split and the scalar-constraint reformulation

Primitive data:
* `problem.basicFeasibleSet`
* `problem.objective`
* `problem.constraintVector`

Derived API:
* `problem.IsSmooth`
* `isNonsmooth_iff` -/

variable (problem : GeneralMinimizationProblem n m)

/- Definition 1.1.4.4: a general minimization problem is nonsmooth exactly when the owner
predicate `IsSmooth` from the previous item does not hold. -/
#check ¬ problem.IsSmooth

/-- Negating the canonical smoothness predicate gives the explicit textbook split into either a
nonsmooth objective or at least one nonsmooth constraint. -/
theorem isNonsmooth_iff (problem : GeneralMinimizationProblem n m) :
    ¬ problem.IsSmooth ↔
      ¬ DifferentiableOn ℝ problem.objectiveOnAmbient problem.basicFeasibleSet ∨
        ∃ i : Fin m,
          ¬ DifferentiableOn ℝ (fun x ↦ problem.constraintVectorOnAmbient x i)
            problem.basicFeasibleSet := by
  classical
  rw [FunctionalConstraintsMinimizationProblem.IsSmooth, not_and_or,
    FunctionalConstraintsMinimizationProblem.constraintVector_differentiableOn_iff, not_forall]

end GeneralMinimizationProblem
