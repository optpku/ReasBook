/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_4_3

-- Declarations for this item will be appended below by the statement pipeline.

namespace GeneralMinimizationProblem

variable {n m : ℕ}

/- Definition 3.25 is a source-facing recall in the constrained-optimization domain of owner
predicates on `GeneralMinimizationProblem n m`.

Primary mathematical domain:
* smooth inequality-constrained minimization on a closed convex feasible set

Sampled owner-style declarations:
* `problem.IsSmooth` in `Definition_1_1_4_3`
* `problem.IsFunctionalConstraintProblem` in `Definition_1_10_21`
* `problem.HasLeConstraints` in `Definition_1_1_1`
* `problem.constraintVector_continuous_iff` in `Definition_1_10_21`

Best owner abstraction:
* `GeneralMinimizationProblem n m`, with the owner smoothness predicate `problem.IsSmooth` and
  the source-facing feasible-set hypotheses expressed directly on `problem.basicFeasibleSet`

Primitive data:
* the owner problem `problem`
* the smoothness hypothesis `problem.IsSmooth`
* the inequality-sense hypothesis `problem.HasLeConstraints`
* closedness and convexity of `problem.basicFeasibleSet`

Derived API:
* objective continuity from `problem.IsSmooth`
* scalar-constraint continuity from `problem.constraintVector_continuous_iff` together with
  `problem.IsSmooth`
* the bundled Chapter 1 bridge `problem.IsFunctionalConstraintProblem`, recovered by
  `smoothFunctionalConstraintProblem_iff`

Source/core/bridge triage:
* source-facing: Definition 3.25 as `problem.IsSmooth`, `problem.HasLeConstraints`, and
  closed-convex geometry of `problem.basicFeasibleSet`
* core/canonical: the owner problem together with its Chapter 1 smoothness predicate
  `problem.IsSmooth`
* bridge/view: the companion equivalence that repackages the source-facing hypothesis list as the
  bundled Chapter 1 predicate `problem.IsFunctionalConstraintProblem`

This file therefore keeps no parallel `IsSmoothFunctionalConstraintProblem` wrapper. Downstream
usage should use the source-facing owner expression directly, and only use the package bridge when
that bundled Chapter 1 API is specifically needed. -/

variable (problem : GeneralMinimizationProblem n m)

/- Definition 3.25: a smooth minimization problem with functional constraints is a smooth
minimization problem whose constraints are all of the form `fⱼ(x) ≤ 0` and whose basic feasible
set `Q` is closed and convex. -/
#check (
  problem.IsSmooth ∧
    problem.HasLeConstraints ∧
    IsClosed problem.basicFeasibleSet ∧
    Convex ℝ problem.basicFeasibleSet
)

section

variable {problem : GeneralMinimizationProblem n m}

/-- The source-facing hypothesis list for Definition 3.25 is equivalent to the bundled Chapter 1
functional-constraint package together with convexity of the basic feasible set. -/
theorem smoothFunctionalConstraintProblem_iff :
    (problem.IsSmooth ∧
      problem.HasLeConstraints ∧
      IsClosed problem.basicFeasibleSet ∧
      Convex ℝ problem.basicFeasibleSet) ↔
      (problem.IsSmooth ∧
        problem.IsFunctionalConstraintProblem ∧
        Convex ℝ problem.basicFeasibleSet) := by
  constructor
  · rintro ⟨hsmooth, hle, hclosed, hconvex⟩
    exact
      ⟨hsmooth,
        { basicFeasibleSet_isClosed := hclosed
          objective_continuous := hsmooth.objective_continuous
          constraint_continuous := fun j ↦
            (problem.constraintVector_continuous_iff.mp hsmooth.constraintVector_continuous) j
          hasLeConstraints := hle },
        hconvex⟩
  · rintro ⟨hsmooth, hfunctional, hconvex⟩
    exact ⟨hsmooth, hfunctional.hasLeConstraints, hfunctional.basicFeasibleSet_isClosed, hconvex⟩

end

end GeneralMinimizationProblem
