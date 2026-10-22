/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} [TopologicalSpace X] {m : ℕ}

/- Definition 1.10.21 lies in the topological constrained-optimization domain.

Sampled owner-style declarations:
* `FunctionalConstraintsMinimizationProblem X m`, `problem.HasLeConstraints`, and
  `problem.mem_feasibleSet_iff` in `Chap01/Definition_1_1_1`
* `FunctionalConstraintsMinimizationProblem.IsLinearlyConstrained` and
  `problem.constraintVector_affineOn_iff_forall_constraint_affineOn` in
  `Chap01/Definition_1_1_4_5`
* `Continuous` and `IsClosed` from mathlib's topological API

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `problem.basicFeasibleSet`
* `problem.objective`
* `problem.constraints`
* `problem.senses`

Derived API:
* closedness of `problem.basicFeasibleSet`
* continuity of `problem.objective`
* continuity of the packaged map `problem.constraintVector`
* continuity of each scalar constraint
* the inequality-only condition `problem.HasLeConstraints`

Source/core/bridge triage:
* source-facing: the textbook `GeneralMinimizationProblem n m` specialization
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization

These hypotheses depend only on the topology of the feasible subtype and the finite real-valued
constraint family, so they belong to the ambient owner `FunctionalConstraintsMinimizationProblem`
rather than to the Euclidean specialization. -/

/- The packaged owner constraint map is continuous exactly when each scalar constraint function is
continuous. This is the canonical owner-level bridge from the coordinate family to the vector
constraint map. -/
theorem constraintVector_continuous_iff (problem : FunctionalConstraintsMinimizationProblem X m) :
    Continuous problem.constraintVector ↔ ∀ j : Fin m, Continuous (problem.constraints j) := by
  constructor
  · intro h j
    have hj : Continuous (fun x : EuclideanSpace ℝ (Fin m) ↦ x j) :=
      PiLp.continuous_apply (2 : ENNReal) (fun _ : Fin m ↦ ℝ) j
    simpa using hj.comp h
  · intro h
    simpa [FunctionalConstraintsMinimizationProblem.constraintVector] using
      (PiLp.continuous_toLp (2 : ENNReal) (fun _ : Fin m ↦ ℝ)).comp (continuous_pi h)

/-- Definition 1.10.21: a nonlinear optimization problem with functional constraints is a
functional-constraint minimization problem whose basic feasible set is closed, whose objective and
constraint functions are continuous on that feasible subtype, and whose scalar constraints are all
of the form `fⱼ(x) ≤ 0`. The textbook `GeneralMinimizationProblem n m` case is the Euclidean
specialization of this owner. The primitive continuity data are the scalar constraints; continuity
of the packaged owner map `problem.constraintVector` is derived. -/
class IsFunctionalConstraintProblem
    (problem : FunctionalConstraintsMinimizationProblem X m) : Prop where
  basicFeasibleSet_isClosed : IsClosed problem.basicFeasibleSet
  objective_continuous : Continuous problem.objective
  constraint_continuous (j : Fin m) : Continuous (problem.constraints j)
  hasLeConstraints : problem.HasLeConstraints

variable {problem : FunctionalConstraintsMinimizationProblem X m}

/-- A functional-constraint problem has a continuous packaged owner constraint map. -/
theorem IsFunctionalConstraintProblem.constraintVector_continuous
    (h : problem.IsFunctionalConstraintProblem) :
    Continuous problem.constraintVector :=
  problem.constraintVector_continuous_iff.2 h.constraint_continuous

instance [h : problem.IsFunctionalConstraintProblem] :
    IsClosed problem.basicFeasibleSet :=
  h.basicFeasibleSet_isClosed

instance [h : problem.IsFunctionalConstraintProblem] :
    Continuous problem.objective :=
  h.objective_continuous

instance [h : problem.IsFunctionalConstraintProblem] :
    Continuous problem.constraintVector :=
  h.constraintVector_continuous

instance [h : problem.IsFunctionalConstraintProblem] (j : Fin m) :
    Continuous (problem.constraints j) :=
  h.constraint_continuous j

instance [h : problem.IsFunctionalConstraintProblem] :
    problem.HasLeConstraints :=
  h.hasLeConstraints

end FunctionalConstraintsMinimizationProblem

namespace GeneralMinimizationProblem

variable {n m : ℕ} (problem : GeneralMinimizationProblem n m)

/- Definition 1.10.21 in the textbook Euclidean ambient space uses the same Chapter 1 owner
predicate, specialized from `FunctionalConstraintsMinimizationProblem X m` to
`GeneralMinimizationProblem n m`. -/
#check problem.IsFunctionalConstraintProblem

end GeneralMinimizationProblem
