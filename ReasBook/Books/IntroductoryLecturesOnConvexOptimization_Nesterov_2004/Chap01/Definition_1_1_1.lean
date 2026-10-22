/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- The primary domain here is constrained optimization with finitely many scalar constraint
functions on a basic feasible set.

Sampled owner-style declarations in this domain:
* `FunctionalConstraintsMinimizationProblem` and `GeneralMinimizationProblem` in
  `Chap01/Definition_1_1_3`, the project owner and its textbook Euclidean specialization;
* `LagrangianProblem.constraintVector` and `LagrangianProblem.mem_feasibleSet_iff` in
  `Chap01/Definition_1_10_2`, which reuse the same owner-level constraint packaging;
* `PrimalEqualityConstrainedProblem.mem_feasibleSet_iff` in `Chap02/Definition_2_30`, which
  specializes the same feasible-set interface to equality constraints.

Best owner abstraction:
* `FunctionalConstraintsMinimizationProblem X m`

Primitive data:
* `basicFeasibleSet`
* `objective`
* `constraints`
* `senses`

Derived API:
* the objective coercion
* the packaged constraint map `constraintVector`
* the inequality-only predicate `HasLeConstraints`
* the feasible-set rewrite `mem_feasibleSet_iff`

Source/core/bridge triage:
* source-facing: the textbook `GeneralMinimizationProblem n m` specialization
* core/canonical: `FunctionalConstraintsMinimizationProblem X m`
* bridge/view: `GeneralMinimizationProblem n m` as the Euclidean specialization

This file therefore keeps the main labeled entry as a direct recall of the existing textbook
specialization and puts the reusable companion API on the ambient owner. -/

section

variable {n m : ℕ}

/- Definition 1.1.1: the textbook general minimization problem on `ℝⁿ` is represented by
`GeneralMinimizationProblem n m`, the Euclidean specialization of the ambient owner
`FunctionalConstraintsMinimizationProblem`. The companion owner-level declarations below record
the objective-function coercion, the packaged constraint vector, and the inequality-only feasible
set from the textbook terminology. -/
#check (GeneralMinimizationProblem n m)

end

/-- A functional-constraint minimization problem coerces to its objective function on the basic
feasible set. -/
instance {X : Type u} {m : ℕ} :
    CoeFun (FunctionalConstraintsMinimizationProblem X m)
      (fun problem ↦ problem.basicFeasibleSet → ℝ) where
  coe problem := problem.objective

namespace FunctionalConstraintsMinimizationProblem

variable {X : Type u} {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

-- Proof sketch: unfold the `CoeFun` instance for
-- `FunctionalConstraintsMinimizationProblem` and evaluate it at `x`.
/-- Evaluating a functional-constraint minimization problem at a feasible point returns its
objective value. -/
@[simp] theorem coe_apply (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) : problem x = problem.objective x :=
  rfl

/-- The vector of functional constraints associated to a minimization problem. -/
def constraintVector (problem : FunctionalConstraintsMinimizationProblem X m) :
    problem.basicFeasibleSet → Λ :=
  fun x ↦ WithLp.toLp 2 fun i ↦ problem.constraints i x

-- Proof sketch: unfold `constraintVector` and evaluate the corresponding coordinate.
/-- The coordinates of the functional-constraint vector are the scalar constraint values. -/
@[simp] theorem constraintVector_apply (problem : FunctionalConstraintsMinimizationProblem X m)
    (x : problem.basicFeasibleSet) (i : Fin m) :
    problem.constraintVector x i = problem.constraints i x :=
  rfl

/-- A minimization problem has only inequality constraints when every comparison sign is `≤`. -/
def HasLeConstraints (problem : FunctionalConstraintsMinimizationProblem X m) : Prop :=
  ∀ i, problem.senses i = .le

-- Proof sketch: unfold `feasibleSet` and `IsFeasible`, then rewrite each constraint sense using
-- the hypothesis that every comparison sign is `ConstraintSense.le`.
/-- Under inequality-only constraints, feasibility is equivalent to satisfying `fⱼ(x) ≤ 0` for
each scalar constraint. -/
@[simp] theorem mem_feasibleSet_iff (problem : FunctionalConstraintsMinimizationProblem X m)
    (h : problem.HasLeConstraints) {x : problem.basicFeasibleSet} :
    x ∈ problem.feasibleSet ↔ ∀ i : Fin m, problem.constraints i x ≤ 0 := by
  constructor
  · intro hx i
    simpa [FunctionalConstraintsMinimizationProblem.feasibleSet,
      FunctionalConstraintsMinimizationProblem.IsFeasible, ConstraintSense.Holds, h i] using hx i
  · intro hx i
    simpa [FunctionalConstraintsMinimizationProblem.feasibleSet,
      FunctionalConstraintsMinimizationProblem.IsFeasible, ConstraintSense.Holds, h i] using hx i

end FunctionalConstraintsMinimizationProblem
