/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-
Definition 3.1 is a source-facing recall in the convex constrained minimization domain.

Primary domain:
- finite-dimensional convex minimization with an extended-real-valued objective and finitely many
  extended-real-valued inequality constraints.

Sampled owner-style declarations:
- `GeneralMinimizationProblem` in `Chap01/Definition_1_1_3`, the earlier project owner for a
  basic feasible set together with finitely many scalar constraints and comparison senses.
- `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the zero-constraint owner for
  an ambient feasible set and a real-valued objective.
- `GeneralConvexMinimizationProblem` in `Definition_3_1_1_1`, the chapter owner matching the
  exact extended-valued convex data of Definition 3.1.
- `GeneralConvexMinimizationProblem.IsFeasible`, the derived feasibility predicate attached to
  that owner.

Best owner abstraction:
- `GeneralConvexMinimizationProblem X m`, with textbook specialization
  `X = EuclideanSpace ℝ (Fin n)`

Primitive data:
- `feasibleSet : Set X`
- `objective : X → WithTop ℝ`
- `constraints : Fin m → X → WithTop ℝ`
- `feasibleSet_closed`
- `feasibleSet_convex`
- `objective_convex`
- `constraints_convex`

Derived API:
- the coercion to the ambient objective function
- `GeneralConvexMinimizationProblem.IsFeasible`

Source/core/bridge triage:
- source-facing: the textbook general convex minimization problem with convex inequality
  constraints `fᵢ(x) ≤ 0`.
- core/canonical: `GeneralConvexMinimizationProblem X m`.
- bridge/view: the textbook Euclidean specialization
  `X = EuclideanSpace ℝ (Fin n)`, together with the coercion to the ambient objective and the
  feasibility predicate `GeneralConvexMinimizationProblem.IsFeasible`.

This file therefore recalls the canonical owner abstraction directly and keeps no parallel public
wrapper such as `ConvexOptimizationProblem` or a separate feasibility package.
-/

recall GeneralConvexMinimizationProblem
    {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] (m : ℕ) :
    Type u

recall GeneralConvexMinimizationProblem.IsFeasible
    {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X] {m : ℕ}
    (problem : GeneralConvexMinimizationProblem X m) (x : X) :
    Prop
