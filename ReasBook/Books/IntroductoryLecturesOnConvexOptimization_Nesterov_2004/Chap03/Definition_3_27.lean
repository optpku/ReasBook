/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_30

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

/- Definition 3.27 lies in the convex optimization domain with linear equality constraints.

Sampled owner-style declarations:
* `PrimalEqualityConstrainedProblem` in `Chap02/Definition_2_30`, the earlier project owner of an
  ambient feasible set, a real-valued objective, and the linear equality data `A x = b`;
* `PrimalEqualityConstrainedProblem.equalityFeasibleSet` in `Chap02/Definition_2_30`, the owner
  projection to the intrinsic feasible region cut out by `x ∈ Q` and `A x = b`;
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the ambient feasible-set /
  objective owner extended by `PrimalEqualityConstrainedProblem`;
* `Matrix.toEuclideanLin`, the mathlib bridge from the textbook matrix presentation to the
  intrinsic linear-map owner.

Best owner abstraction:
* source-facing: `LinearEqualityConstrainedConvexProblem E Λ`;
* core/canonical: `PrimalEqualityConstrainedProblem E Λ`;
* bridge/view: the equality-feasible-set projection
  `PrimalEqualityConstrainedProblem.equalityFeasibleSet`, together with the Euclidean matrix
  realization obtained by specializing `E`, `Λ`, and `A` to `EuclideanSpace` and
  `Matrix.toEuclideanLin`.

Primitive data:
* the ambient feasible set `Q`, objective `f : E → ℝ`, linear map `A`, and right-hand side `b`,
  owned canonically by `PrimalEqualityConstrainedProblem E Λ`;
* closedness of `Q` and convexity of `f` on `Q`.

Derived API:
* convexity of `Q`, recovered canonically from `objective_convex`;
* the intrinsic equality-feasible region `problem.equalityFeasibleSet`, inherited from the
  Chapter 2 owner;
* any later full-row-rank / surjectivity hypotheses on `A`, which belong on downstream theorems
  rather than in the owner data.

This file therefore keeps the convex problem itself source-facing, but the equality-constraint
layer is owned by `PrimalEqualityConstrainedProblem` instead of being restated locally. The
textbook matrix presentation is a specialization via `Matrix.toEuclideanLin`, not the main owner.
Its primitive data only use the topological/module layer on `E`, so the public owner does not
freeze normed structure into Definition 3.27 itself.
-/

/-- Definition 3.27: a convex optimization problem with linear equality constraints consists of an
ambient closed convex set `Q`, a convex objective `f` on `Q`, a linear map `A`, and a right-hand
side `b`, encoding the program `min_{x ∈ Q} {f x : A x = b}`. In the textbook Euclidean
realization, `A` is represented by a matrix; full row rank is an additional theorem-level
assumption on that matrix presentation, not primitive owner data. -/
structure LinearEqualityConstrainedConvexProblem
    (E : Type u) (Λ : Type v) [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
    [AddCommMonoid Λ] [Module ℝ Λ]
    extends PrimalEqualityConstrainedProblem E Λ where
  /-- The ambient set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The objective is convex on the ambient set `Q`. -/
  objective_convex : ConvexOn ℝ feasibleSet objective

namespace LinearEqualityConstrainedConvexProblem

variable {E : Type u} {Λ : Type v}
variable [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]
variable [AddCommMonoid Λ] [Module ℝ Λ]

/-- The ambient set `Q` of a linear-equality-constrained convex problem is convex. -/
theorem feasibleSet_convex (problem : LinearEqualityConstrainedConvexProblem E Λ) :
    Convex ℝ problem.feasibleSet :=
  problem.objective_convex.1

/-- A linear-equality-constrained convex problem can be used as its ambient objective function. -/
instance : CoeFun (LinearEqualityConstrainedConvexProblem E Λ) (fun _ ↦ E → ℝ) where
  coe problem := problem.toPrimalEqualityConstrainedProblem

/-- Evaluating a linear-equality-constrained convex problem returns its ambient objective value. -/
@[simp] theorem coe_apply
    (problem : LinearEqualityConstrainedConvexProblem E Λ) (x : E) :
    problem x = problem.objective x :=
  rfl

end LinearEqualityConstrainedConvexProblem
