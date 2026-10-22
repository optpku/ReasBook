/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-
Definition 6.4 lies in the constrained convex minimization domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the project owner of a
  feasible set together with a real-valued objective;
* `SetConstrainedMinimizationProblem.optimalValue` in `Chap01/Definition_1_3_7`, the canonical
  optimal-value owner for that ambient problem data;
* `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, which extends the same
  owner and keeps only genuinely extra convex-program data as primitive fields;
* `Metric.isCompact_of_isClosed_isBounded`, together with `FiniteDimensional.proper_real`, the
  canonical bounded-to-compact bridge used only when the ambient space is finite-dimensional.

Best owner abstraction:
* source-facing: `PrimalConvexMinimizationProblem E`;
* core/canonical: `SetConstrainedMinimizationProblem E` and its owner `optimalValue`;
* bridge/view: the finite-dimensional compactness theorem for the feasible set.

Primitive data:
* the feasible set and objective, owned by `SetConstrainedMinimizationProblem E`;
* nonemptiness, boundedness, and closedness of the feasible set;
* continuity and convexity of the objective on the feasible set.

Derived API:
* coercion to the ambient objective;
* the inherited owner optimal-value API, available directly as `problem.optimalValue`;
* convexity of the feasible set, recovered canonically from `objective_convex`;
* compactness of the feasible set under the additional finite-dimensional ambient hypothesis.
-/

/-- Definition 6.4: a primal convex minimization problem consists of a nonempty bounded closed
convex feasible set `Q₁` and a continuous convex objective function `f : E → ℝ`, considered on
`Q₁`. The textbook item specializes this data to finite-dimensional real ambient spaces. -/
structure PrimalConvexMinimizationProblem (E : Type u) [NormedAddCommGroup E]
    [NormedSpace ℝ E] extends SetConstrainedMinimizationProblem E where
  /-- The feasible set is nonempty, so the minimum-value notation is meaningful. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set is bounded. -/
  feasibleSet_bounded : Bornology.IsBounded feasibleSet
  /-- The feasible set is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The objective is continuous on the feasible set. -/
  objective_continuous : ContinuousOn objective feasibleSet
  /-- The objective is convex on the feasible set. -/
  objective_convex : ConvexOn ℝ feasibleSet objective

namespace PrimalConvexMinimizationProblem

/-- The feasible set of a primal convex minimization problem is convex. -/
theorem feasibleSet_convex (problem : PrimalConvexMinimizationProblem E) :
    Convex ℝ problem.feasibleSet :=
  problem.objective_convex.1

/-- A primal convex minimization problem can be used as its objective function. -/
instance : CoeFun (PrimalConvexMinimizationProblem E) (fun _ ↦ E → ℝ) where
  coe problem := problem.objective

/-- Evaluating a primal convex minimization problem returns its objective value. -/
@[simp] theorem coe_apply
    (problem : PrimalConvexMinimizationProblem E) (x : E) :
    problem x = problem.objective x :=
  rfl

-- Proof sketch: in finite-dimensional real normed spaces, closed and bounded sets are compact.
/-- A primal convex minimization problem has compact feasible set. -/
theorem feasibleSet_isCompact [FiniteDimensional ℝ E]
    (problem : PrimalConvexMinimizationProblem E) :
    IsCompact problem.feasibleSet := by
  letI : ProperSpace E := FiniteDimensional.proper_real E
  simpa using
    Metric.isCompact_of_isClosed_isBounded
      problem.feasibleSet_closed problem.feasibleSet_bounded

end PrimalConvexMinimizationProblem
