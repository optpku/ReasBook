/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped ConstrainedArgmin

/- Definition 3.36 lies in the constrained convex minimization domain.

Sampled owner-style declarations:
* `SetConstrainedMinimizationProblem` in `Chap01/Definition_1_3_3`, the Chapter 1 owner for the
  feasible-set / objective data of a minimization problem;
* `constrainedArgmin` and `mem_constrainedArgmin_iff` in `Chap01/Definition_1_3_3`, the canonical
  owner of optimal-solution membership on a feasible set;
* `subdifferentialWithin` and `mem_subdifferentialWithin_iff` in `Chap03/Theorem_3_44`, the
  real-valued feasible-subgradient surface already owned upstream in the chapter;
* `LinearEqualityConstrainedConvexProblem` in `Chap03/Definition_3_27`, the nearby chapter owner
  pattern where the ambient optimization data are inherited from an upstream owner and only the
  genuinely extra convex-program hypotheses remain primitive.

Best owner abstraction:
* source-facing: `ConvexMinimizationProblem X`;
* core/canonical: `SetConstrainedMinimizationProblem X`, `argmin[Q] f`, and the chapter's
  constrained-subdifferential owners;
* bridge/view: `objective_convexOn`.

Primitive data:
* the feasible set `Q` and the real-valued objective `f`, already owned by
  `SetConstrainedMinimizationProblem X`;
* the nonemptiness, closedness, and convexity of `Q`;
* the whole-space convexity witness `ConvexOn ℝ Set.univ f`.

Derived API:
* the coercion back to the inherited Chapter 1 owner;
* the feasible-set convexity owner `problem.objective_convexOn`.

This file therefore keeps the source-facing problem class, but its optimality and subgradient
surfaces are the upstream owners `x ∈ argmin[problem.feasibleSet] problem` and, in downstream
real-valued inner-product settings, `g ∈ ∂[problem.feasibleSet] problem(x)` rather than parallel
local aliases. -/

section

variable {X : Type u} [TopologicalSpace X] [AddCommMonoid X] [Module ℝ X]

/-- Definition 3.36: a convex minimization problem is a set-constrained minimization problem
`min_{x ∈ Q} f(x)` whose feasible set `Q` is nonempty, closed, and convex, and whose objective
`f` is convex on the whole ambient space. -/
structure ConvexMinimizationProblem (X : Type u) [TopologicalSpace X] [AddCommMonoid X]
    [Module ℝ X] extends SetConstrainedMinimizationProblem X where
  /-- The feasible set `Q` is nonempty. -/
  feasibleSet_nonempty : feasibleSet.Nonempty
  /-- The feasible set `Q` is closed. -/
  feasibleSet_closed : IsClosed feasibleSet
  /-- The feasible set `Q` is convex. -/
  feasibleSet_convex : Convex ℝ feasibleSet
  /-- The objective `f` is convex on the whole ambient space. -/
  objective_convex : ConvexOn ℝ Set.univ objective

namespace ConvexMinimizationProblem

/-- A convex minimization problem can be used as its objective function. -/
instance : CoeFun (ConvexMinimizationProblem X) (fun _ ↦ X → ℝ) where
  coe problem := problem.toSetConstrainedMinimizationProblem

/-- Evaluating a convex minimization problem returns its objective value. -/
@[simp] theorem coe_apply (problem : ConvexMinimizationProblem X) (x : X) :
    problem x = problem.objective x :=
  rfl

/-- Restricting the whole-space convex objective to the feasible set yields the canonical
`ConvexOn` owner on that feasible set. -/
theorem objective_convexOn (problem : ConvexMinimizationProblem X) :
    ConvexOn ℝ problem.feasibleSet problem := by
  refine ⟨problem.feasibleSet_convex, ?_⟩
  intro x hx y hy a b ha hb hab
  simpa using problem.objective_convex.2 (by simp) (by simp) ha hb hab

end ConvexMinimizationProblem

end
