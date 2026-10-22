/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_3_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConstrainedArgmin SmoothConvex

noncomputable section

universe u

/- Primary domain: smooth convex unconstrained minimization on finite-dimensional real
inner-product spaces.

Owner-style declarations sampled for this item:
* `IsMinOn f Set.univ xStar` in `Definition_2_1`, the Chapter 2 source-facing owner of the
  unconstrained minimizer part of `min_x f(x)`;
* `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` in `Theorem_2_5`, the objective-side owner for the whole-space
  smooth-convex class on the intrinsic ambient space `E`;
* `ConvexC1SeminormSmooth.gradient_lipschitz`, the derived norm-gradient-Lipschitz view of that
  owner predicate;
* `SetConstrainedMinimizationProblem.unconstrained` in `Chap01/Definition_1_3_3`, the Chapter 1
  owner for the associated whole-space minimization problem.

Best owner abstraction:
* source-facing core:
  `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` together with `IsMinOn f Set.univ xStar`;
* bridge/view:
  the associated Chapter 1 owner
  `SetConstrainedMinimizationProblem.unconstrained f`.

Primitive data:
* the objective `f : E → ℝ`;
* the owner smooth-convex hypothesis on `f`;
* a minimizing point `xStar : E` with `IsMinOn f Set.univ xStar`.

Derived API:
* convexity, whole-space `C¹` regularity, and norm-gradient Lipschitz continuity of `f`;
* the associated whole-space constrained-owner package
  `SetConstrainedMinimizationProblem.unconstrained f`;
* the Chapter 1 optimal-value and approximate-minimizer API for that package.

Source/core/bridge triage:
* source-facing: a smooth convex objective on `E` together with the unconstrained minimization
  problem `min_x f(x)` and a global minimizer `xStar`;
* core/canonical: `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` and `IsMinOn f Set.univ xStar`;
* bridge/view: the packaged owner problem on `Set.univ` and its `optimalValue` API.

Definition 2.19 is therefore recorded by reusing the Chapter 2 minimizer API from
`Definition_2_1` and the objective-side owner predicate from `Theorem_2_5`, without a parallel
local smooth-problem wrapper. The Chapter 1 packaged problem is kept only as a bridge for
downstream optimal-value language. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

local notation "p" => normSeminorm ℝ E

variable (L : NNReal) (f : E → ℝ)
variable (xStar : E)

recall ConvexC1SeminormSmooth
recall ConvexC1SeminormSmooth.gradient_lipschitz
recall SetConstrainedMinimizationProblem.unconstrained
recall SetConstrainedMinimizationProblem.optimalValue

set_option linter.hashCommand false

/-
Definition 2.19: given a smooth convex objective `f ∈ 𝓕[L, p]¹¹`, the unconstrained
minimization problem `min_{x ∈ E} f(x)` is the Chapter 1 whole-space owner
`SetConstrainedMinimizationProblem.unconstrained f`.
-/
#check
  (SetConstrainedMinimizationProblem.unconstrained f : SetConstrainedMinimizationProblem E)

#check f ∈ 𝓕[L, p]¹¹

#check IsMinOn f Set.univ xStar

#check
  (show IsMinOn f Set.univ xStar ↔ ∀ x : E, f xStar ≤ f x from
    isMinOn_univ_iff)

#check ((SetConstrainedMinimizationProblem.unconstrained f).optimalValue : EReal)
