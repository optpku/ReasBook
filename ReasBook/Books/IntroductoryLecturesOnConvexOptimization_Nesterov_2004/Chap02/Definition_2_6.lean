/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex SeminormDualNorm

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]
variable {p : Seminorm ℝ E} [Seminorm.IsNorm p] {L : NNReal}
variable {Q : Set E} {f : E → ℝ}

/- Definition 2.6 is a source-facing recall in first-order smooth convex analysis on a feasible
set, measured by a norm and its dual norm.

Primary domain:
* the smooth-convex owner `f ∈ 𝓕[L, p]¹¹(Q)` on a set `Q`

Sampled owner-style declarations:
* `ConvexC1On` in `Definition_2_4`, the underlying `C¹` convex owner on `Q`
* `‖g‖[p,*]` in `Definition_2_5`, the source-facing dual-norm notation
* `ConvexC1SeminormSmoothOn` in `Theorem_2_5`, the canonical owner for Definition 2.6
* `ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le` in `Theorem_2_5`, the derived gradient
  inequality API

Best owner abstraction:
* source-facing: `f ∈ 𝓕[L, p]¹¹(Q)`
* core/canonical: `ConvexC1SeminormSmoothOn p L Q f`
* bridge/view: the owner projection lemmas `.convexC1On`, `.contDiffOn`, `.convexOn`, and
  `.dualNorm_gradient_sub_le`

Primitive data:
* the feasible set `Q`
* the objective `f`
* the seminorm `p`
* the smoothness constant `L`
* the owner predicate `ConvexC1SeminormSmoothOn p L Q f`

Derived API:
* `ConvexC1SeminormSmoothOn.convexC1On`
* `ConvexC1SeminormSmoothOn.contDiffOn`
* `ConvexC1SeminormSmoothOn.convexOn`
* `ConvexC1SeminormSmoothOn.hasGradientAt`
* `ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le`

Source/core/bridge triage:
* source-facing: the textbook class `f ∈ 𝓕[L, p]¹¹(Q)`
* core/canonical: `ConvexC1SeminormSmoothOn p L Q f`
* bridge/view: the owner projections and the displayed estimate
  `‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y)`

This recall file therefore uses the chapter owner directly instead of re-expanding its defining
conjunction. No parallel local wrapper or duplicate conjunction API is kept here. -/

section

variable (p) (L) (Q) (f)

/- Definition 2.6: a function on `Q` belongs to the smooth-convex class exactly when
`f ∈ 𝓕[L, p]¹¹(Q)`, whose defining gradient clause is
`‖∇ f x - ∇ f y‖[p,*] ≤ (L : ℝ) * p (x - y)` together with the ambient gradient witness
`HasGradientAt f (∇ f x) x` on `Q`. -/
#check f ∈ 𝓕[L, p]¹¹(Q)

/- The owner predicate exposes its `C¹` convexity and smoothness projections canonically. -/
recall ConvexC1SeminormSmoothOn.convexC1On

recall ConvexC1SeminormSmoothOn.contDiffOn

recall ConvexC1SeminormSmoothOn.convexOn

recall ConvexC1SeminormSmoothOn.hasGradientAt

/- The displayed dual-norm gradient estimate is also owned canonically by the chapter predicate.
-/
recall ConvexC1SeminormSmoothOn.dualNorm_gradient_sub_le

end
