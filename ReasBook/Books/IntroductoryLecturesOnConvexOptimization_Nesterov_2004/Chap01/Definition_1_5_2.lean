/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

/- Definition 1.5.2 is the Chapter 1 source-facing recall point for the textbook class
`C^{1,1}_L`.

Source/core/bridge triage:
* source-facing: the textbook `C^{1,1}_L` condition on a real-valued function
* core/canonical: the owner predicates `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`
* bridge/view: the pointwise estimate `hgrad.norm_sub_le x y` and the differentiability
  consequence `ContDiff.differentiable_one`

Primary domain:
* first-order smooth optimization on real Hilbert spaces

Sampled owner-style declarations:
* `gradient`
* `ContDiff ℝ 1 f`
* `LipschitzWith L (∇ f)`
* `ContDiff.differentiable_one`
* `LipschitzWith.norm_sub_le`

Owner abstraction:
* the canonical pair `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`

Primitive data:
* a function `f`
* a Lipschitz constant `L`

Derived API:
* ordinary differentiability from `ContDiff.differentiable_one`
* the textbook estimate `‖∇ f x - ∇ f y‖ ≤ L ‖x - y‖` from `LipschitzWith.norm_sub_le`

This item is treated as a canonical type-expression recall rather than a new owner definition:
nearby Chapter 1 files use the pair `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)` directly,
so introducing a second wrapper or notation here would create a parallel API. -/

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {L : NNReal}

/- Definition 1.5.2: the textbook class `C_{L}^{1,1}(ℝ^n)` is represented in this chapter by
the conjunction `ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f)`, meaning that `f` is `C¹` and its
gradient is globally `L`-Lipschitz. -/
#check (ContDiff ℝ 1 f ∧ LipschitzWith L (∇ f))

/- The `C¹` component of Definition 1.5.2 supplies ordinary differentiability. -/
recall ContDiff.differentiable_one

/- The Lipschitz-gradient component of Definition 1.5.2 yields the textbook pointwise estimate
`‖∇ f x - ∇ f y‖ ≤ L ‖x - y‖`. -/
recall LipschitzWith.norm_sub_le

end
