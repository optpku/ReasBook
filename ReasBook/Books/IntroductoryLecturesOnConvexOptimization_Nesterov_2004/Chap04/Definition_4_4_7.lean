/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 4.4.7 lies in the Fréchet-derivative / gradient calculus domain.

Sampled owner-style declarations:
- mathlib `fderiv`
- mathlib `DifferentiableAt.hasGradientAt`
- mathlib `HasGradientAt.fderiv_apply`
- mathlib `inner_gradient_left`

Best owner abstraction:
- core/canonical: `fderiv`

Primitive data:
- a map `f : E → F`
- a base point `x : E`

Derived API:
- the canonical gradient witness `DifferentiableAt.hasGradientAt`
- the scalar-valued derivative evaluation formula `HasGradientAt.fderiv_apply`
- the symmetric inner-product reformulation `inner_gradient_left`

Source/core/bridge triage:
- source-facing: the Jacobian `F'(x)` of a differentiable map and, in the real Hilbert-space
  scalar-valued case, its evaluation on a direction
- core/canonical: `fderiv`
- bridge/view: the gradient-pairing formulas derived from `HasGradientAt.fderiv_apply` and
  `inner_gradient_left`

This item is therefore a recall file. The Jacobian itself is the canonical Fréchet derivative, and
the real-valued Hilbert-space specialization should reuse the existing gradient bridge instead of
introducing a chapter-local wrapper theorem.
-/

/- Definition 4.4.7: for a Fréchet differentiable map `F : E₁ → E₂`, the Jacobian at `x` is the
canonical Fréchet derivative `fderiv`; in the real Euclidean setting of the text, this is the
linear operator `fderiv ℝ F x : E₁ →L[ℝ] E₂` characterized by the usual directional quotient
limit. -/
recall fderiv

/- For a real-valued differentiable function on a real Hilbert space, applying the Jacobian to a
direction is exactly the existing gradient-pairing bridge `inner_gradient_left`. -/
recall inner_gradient_left

end
