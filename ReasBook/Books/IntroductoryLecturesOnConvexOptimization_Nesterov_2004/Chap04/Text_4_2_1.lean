/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.1 lies in the real inner-product-space gradient/Fréchet-derivative domain.

Relevant owner-style declarations sampled before refinement:
- `DifferentiableAt.hasGradientAt`
- `HasGradientAt.fderiv_apply`
- `inner_gradient_left`
- `HasGradientAt.hasFDerivAt`

Best owner abstraction:
- `DifferentiableAt.hasGradientAt`

Primitive data:
- a function `f : E → ℝ`
- a base point `x : E`

Derived API:
- the canonical gradient witness `DifferentiableAt.hasGradientAt`
- the owner-side derivative evaluation formula `HasGradientAt.fderiv_apply`
- its differentiability-point specialization `inner_gradient_left`

Source/core/bridge triage:
- source-facing: the textbook statement that, at differentiability points, the gradient
  represents the derivative
- core/canonical: `DifferentiableAt.hasGradientAt`
- bridge/view: `HasGradientAt.fderiv_apply` and `inner_gradient_left`

The first sentence of Text 4.2.1 is already exactly the mathlib owner theorem, so this file
recalls the canonical owner surface directly instead of keeping parallel wrapper lemmas. The
ambient model is generalized from `EuclideanSpace ℝ (Fin n)` to an arbitrary complete real inner
product space, since the canonical owner API and the source mathematics use only that structure.
-/

recall DifferentiableAt.hasGradientAt

recall HasGradientAt.fderiv_apply

recall inner_gradient_left
