/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_13

-- Declarations for this item will be appended below by the statement pipeline.

/- Primary domain: whole-space strong-convexity quadratic growth for stationary points on complete
real inner-product spaces.

Sampled owner-style declarations:
* `quadratic_growth_of_gradient_eq_zero` in `Definition_2_13`
* `StrongConvexOnWith.quadratic_growth_of_hasGradientAt_zero` in `Definition_2_13`
* `StrongConvexOnWith.quadratic_growth_of_isMinOn_of_mem` in `Definition_2_14`
* `f ∈ 𝓛^1[μ]` in `Definition_2_14`

Best owner abstraction:
* source-facing: the class hypothesis `f ∈ 𝓛^1[μ]`
* core/canonical: `StrongConvexOnWith.quadratic_growth_of_gradient_eq_zero`
* bridge/view: `quadratic_growth_of_gradient_eq_zero`, the ambient-norm specialization of the
  core owner theorem to the source class `𝓛^1[μ]`

Primitive data:
* the source-facing whole-space strong-convexity hypothesis `f ∈ 𝓛^1[μ]`
* differentiability at the stationary point
* the equation `∇ f xStar = 0`

Derived API:
* the quadratic-growth lower bound at arbitrary `x`

Source/core/bridge triage:
* source-facing: Theorem 2.9 on the textbook class surface `𝓛^1[μ]`
* core/canonical: `StrongConvexOnWith.quadratic_growth_of_gradient_eq_zero`
* bridge/view: `quadratic_growth_of_gradient_eq_zero` in `Definition_2_13`

This numbered file is recall-only: after specializing the owner theorem in `Definition_2_13` to
the ambient norm, the public statement is exactly the textbook theorem surface, so no parallel
top-level wrapper is kept here.
-/

/- Theorem 2.9 is the direct source-facing recall of the stationary-point quadratic-growth theorem
for the strong-convexity class `𝓛^1[μ]`. -/
recall quadratic_growth_of_gradient_eq_zero
