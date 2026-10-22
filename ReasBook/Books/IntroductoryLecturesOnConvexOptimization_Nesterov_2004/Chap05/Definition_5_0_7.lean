/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Domain design notes:

Primary domain:
* functions with Lipschitz-continuous Hessian on a real Hilbert space

Sampled owner-style declarations:
* `HasLipschitzContinuousHessian` in `Chap04/Definition_4_2_7`
* `HasLipschitzContinuousHessian.contDiff`
* `HasLipschitzContinuousHessian.norm_sub_le`
* the theorem-surface notation `f ∈ C22[M]`

Source/core/bridge triage:
* source-facing: the textbook class `C_M^{2,2}(ℝⁿ)`
* core/canonical: `HasLipschitzContinuousHessian M f`
* bridge/view: the theorem-surface notation `f ∈ C22[M]`, the `C²` projection
  `HasLipschitzContinuousHessian.contDiff`, and the Hessian-difference estimate
  `HasLipschitzContinuousHessian.norm_sub_le`

Primitive data:
* none; this is a recall-only item

Derived API:
* the owner predicate `HasLipschitzContinuousHessian M f`
* the textbook notation `f ∈ C22[M]`
* the `C²` regularity projection
* the Hessian-difference estimate

This item therefore reuses the Chapter 4 owner directly instead of introducing a second local
wrapper. The textbook `ℝⁿ` statement is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/

section

variable {M : NNReal} {f : E → ℝ}

/- Definition 5.0.7: the textbook class `C_M^{2,2}(ℝⁿ)` is represented in this project by the
canonical owner `HasLipschitzContinuousHessian M f`, written on theorem surfaces as
`f ∈ C22[M]`. Its defining consequences are the inherited `C²` regularity and the displayed
Hessian Lipschitz estimate `‖∇² f(x) - ∇² f(y)‖ ≤ M ‖x - y‖`. -/
recall HasLipschitzContinuousHessian

set_option linter.hashCommand false in
#check (f ∈ C22[M])

recall HasLipschitzContinuousHessian.contDiff
recall HasLipschitzContinuousHessian.norm_sub_le

end
