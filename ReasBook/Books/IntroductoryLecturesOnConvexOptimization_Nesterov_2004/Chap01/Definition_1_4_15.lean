/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {xBar : E}

/-
Primary domain: first-order differential calculus on real Hilbert spaces.

Source/core/bridge triage:
* source-facing item: the stationary-point condition at `xBar`
* core/canonical owner abstraction: `HasGradientAt f 0 xBar`
* bridge/view: the derived reformulation
  `DifferentiableAt ℝ f xBar ∧ ∇ f xBar = 0`

Relevant owner declarations sampled before refining:
* `HasGradientAt`
* `DifferentiableAt.hasGradientAt`
* `HasGradientAt.differentiableAt`
* `HasGradientAt.gradient`

Primitive data:
* the owner predicate `HasGradientAt f g xBar`

Derived API:
* differentiability at `xBar`
* identification of the canonical gradient with the witness `g`

The source specializes this owner to `f : ℝⁿ → ℝ`, but no Euclidean coordinates or
finite-dimensional structure are used in the owner itself. Definition 1.4.15 is therefore a
recall item: a stationary point of `f` at `xBar` is exactly the specialized owner condition
`HasGradientAt f 0 xBar`.
-/

/- Definition 1.4.15: for a differentiable real-valued function, a point is stationary exactly
when it satisfies the canonical zero-gradient owner condition `HasGradientAt f 0 xBar`. -/
#check HasGradientAt f 0 xBar

-- Proof sketch: use `hf.hasGradientAt` to identify the canonical gradient witness at `xBar` with
-- `∇ f xBar`; then `HasGradientAt.gradient` turns `HasGradientAt f 0 xBar` into the zero-gradient
-- equation, and conversely `hf.hasGradientAt` rewrites `∇ f xBar = 0` back to the stationary
-- owner condition.
/-- Under differentiability at `xBar`, the canonical stationary-point owner is equivalent to the
textbook equation `∇ f xBar = 0`. -/
theorem hasGradientAt_zero_iff_gradient_eq_zero (hf : DifferentiableAt ℝ f xBar) :
    HasGradientAt f 0 xBar ↔ ∇ f xBar = 0 := by
  constructor
  · intro h
    simpa using h.gradient
  · intro h
    convert hf.hasGradientAt using 1
    exact h.symm

end
