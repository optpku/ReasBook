/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 4.2.2 lies in the first-order differential-calculus / gradient domain on real
Hilbert spaces.

Sampled owner-style declarations:
* `gradient`, recalled in `Chap01/Definition_1_4_7`, the canonical gradient vector;
* `DifferentiableAt.hasGradientAt`, which supplies the gradient witness at differentiability
  points;
* `hasGradientAt_iff_sub_affineApproximation_isLittleO`, the Chapter 1 affine-approximation
  bridge for first-order Taylor expansion.

Best owner abstraction:
* source-facing/core: the canonical pointwise gradient `∇ f xBar`.

Primitive data:
* a function `f : E → ℝ`;
* a base point `xBar : E`.

Derived API:
* the first-order Taylor remainder estimate for `∇ f xBar` under differentiability at `xBar`;
* uniqueness of any vector satisfying that remainder estimate.

Source/core/bridge triage:
* source-facing: the vector appearing in the first-order Taylor expansion at `xBar`;
* core/canonical: `∇ f xBar`;
* bridge/view: `HasGradientAt` and the Chapter 1 little-o characterization.

This item therefore reuses the existing gradient owner directly rather than introducing a parallel
Chapter 4 definition. -/

section

variable (f : E → ℝ) (xBar : E)

set_option linter.hashCommand false in
/- Definition 4.2.2: for a differentiable real-valued function on a complete real inner-product
space, the gradient at `xBar`, denoted `∇ f xBar`, is the canonical gradient vector. -/
#check (∇ f xBar : E)

end

/-- The gradient at a differentiability point gives the first-order Taylor expansion remainder of
`f` at `xBar`. -/
-- Proof sketch: obtain `HasGradientAt f (∇ f xBar) xBar` from `hf.hasGradientAt`, then rewrite it
-- with mathlib's zero-centered little-o gradient characterization.
theorem gradient_taylorExpansion_isLittleO
    (f : E → ℝ) (xBar : E) (hf : DifferentiableAt ℝ f xBar) :
    (fun h ↦ f (xBar + h) - (f xBar + inner ℝ (∇ f xBar) h)) =o[nhds (0 : E)] fun h ↦ ‖h‖ := by
  rw [Asymptotics.isLittleO_norm_right]
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    (hasGradientAt_iff_isLittleO_nhds_zero.mp hf.hasGradientAt)

/-- Any vector satisfying the first-order Taylor expansion remainder at `xBar` is the gradient at
that point. -/
-- Proof sketch: translate the displayed little-o assumption into `HasGradientAt f g xBar` by the
-- zero-centered little-o characterization, then use `HasGradientAt.gradient`.
theorem eq_gradient_of_taylorExpansion_isLittleO
    (f : E → ℝ) (xBar : E) (g : E)
    (hg :
      (fun h ↦ f (xBar + h) - (f xBar + inner ℝ g h)) =o[nhds (0 : E)] fun h ↦ ‖h‖) :
    g = ∇ f xBar := by
  rw [Asymptotics.isLittleO_norm_right] at hg
  have hg' :
      (fun h ↦ f (xBar + h) - f xBar - inner ℝ g h) =o[nhds (0 : E)] fun h ↦ h := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hg
  have hgrad : HasGradientAt f g xBar := by
    exact hasGradientAt_iff_isLittleO_nhds_zero.mpr hg'
  simpa using hgrad.gradient.symm

end
