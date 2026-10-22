/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Calculus.Gradient.Basic

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Primary domain: first-order differential calculus on real inner-product spaces, specialized in the
source text to `ℝⁿ`.

Relevant owner-style declarations sampled before refining:
* `HasGradientAt`
* `DifferentiableAt.hasGradientAt`
* `HasGradientAt.differentiableAt`
* `hasGradientAt_iff_isLittleO`

Best owner abstraction:
* the canonical gradient predicate `HasGradientAt f g xBar`

Primitive data:
* the gradient witness `g`
* the owner predicate `HasGradientAt f g xBar`

Derived API:
* `DifferentiableAt ℝ f xBar`
* the little-o reformulation `hasGradientAt_iff_isLittleO`
* the affine-approximation reformulations below

Source/core/bridge triage:
* source-facing: `differentiableAt_iff_exists_sub_affineApproximation_isLittleO`
* core/canonical: `HasGradientAt f g xBar`
* bridge/view: `hasGradientAt_iff_sub_affineApproximation_isLittleO`

The file therefore keeps the textbook affine-approximation statement as a thin bridge over the
owner API, without introducing any parallel wrapper. Since neither the statement nor the proof
uses coordinates, the public bridge is stated at the canonical real Hilbert-space level and
specializes to `ℝⁿ`.
-/

/-- The canonical gradient predicate is equivalent to the textbook affine-approximation remainder
formulation. -/
theorem hasGradientAt_iff_sub_affineApproximation_isLittleO
    {f : E → ℝ} {xBar g : E} :
    HasGradientAt f g xBar ↔
      (fun y ↦ f y - (f xBar + inner ℝ g (y - xBar))) =o[nhds xBar] fun y ↦ ‖y - xBar‖ := by
  simpa [Asymptotics.isLittleO_norm_right, sub_eq_add_neg, add_assoc,
    add_left_comm, add_comm] using
    (hasGradientAt_iff_isLittleO : HasGradientAt f g xBar ↔
      (fun y : E ↦ f y - f xBar - inner ℝ g (y - xBar)) =o[nhds xBar] fun y ↦ y - xBar)

/-- Definition 1.4.6: for a scalar-valued function on a real inner-product space, and hence in
particular on `ℝⁿ`, differentiability at `xBar` is equivalent to the existence of a gradient
vector whose affine approximation at `xBar` differs from `f` by a term that is little-o of
`‖y - xBar‖` as `y → xBar`; equivalently, `g` is the vector representing the first-order linear
part of that affine approximation. -/
theorem differentiableAt_iff_exists_sub_affineApproximation_isLittleO
    {f : E → ℝ} {xBar : E} :
    DifferentiableAt ℝ f xBar ↔
      ∃ g : E,
        (fun y ↦ f y - (f xBar + inner ℝ g (y - xBar))) =o[nhds xBar] fun y ↦ ‖y - xBar‖ := by
  constructor
  · intro hf
    exact ⟨∇ f xBar, hasGradientAt_iff_sub_affineApproximation_isLittleO.mp hf.hasGradientAt⟩
  · rintro ⟨g, hg⟩
    exact (hasGradientAt_iff_sub_affineApproximation_isLittleO.mpr hg).differentiableAt
