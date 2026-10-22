/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Theorem 2.29 lies in first-order optimality for convex minimization on a real inner-product
space.

Sampled owner-style declarations before refining this file:
* mathlib `ConvexOn`
* mathlib `IsMinOn`
* `ConvexOn.lower_tangent_plane` in `Definition_2_2`, the chapter owner theorem for the
  first-order support inequality on a convex set
* `DifferentiableAt.hasGradientAt`, the canonical bridge from the source differentiability
  hypothesis to an explicit gradient witness
* `IsMinOn.isGLB` in mathlib, a canonical minimizer consequence later reused from this owner
  theorem

Best owner abstraction:
* `ConvexOn ℝ Q f` together with `IsMinOn f Q xStar`

Primitive data:
* the feasible set `Q`
* the objective `f`
* the feasible point `xStar`
* convexity of `f` on `Q`
* the constrained minimizing predicate `IsMinOn f Q xStar`

Derived API:
* the supporting-nesterovHyperplane inequality from `ConvexOn.lower_tangent_plane`
* the owner theorem `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt`
* the source-facing specialization obtained from `DifferentiableAt.hasGradientAt`

Source/core/bridge triage:
* source-facing: Theorem 2.29 as the variational characterization of constrained optimality using
  the ambient gradient `∇ f xStar`
* core/canonical: `ConvexOn ℝ Q f`, `HasGradientAt f g xStar`, and `IsMinOn f Q xStar`
* bridge/view: the source differentiability hypothesis specialized via
  `DifferentiableAt.hasGradientAt`
-/

namespace ConvexOn

variable {Q : Set E} {f : E → ℝ} {xStar g : E}

/-- A feasible point minimizes a convex function on `Q` exactly when every feasible displacement
has nonnegative pairing with an ambient gradient witness at that point. -/
-- Proof sketch: the forward implication combines `ConvexOn.lower_tangent_plane` at `xStar` with
-- the minimizing property to force nonnegative pairing against every feasible displacement. For
-- the reverse implication, restrict `f` to the segment from `xStar` to `x`; convexity gives a
-- one-variable convex function with a minimum at `0`, and `hf_grad` identifies its derivative
-- there with `inner ℝ g (x - xStar)`.
theorem isMinOn_iff_variational_inequality_of_hasGradientAt
    (hf_conv : ConvexOn ℝ Q f) (hxStar : xStar ∈ Q) (hf_grad : HasGradientAt f g xStar) :
    IsMinOn f Q xStar ↔ ∀ x ∈ Q, 0 ≤ inner ℝ g (x - xStar) := by
  constructor
  · intro hopt x hx
    -- Every feasible displacement comes from a segment inside `Q`, so it is a valid tangent
    -- direction for the localized minimizing property at `xStar`.
    have hdir : x - xStar ∈ posTangentConeAt Q xStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hf_conv.1.segment_subset hxStar hx)
    -- Localizing the constrained minimum turns the gradient witness into a nonnegative directional
    -- derivative along that feasible direction.
    have hfirstOrder :=
      hopt.localize.hasFDerivWithinAt_nonneg hf_grad.hasFDerivAt.hasFDerivWithinAt hdir
    -- The derivative supplied by `HasGradientAt` evaluates to the ambient inner product.
    simpa [hf_grad.hasFDerivAt.fderiv, innerSL_apply_apply] using hfirstOrder
  · intro hvari
    rw [isMinOn_iff]
    intro x hx
    -- Turn the ambient gradient witness into the corresponding within-set witness at `xStar`.
    have hgradWithin : HasGradientWithinAt f g Q xStar := by
      convert
        (hf_grad.hasFDerivAt.hasFDerivWithinAt.hasGradientWithinAt :
          HasGradientWithinAt f _ Q xStar) using 1
      simp
    -- Convexity gives the tangent-plane lower bound at `xStar`.
    have hplane :=
      hf_conv.lower_tangent_plane_of_hasGradientWithinAt xStar hxStar g
        hgradWithin x hx
    -- The assumed variational inequality makes the tangent correction term nonnegative.
    have hpair : 0 ≤ inner ℝ g (x - xStar) := hvari x hx
    linarith

end ConvexOn

namespace ConvexOn

variable {Q : Set E} {f : E → ℝ} {xStar : E}

/-- Theorem 2.29: for a convex function `f` on `Q` that is differentiable at the feasible point
`xStar`, constrained optimality at `xStar` is equivalent to the variational inequality
`⟪∇ f xStar, x - xStar⟫ ≥ 0` for every `x ∈ Q`. -/
-- Proof sketch: specialize the preceding owner theorem using the canonical gradient
-- witness `hf_diff.hasGradientAt`.
theorem isMinOn_iff_gradient_variational_inequality
    (hf_conv : ConvexOn ℝ Q f) (hxStar : xStar ∈ Q) (hf_diff : DifferentiableAt ℝ f xStar) :
    IsMinOn f Q xStar ↔ ∀ x ∈ Q, 0 ≤ inner ℝ (∇ f xStar) (x - xStar) :=
  hf_conv.isMinOn_iff_variational_inequality_of_hasGradientAt hxStar hf_diff.hasGradientAt

end ConvexOn

end
