/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: first-order convex minimization of differentiable objectives on real inner
product spaces.

Sampled owner-style declarations:
* `IsMinOn f Set.univ xStar` in `Definition_2_1`, the Chapter 2 minimizer owner
* `ConvexOn.lower_tangent_plane` in `Definition_2_2`, the source-faithful first-order support
  inequality for convex functions
* `DifferentiableAt.differentiableWithinAt`, the bridge from ambient differentiability to the
  whole-space within-set derivative needed by `lower_tangent_plane`

Best owner abstraction:
* `ConvexOn ℝ Set.univ f` together with `IsMinOn f Set.univ xStar`

Primitive data:
* the objective `f : E → ℝ`
* the candidate minimizer `xStar : E`
* whole-space convexity of `f`
* pointwise differentiability of `f` at `xStar`
* the stationary-gradient identity `∇ f xStar = 0`

Derived API:
* the textbook pointwise lower bound `∀ x, f xStar ≤ f x`
* the minimizing conclusion `IsMinOn f Set.univ xStar`

Source/core/bridge triage:
* source-facing: Theorem 2.1 for convex objectives with a stationary differentiable point
* core/canonical: `ConvexOn.lower_tangent_plane`
* bridge/view: `isMinOn_univ_iff`, converting the pointwise inequality into `IsMinOn`
-/

/-- Helper for Theorem 2.1: the tangent-plane inequality at a stationary point gives the textbook
pointwise lower bound on the whole space. -/
-- Proof sketch: apply `ConvexOn.lower_tangent_plane` at the base point `xStar`, simplify the
-- whole-space gradient term to the ambient gradient, and then use `∇ f xStar = 0`.
lemma convex_stationary_point_pointwise_lower_bound
    {f : E → ℝ} {xStar : E} (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_diff : DifferentiableAt ℝ f xStar) (hgrad : ∇ f xStar = 0) :
    ∀ x : E, f xStar ≤ f x := by
  intro x
  -- Compare `f x` against the tangent plane supported at the stationary base point `xStar`.
  have hsupport :
      f x ≥ f xStar + inner ℝ (∇ f xStar) (x - xStar) := by
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hf_conv.lower_tangent_plane
        xStar (by simp) hf_diff.differentiableWithinAt x (by simp)
  -- The stationary gradient annihilates the linear correction term.
  simpa [hgrad] using hsupport

/-- Theorem 2.1: a critical point of a convex differentiable function is a global minimizer. -/
-- Proof sketch: rewrite whole-space optimality as the textbook pointwise inequality, then use the
-- supporting-nesterovHyperplane inequality at `xStar` and the stationary-gradient identity.
theorem stationaryPoint_isMinOn_of_convexOn
    {f : E → ℝ} {xStar : E} (hf_conv : ConvexOn ℝ Set.univ f)
    (hf_diff : DifferentiableAt ℝ f xStar) (hgrad : ∇ f xStar = 0) :
    IsMinOn f Set.univ xStar := by
  -- Rewrite whole-space optimality into the textbook inequality `f xStar ≤ f x` for all `x`.
  rw [isMinOn_univ_iff]
  -- The helper is exactly the lower-tangent-plane argument from the source proof.
  exact convex_stationary_point_pointwise_lower_bound hf_conv hf_diff hgrad

end
