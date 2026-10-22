/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_2
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_33

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
Proposition 4.1.3 lies in first-order convex analysis on a real Hilbert space.

Sampled owner-style declarations:
* `ConvexOn.lower_tangent_plane` in `Chap02/Definition_2_2`
* `isMinOn_iff_eq_sInf_range` in `Chap03/Definition_3_33`
* mathlib `real_inner_le_norm`

Best owner abstraction:
* `ConvexOn ℝ Set.univ f`

Primitive data:
* the objective `f`
* whole-space convexity of `f`
* differentiability of `f` at the base point where the gradient is evaluated
* for the source-facing proposition, a chosen global minimizer `xStar` witnessing that the
  canonical optimal value `sInf (Set.range f)` is attained

Derived API:
* the first-order support inequality from `ConvexOn.lower_tangent_plane`
* the radius estimate from Cauchy--Schwarz
* the sharper comparison-point gap estimate on a closed ball
* the optimal-value identity `sInf (Set.range f) = f xStar` from
  `isMinOn_iff_eq_sInf_range`

Source/core/bridge triage:
* source-facing: the suboptimality bound relative to the canonical optimal value, witnessed by a
  chosen minimizer
* core/canonical: `ConvexOn.lower_tangent_plane`
* bridge/view: the comparison-point estimate obtained by specializing that owner theorem to
  `Set.univ` and combining it with `real_inner_le_norm`, together with the attained-infimum bridge
  `isMinOn_iff_eq_sInf_range`

The main proposition now records the suboptimality gap against the canonical optimal value
`sInf (Set.range f)`, so the minimizer witness is mathematically active rather than an unused
binder. The sharper owner-level comparison estimate is retained only as a companion theorem.
-/
namespace ConvexOn

/-- Helper for Proposition 4.1.3: for a convex function on a real Hilbert space that is
differentiable at the base point `x`, the objective gap to any comparison point within distance at
most `R` from `x` is bounded by `R` times the gradient norm at `x`. -/
-- Proof sketch: apply `ConvexOn.lower_tangent_plane` at the base point `x` and comparison point
-- `y`, rewrite the resulting support inequality as a bound on `f x - f y`, and then use
-- Cauchy--Schwarz together with `‖x - y‖ ≤ R`.
theorem gap_le_radius_mul_norm_gradient_of_dist_le
    {f : E → ℝ} (hf_conv : ConvexOn ℝ Set.univ f) {x : E} (hf_diff : DifferentiableAt ℝ f x)
    {y : E} {R : ℝ}
    (hxy : ‖x - y‖ ≤ R) :
    f x - f y ≤ R * ‖∇ f x‖ := by
  have hsupport :
      f y ≥ f x + inner ℝ (∇ f x) (y - x) := by
    simpa [gradientWithin, gradient, fderivWithin_univ] using
      hf_conv.lower_tangent_plane x (by simp) hf_diff.differentiableWithinAt y (by simp)
  have hfirst : f x - f y ≤ inner ℝ (∇ f x) (x - y) := by
    have hinner :
        inner ℝ (∇ f x) (y - x) = -inner ℝ (∇ f x) (x - y) := by
      calc
        inner ℝ (∇ f x) (y - x) = inner ℝ (∇ f x) (-(x - y)) := by
          congr 2
          abel
        _ = -inner ℝ (∇ f x) (x - y) := by
          rw [inner_neg_right]
    linarith
  calc
    f x - f y ≤ inner ℝ (∇ f x) (x - y) := hfirst
    _ ≤ ‖∇ f x‖ * ‖x - y‖ := real_inner_le_norm _ _
    _ ≤ ‖∇ f x‖ * R := mul_le_mul_of_nonneg_left hxy (norm_nonneg _)
    _ = R * ‖∇ f x‖ := by ring

end ConvexOn

/-- Proposition 4.1.3: if `f` is convex, `xStar` is a global minimizer of `f`, and `f` is
differentiable at a point `x` lying in the closed ball of radius `R` around `xStar`, then the
suboptimality gap above the optimal value `sInf (Set.range f)` is bounded by `R * ‖∇ f x‖`.
Since `xStar` attains that infimum, this is equivalent to the textbook form
`f x - f xStar ≤ R * ‖∇ f x‖`. -/
-- Proof sketch: use the Chapter 3 owner bridge `isMinOn_iff_eq_sInf_range` to rewrite the
-- canonical optimal value `sInf (Set.range f)` as `f xStar`, then apply the comparison-point
-- estimate with `y = xStar`.
theorem convex_suboptimality_le_radius_mul_norm_gradient
    (f : E → ℝ) (hf_conv : ConvexOn ℝ Set.univ f)
    (xStar : E) (hxStar : IsMinOn f Set.univ xStar) {x : E} (hf_diff : DifferentiableAt ℝ f x)
    {R : ℝ}
    (hx : ‖x - xStar‖ ≤ R) :
    f x - sInf (Set.range f) ≤ R * ‖∇ f x‖ := by
  have hsInf_eq : sInf (Set.range f) = f xStar := by
    have hbelow : BddBelow (Set.range f) := ⟨f xStar, by
      rintro _ ⟨y, rfl⟩
      exact hxStar (by simp)
    ⟩
    exact ((isMinOn_iff_eq_sInf_range hbelow).1 hxStar).symm
  rw [hsInf_eq]
  exact hf_conv.gap_le_radius_mul_norm_gradient_of_dist_le hf_diff hx

end
