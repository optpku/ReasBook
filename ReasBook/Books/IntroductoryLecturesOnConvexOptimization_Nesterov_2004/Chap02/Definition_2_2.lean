/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Example_2_67

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Definition 2.2 lies in first-order convex analysis for `C¹` functions on real Hilbert spaces.

Sampled owner-style declarations:
* mathlib `ConvexOn`
* mathlib `gradientWithin` / `HasGradientWithinAt`
* Chapter 2 `Definition_2_6` for the within-set derivative owner API
* Chapter 4 `Definition_4_2_8`, which keeps a source-facing first-order lower-support statement
  while using a canonical convexity owner underneath

Source/core/bridge triage:
* source-facing: the lower-tangent characterization of convexity for a `C¹` function on `Q`
* core/canonical: `ConvexOn ℝ Q f`
* bridge/view: the pointwise tangent-plane inequality at a feasible base point, first with an
  explicit gradient witness and then with the canonical `gradientWithin`

Primitive data:
* the feasible set `Q`
* the objective `f`
* for the source-facing theorem, `ContDiffOn ℝ 1 f Q`
* for the canonical bridge, `ConvexOn ℝ Q f`
* for pointwise tangent data, an explicit witness `HasGradientWithinAt f g Q x`

Derived API:
* `ConvexOn.lower_tangent_plane_of_hasGradientWithinAt`
* `ConvexOn.lower_tangent_plane`
* `convexOn_iff_lower_tangent_plane`, the sharper owner bridge using `DifferentiableOn ℝ f Q`
* `convexOn_iff_lower_tangent_plane_of_contDiffOn`, the source-facing `C¹` formulation

This file therefore keeps the lower-tangent characterization as the main numbered outcome and uses
`ConvexOn` only as the canonical owner behind it. The explicit `HasGradientWithinAt` statement is
the primitive pointwise bridge; the `gradientWithin` and `ContDiffOn` forms are derived from that
owner-level bridge rather than packaged as parallel owners. -/

namespace ConvexOn

variable {Q : Set E} {f : E → ℝ}

/-- A convex function lies above every feasible tangent plane arising from an explicit within-set
gradient witness at the base point. -/
-- Proof sketch: this is the standard first-order characterization of convexity for
-- differentiable functions on convex sets, stated at the primitive owner level
-- `HasGradientWithinAt`.
theorem lower_tangent_plane_of_hasGradientWithinAt
    (hf_conv : ConvexOn ℝ Q f)
    (x : E) (hx : x ∈ Q) (g : E) (hgrad : HasGradientWithinAt f g Q x) (y : E) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ g (y - x) := by
  -- Restrict `f` to the segment from `x` to `y` so that the multivariate statement becomes
  -- a one-dimensional convex-derivative inequality on `Icc 0 1`.
  let seg : ℝ → E := AffineMap.lineMap x y
  have hmaps : Set.MapsTo seg (Set.Icc (0 : ℝ) 1) Q := hf_conv.1.mapsTo_lineMap hx hy
  have hseg_conv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (f ∘ seg) := by
    refine (hf_conv.comp_affineMap (AffineMap.lineMap x y)).subset ?_ (convex_Icc (0 : ℝ) 1)
    intro t ht
    exact hmaps ht
  -- Compose the gradient witness at `x = seg 0` with the segment parameterization.
  have hderiv :
      HasDerivWithinAt (f ∘ seg) (inner ℝ g (y - x)) (Set.Icc (0 : ℝ) 1) 0 := by
    simpa [seg] using
      hgrad.hasFDerivWithinAt.comp_hasDerivWithinAt_of_eq (0 : ℝ)
        AffineMap.hasDerivWithinAt_lineMap hmaps (AffineMap.lineMap_apply_zero x y).symm
  -- The derivative at the left endpoint is bounded by the secant slope, which is exactly the
  -- desired first-order lower support inequality after simplifying the slope on `[0,1]`.
  have hslope := hseg_conv.le_slope_of_hasDerivWithinAt (by simp) (by simp) zero_lt_one hderiv
  have hslope' : inner ℝ g (y - x) ≤ f y - f x := by
    simpa [seg, slope, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hslope
  linarith

/-- A convex function lies above the tangent plane determined by the canonical within-set gradient
at a feasible base point. -/
-- Proof sketch: specialize `lower_tangent_plane_of_hasGradientWithinAt` to the canonical witness
-- `gradientWithin f Q x`, using `DifferentiableWithinAt.hasGradientWithinAt`.
theorem lower_tangent_plane
    (hf_conv : ConvexOn ℝ Q f)
    (x : E) (hx : x ∈ Q) (hf_diff : DifferentiableWithinAt ℝ f Q x) (y : E) (hy : y ∈ Q) :
    f y ≥ f x + inner ℝ (gradientWithin f Q x) (y - x) := by
  -- Use the canonical within-set gradient as the explicit witness in the primitive theorem.
  exact lower_tangent_plane_of_hasGradientWithinAt hf_conv x hx (gradientWithin f Q x)
    hf_diff.hasGradientWithinAt y hy

end ConvexOn

/-- On a convex set, pointwise within-set differentiability makes the canonical owner predicate
`ConvexOn ℝ Q f` equivalent to the lower-tangent-plane inequality. -/
-- Proof sketch: the forward direction is `ConvexOn.lower_tangent_plane`; the reverse direction is
-- the converse first-order criterion for convexity on convex sets.
theorem convexOn_iff_lower_tangent_plane
    {Q : Set E} {f : E → ℝ}
    (hQ : Convex ℝ Q)
    (hf_diff : DifferentiableOn ℝ f Q) :
    ConvexOn ℝ Q f ↔
      ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
        f y ≥ f x + inner ℝ (gradientWithin f Q x) (y - x) := by
  constructor
  · intro hf_conv x hx y hy
    -- The forward implication is the canonical tangent-plane bound for convex functions.
    exact ConvexOn.lower_tangent_plane hf_conv x hx (hf_diff x hx) y hy
  · intro hlower
    -- For the converse, prove Jensen's inequality at the convex combination point `z`.
    refine ⟨hQ, ?_⟩
    intro x hx y hy a b ha hb hab
    let z : E := a • x + b • y
    have hz : z ∈ Q := hQ hx hy ha hb hab
    -- Apply the assumed lower-support inequality at the common base point `z`.
    have hx_plane : f x ≥ f z + inner ℝ (gradientWithin f Q z) (x - z) := hlower hz hx
    have hy_plane : f y ≥ f z + inner ℝ (gradientWithin f Q z) (y - z) := hlower hz hy
    -- The weighted displacements from `z` back to `x` and `y` cancel because `z = a • x + b • y`.
    have hdisp : a • (x - z) + b • (y - z) = 0 := by
      calc
        a • (x - z) + b • (y - z) = z - (a + b) • z := by
          simp [z, sub_eq_add_neg, smul_add, add_smul, add_comm, add_left_comm, add_assoc]
        _ = z - z := by simp [hab]
        _ = 0 := by simp
    have hcancel :
        a * inner ℝ (gradientWithin f Q z) (x - z) +
          b * inner ℝ (gradientWithin f Q z) (y - z) = 0 := by
      calc
        a * inner ℝ (gradientWithin f Q z) (x - z) +
            b * inner ℝ (gradientWithin f Q z) (y - z) =
            inner ℝ (gradientWithin f Q z) (a • (x - z) + b • (y - z)) := by
              rw [inner_add_right, inner_smul_right, inner_smul_right]
        _ = 0 := by simp [hdisp]
    have hx_bound :
        a * f z + a * inner ℝ (gradientWithin f Q z) (x - z) ≤ a * f x := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using
        mul_le_mul_of_nonneg_left hx_plane ha
    have hy_bound :
        b * f z + b * inner ℝ (gradientWithin f Q z) (y - z) ≤ b * f y := by
      simpa [mul_add, add_comm, add_left_comm, add_assoc] using
        mul_le_mul_of_nonneg_left hy_plane hb
    have hz_bound : f z ≤ a * f x + b * f y := by
      calc
        f z = (a + b) * f z := by rw [hab, one_mul]
        _ = a * f z + b * f z := by ring
        _ = (a * f z + b * f z) +
              (a * inner ℝ (gradientWithin f Q z) (x - z) +
                b * inner ℝ (gradientWithin f Q z) (y - z)) := by rw [hcancel, add_zero]
        _ = (a * f z + a * inner ℝ (gradientWithin f Q z) (x - z)) +
              (b * f z + b * inner ℝ (gradientWithin f Q z) (y - z)) := by ring
        _ ≤ a * f x + b * f y := add_le_add hx_bound hy_bound
    simpa [z] using hz_bound

/-- Definition 2.2: on a convex set `Q`, a `C¹` function is convex exactly when it lies above
each tangent plane determined by its within-set gradient. -/
-- Proof sketch: specialize the sharper owner bridge
-- `convexOn_iff_lower_tangent_plane` using the differentiability supplied by the `C¹` hypothesis.
theorem convexOn_iff_lower_tangent_plane_of_contDiffOn
    {Q : Set E} {f : E → ℝ}
    (hQ : Convex ℝ Q)
    (hf_C1 : ContDiffOn ℝ 1 f Q) :
    ConvexOn ℝ Q f ↔
      ∀ ⦃x⦄, x ∈ Q → ∀ ⦃y⦄, y ∈ Q →
        f y ≥ f x + inner ℝ (gradientWithin f Q x) (y - x) := by
  exact convexOn_iff_lower_tangent_plane hQ (hf_C1.differentiableOn (by simp))

end
