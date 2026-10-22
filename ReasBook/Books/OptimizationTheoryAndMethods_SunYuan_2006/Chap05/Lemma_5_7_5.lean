/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Extrema
import Mathlib.Analysis.Convex.Strong
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

-- Domain sampling for this refine pass:
-- * core/canonical owner `StrongConvexOn`
-- * canonical bridge `strongConvexOn_iff_convex`
-- * canonical first-order gradient interfaces `DifferentiableAt.hasGradientAt`
--   and `inner_gradient_left`
-- * project companion `Lemma_5_3_4.gradientNormSqLowerBound`
-- This theorem is source-facing. Its primitive data are the strong-convexity owner, the
-- minimizer, and the first-order differentiability needed to speak about `∇ f x`; higher-order
-- smoothness is derived/proof-route data and does not belong in the public statement.

omit [CompleteSpace E] in
/-- Helper for Chapter05 Lemma 5.7.5: a convex function on a real inner product space lies above
its affine tangent bound at every differentiability point. -/
lemma convex_tangent_le_of_hasFDerivAt
    {h : E → ℝ} (hConv : ConvexOn ℝ Set.univ h) {x y : E} {h' : E →L[ℝ] ℝ}
    (hx : HasFDerivAt h h' x) :
    h x + h' (y - x) ≤ h y := by
  -- Restrict the convex function to the segment from `x` to `y`.
  let g : ℝ → ℝ := h ∘ AffineMap.lineMap x y
  have hConv_g : ConvexOn ℝ Set.univ g := by
    simpa [g] using (hConv.comp_affineMap (AffineMap.lineMap x y))
  -- The derivative of the line restriction at `0` is the ambient derivative applied to `y - x`.
  have hg' : HasDerivAt g (h' (y - x)) 0 := by
    simpa [g] using
      (HasFDerivAt.comp_hasDerivAt_of_eq
        (x := 0) (y := x) (f := AffineMap.lineMap x y) hx
        (AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := 0))
        (AffineMap.lineMap_apply_zero x y).symm)
  -- Convexity compares this tangent slope with the secant slope between `0` and `1`.
  have hSlope :=
    hConv_g.deriv_le_slope (x := 0) (y := 1) (by simp) (by simp) zero_lt_one hg'.differentiableAt
  have hDeriv : deriv g 0 = h' (y - x) := by
    simpa [g] using hg'.deriv
  have hSlope' : h' (y - x) ≤ h y - h x := by
    calc
      h' (y - x) = deriv g 0 := hDeriv.symm
      _ ≤ slope g 0 1 := hSlope
      _ = h y - h x := by simp [g, slope_def_field]
  linarith

/-- Chapter05 Lemma 5.7.5, stated on a real inner product space: if `f : E → ℝ` is
strongly convex on `E` with modulus `m > 0`, differentiable at `x`, and `xStar` is a global
minimizer of `f`, then
`f x - f xStar ≤ (1 / m) * ‖∇ f x‖ ^ (2 : ℕ)` for every `x`. This is the coordinate-free form
of the source's `ℝ^n` statement. -/
theorem sub_globalMin_le_inv_mul_norm_gradient_sq_of_strongConvex
    (f : E → ℝ) (m : ℝ) (x xStar : E)
    (hm : 0 < m)
    (hStrong : StrongConvexOn Set.univ m f)
    (hx : DifferentiableAt ℝ f x)
    (hMin : IsMinOn f Set.univ xStar) :
    f x - f xStar ≤ (1 / m) * ‖∇ f x‖ ^ (2 : ℕ) := by
  -- Route correction: we encode the source strong-convexity line argument through the canonical
  -- convex perturbation `z ↦ f z - (m / 2) * ‖z‖²`, which packages the same quadratic control.
  have _ : f xStar ≤ f x := hMin (by simp : x ∈ Set.univ)
  have hConvShift : ConvexOn ℝ Set.univ (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)) := by
    simpa using (strongConvexOn_iff_convex (s := Set.univ) (m := m) (f := f)).1 hStrong
  have hNormSqDeriv :
      HasFDerivAt (fun z : E ↦ ‖z‖ ^ (2 : ℕ)) (2 • innerSL ℝ x) x := by
    simpa using (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  have hShiftDeriv :
      HasFDerivAt
        (fun z : E ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ))
        (fderiv ℝ f x - (m / 2) • (2 • innerSL ℝ x)) x := by
    exact hx.hasFDerivAt.sub (hNormSqDeriv.const_mul (m / 2))
  -- The tangent inequality for the shifted convex function yields the core quadratic estimate.
  have hShiftSupport :=
    convex_tangent_le_of_hasFDerivAt hConvShift (x := x) (y := xStar) hShiftDeriv
  have hDerivEval :
      (fderiv ℝ f x - (m / 2) • (2 • innerSL ℝ x)) (xStar - x) =
        inner ℝ (∇ f x) (xStar - x) - m * inner ℝ x (xStar - x) := by
    rw [sub_apply, smul_apply, inner_gradient_left]
    simp [innerSL_apply_apply]
    ring
  have hQuadratic :
      -(m / 2) * ‖x‖ ^ (2 : ℕ) - m * inner ℝ x (xStar - x) + (m / 2) * ‖xStar‖ ^ (2 : ℕ) =
        (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq, norm_sub_sq_real]
    ring
  have hCore :
      f x + inner ℝ (∇ f x) (xStar - x) + (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ f xStar := by
    have hShiftSupport' :
        f x - (m / 2) * ‖x‖ ^ (2 : ℕ) +
            (inner ℝ (∇ f x) (xStar - x) - m * inner ℝ x (xStar - x)) ≤
          f xStar - (m / 2) * ‖xStar‖ ^ (2 : ℕ) := by
      simpa [hDerivEval] using hShiftSupport
    linarith [hShiftSupport', hQuadratic]
  have hStrongBound :
      f x - f xStar ≤
        inner ℝ (∇ f x) (x - xStar) - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    have hTmp :
        f x - f xStar ≤
          -inner ℝ (∇ f x) (xStar - x) - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
      linarith [hCore]
    simpa [sub_eq_add_neg, inner_add_right, inner_neg_right] using hTmp
  -- Cauchy-Schwarz controls the pairing term, then a quadratic estimate absorbs the distance term.
  have hCauchy :
      inner ℝ (∇ f x) (x - xStar) ≤ ‖∇ f x‖ * ‖x - xStar‖ := by
    exact real_inner_le_norm _ _
  have hDistanceElim :
      f x - f xStar ≤
        ‖∇ f x‖ * ‖x - xStar‖ - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    linarith [hStrongBound, hCauchy]
  have hQuadraticOptHalf :
      ‖∇ f x‖ * ‖x - xStar‖ - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        (1 / (2 * m)) * ‖∇ f x‖ ^ (2 : ℕ) := by
    have hm2 : 0 < 2 * m := by positivity
    have hMul :
        (‖∇ f x‖ * ‖x - xStar‖ - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ)) * (2 * m) ≤
          ‖∇ f x‖ ^ (2 : ℕ) := by
      nlinarith [sq_nonneg (‖∇ f x‖ - m * ‖x - xStar‖)]
    have hDiv :
        ‖∇ f x‖ * ‖x - xStar‖ - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤
          ‖∇ f x‖ ^ (2 : ℕ) / (2 * m) := by
      exact (le_div_iff₀ hm2).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hMul)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hDiv
  have hHalfLe :
      (1 / (2 * m)) * ‖∇ f x‖ ^ (2 : ℕ) ≤
        (1 / m) * ‖∇ f x‖ ^ (2 : ℕ) := by
    have hCoeff : 1 / (2 * m) ≤ 1 / m := by
      have hMul : m ≤ 2 * m := by nlinarith
      exact one_div_le_one_div_of_le hm hMul
    gcongr
  exact hDistanceElim.trans (hQuadraticOptHalf.trans hHalfLe)
