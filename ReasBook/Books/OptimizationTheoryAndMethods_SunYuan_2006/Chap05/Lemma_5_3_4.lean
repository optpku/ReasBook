/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Assumption_5_3_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_13
import Mathlib.Analysis.Calculus.Gradient.Basic

noncomputable section

section Chapter05Lemma534

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling: the source statement is the ambient "for all vectors `x`" inequality, and the
-- canonical owner for that route in this project is global strong convexity on `Set.univ`.
-- The Chapter 5 level-set/Hessian package is proof-route data for later corollaries, not the main
-- labeled statement surface here.

/-- Helper for Chapter05 Lemma 5.3.4: a convex function on the ambient space lies above the
affine tangent determined by any Fréchet derivative at a point. -/
lemma convexOnUniv_tangent_le_of_hasFDerivAt
    {h : Point → ℝ} (hConv : ConvexOn ℝ Set.univ h) {x y : Point} {h' : Point →L[ℝ] ℝ}
    (hx : HasFDerivAt h h' x) :
    h x + h' (y - x) ≤ h y := by
  let g : ℝ → ℝ := h ∘ AffineMap.lineMap x y
  have hgConv : ConvexOn ℝ Set.univ g := by
    -- Restrict the ambient convex function to the line through `x` and `y`.
    simpa [g] using hConv.comp_affineMap (AffineMap.lineMap x y)
  have hderivG : HasDerivAt g (h' (y - x)) 0 := by
    -- The line derivative at `0` is exactly the directional derivative in direction `y - x`.
    simpa [g] using
      (hx.comp_hasDerivAt_of_eq
        (hf := AffineMap.hasDerivAt_lineMap (a := x) (b := y) (x := (0 : ℝ)))
        (hy := (AffineMap.lineMap_apply_zero x y).symm))
  have hslope : h' (y - x) ≤ h y - h x := by
    -- Convexity bounds the directional derivative by the secant slope between `0` and `1`.
    have hSlope := hgConv.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hderivG
    simpa [g, slope_def_field] using hSlope
  linarith

/-- Helper for Chapter05 Lemma 5.3.4: strong convexity on `Set.univ` yields the quadratic
first-order support inequality at every differentiability point. -/
lemma strongConvexOnUniv_supportQuadratic_le
    (f : Point → ℝ) (m : ℝ) {x y : Point}
    (hStrong : StrongConvexOn Set.univ m f) (hx : DifferentiableAt ℝ f x) :
    f x + inner ℝ (gradient f x) (y - x) + (m / 2) * ‖x - y‖ ^ (2 : ℕ) ≤ f y := by
  let g : Point → ℝ := fun z ↦ f z - (m / 2) * ‖z‖ ^ (2 : ℕ)
  have hgConv : ConvexOn ℝ Set.univ g := by
    -- Route correction: pass to the shifted function so ordinary convexity exposes the support
    -- inequality matched to the source proof.
    simpa [g] using (strongConvexOn_iff_convex (s := Set.univ) (m := m) (f := f)).1 hStrong
  have hGrad : HasGradientAt f (gradient f x) x := hx.hasGradientAt
  have hgDeriv :
      HasFDerivAt g (InnerProductSpace.toDual ℝ Point (gradient f x - m • x)) x := by
    -- Differentiate the quadratic shift once, then keep the main proof at the support level.
    simpa [g] using (hasGradientAt_sub_half_mul_norm_sq (c := m) hGrad).hasFDerivAt
  have hSupport :
      g x + InnerProductSpace.toDual ℝ Point (gradient f x - m • x) (y - x) ≤ g y :=
    convexOnUniv_tangent_le_of_hasFDerivAt (x := x) (y := y) hgConv hgDeriv
  have hFDeriv : fderiv ℝ f x = InnerProductSpace.toDual ℝ Point (gradient f x) := by
    -- The gradient at `x` is exactly the Riesz-dual of the Fréchet derivative there.
    simpa using hGrad.hasFDerivAt.fderiv
  have hFDerivY : (fderiv ℝ f x) y = inner ℝ (gradient f x) y := by
    rw [hFDeriv, InnerProductSpace.toDual_apply_apply]
  have hFDerivX : (fderiv ℝ f x) x = inner ℝ (gradient f x) x := by
    rw [hFDeriv, InnerProductSpace.toDual_apply_apply]
  have hShiftLeRaw :
      f x - (m / 2) * ‖x‖ ^ (2 : ℕ) +
          ((fderiv ℝ f x) y - (fderiv ℝ f x) x - m * inner ℝ x (y - x)) ≤
        f y - (m / 2) * ‖y‖ ^ (2 : ℕ) := by
    -- This is the direct unfolded form produced by the tangent lemma and linearity of the dual map.
    simpa [g, InnerProductSpace.toDual_apply_apply] using hSupport
  have hInnerExpand :
      inner ℝ (gradient f x - m • x) (y - x) =
        (fderiv ℝ f x) y - (fderiv ℝ f x) x - m * inner ℝ x (y - x) := by
    -- Rewrite the derivative evaluations through the gradient, then expand the inner products.
    calc
      inner ℝ (gradient f x - m • x) (y - x)
          = inner ℝ (gradient f x) (y - x) - inner ℝ (m • x) (y - x) := by
              rw [inner_sub_left]
      _ = inner ℝ (gradient f x) (y - x) - m * inner ℝ x (y - x) := by
            rw [real_inner_smul_left]
      _ = (inner ℝ (gradient f x) y - inner ℝ (gradient f x) x) - m * inner ℝ x (y - x) := by
            rw [inner_sub_right]
      _ = (fderiv ℝ f x) y - (fderiv ℝ f x) x - m * inner ℝ x (y - x) := by
            rw [← hFDerivY, ← hFDerivX]
  have hShiftLe :
      f x - (m / 2) * ‖x‖ ^ (2 : ℕ) +
          inner ℝ (gradient f x - m • x) (y - x) ≤
        f y - (m / 2) * ‖y‖ ^ (2 : ℕ) := by
    -- Unfold only the shifted function before translating the dual action into an inner product.
    rw [hInnerExpand]
    exact hShiftLeRaw
  have hShift :
      f y - (m / 2) * ‖y‖ ^ (2 : ℕ) ≥
        f x - (m / 2) * ‖x‖ ^ (2 : ℕ) + inner ℝ (gradient f x - m • x) (y - x) := by
    -- Rewrite the dual pairing as the inner product form used by the Chapter 1 shift lemma.
    simpa [ge_iff_le] using hShiftLe
  have hFinal :=
    (sub_half_mul_norm_sq_supporting_iff
      (c := m) (fx := f x) (fy := f y) (x := x) (y := y) (g := gradient f x)).mp hShift
  simpa [norm_sub_rev] using hFinal

/-- Helper for Chapter05 Lemma 5.3.4: the scalar quadratic term
`a * t - (m / 2) * t^2` is bounded by `(1 / (2 * m)) * a^2` when `m > 0`. -/
lemma youngMulSubHalfMulSq_le_halfInvMulSq
    {a t m : ℝ} (hm : 0 < m) :
    a * t - (m / 2) * t ^ (2 : ℕ) ≤ (1 / (2 * m)) * a ^ (2 : ℕ) := by
  have hSq : 0 ≤ (m / 2) * (t - a / m) ^ (2 : ℕ) := by
    -- Complete the square once so the remaining estimate is purely algebraic.
    positivity
  have hExpand :
      (m / 2) * (t - a / m) ^ (2 : ℕ) =
        (m / 2) * t ^ (2 : ℕ) - a * t + (1 / (2 * m)) * a ^ (2 : ℕ) := by
    field_simp [pow_two, hm.ne']
    ring
  nlinarith [hSq, hExpand]

/-- Chapter05 Lemma 5.3.4: if `f : ℝ^n → ℝ` is strongly convex on the ambient space with modulus
`m > 0`, `f xStar` is the minimum value of `f`, and `f` is differentiable at `x`, then
`‖gradient f x‖ ^ (2 : ℕ) ≥ m * (f x - f xStar)`. -/
theorem gradientNormSqLowerBound
    (f : Point → ℝ) (x xStar : Point)
    (m : ℝ)
    (hm : 0 < m)
    (hStrong : StrongConvexOn Set.univ m f)
    (hx : DifferentiableAt ℝ f x)
    (hMin : IsMinOn f Set.univ xStar) :
    m * (f x - f xStar) ≤ ‖gradient f x‖ ^ (2 : ℕ) := by
  have hMinValue : f xStar ≤ f x := (isMinOn_iff.mp hMin) x (by simp)
  have hGapNonneg : 0 ≤ f x - f xStar := sub_nonneg.mpr hMinValue
  have hSupport :=
    strongConvexOnUniv_supportQuadratic_le (x := x) (y := xStar) f m hStrong hx
  have hSub : xStar - x = -(x - xStar) := by
    abel_nf
  have hSupport' :
      f x - inner ℝ (gradient f x) (x - xStar) + (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤ f xStar := by
    -- Normalize the support inequality to the `(x - xStar)` direction used in the closing step.
    rw [hSub, inner_neg_right] at hSupport
    linarith
  have hGap :
      f x - f xStar ≤
        inner ℝ (gradient f x) (x - xStar) - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) := by
    -- Specializing the support inequality at the minimizer exposes the objective gap.
    linarith [hSupport']
  have hInner :
      inner ℝ (gradient f x) (x - xStar) ≤ ‖gradient f x‖ * ‖x - xStar‖ := by
    -- Cauchy-Schwarz isolates the distance term from the gradient norm.
    exact real_inner_le_norm _ _
  have hYoung :
      ‖gradient f x‖ * ‖x - xStar‖ - (m / 2) * ‖x - xStar‖ ^ (2 : ℕ) ≤
        (1 / (2 * m)) * ‖gradient f x‖ ^ (2 : ℕ) :=
    youngMulSubHalfMulSq_le_halfInvMulSq (a := ‖gradient f x‖) (t := ‖x - xStar‖) hm
  have hEstimate :
      f x - f xStar ≤ (1 / (2 * m)) * ‖gradient f x‖ ^ (2 : ℕ) := by
    -- The gap is bounded by the sharp quadratic envelope in the gradient norm.
    linarith
  have hScaled :
      m * (f x - f xStar) ≤ m * ((1 / (2 * m)) * ‖gradient f x‖ ^ (2 : ℕ)) := by
    exact mul_le_mul_of_nonneg_left hEstimate hm.le
  have hGradSqNonneg : 0 ≤ ‖gradient f x‖ ^ (2 : ℕ) := by
    positivity
  calc
    m * (f x - f xStar) ≤ m * ((1 / (2 * m)) * ‖gradient f x‖ ^ (2 : ℕ)) := hScaled
    _ = (1 / 2 : ℝ) * ‖gradient f x‖ ^ (2 : ℕ) := by
      field_simp [hm.ne']
    _ ≤ ‖gradient f x‖ ^ (2 : ℕ) := by
      nlinarith [hGradSqNonneg, hGapNonneg]

end Chapter05Lemma534
