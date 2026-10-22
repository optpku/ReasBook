/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped MeasureTheory

/- Definition 14.17 (1): For nonnegative maps on the coordinate model `Fin n → ℝ` of `ℝ^n`, the
textbook convolution `(f * g) (x) = ∫⁻ y, f y * g (x - y)` is the canonical additive
`ENNReal`-valued convolution `MeasureTheory.lconvolution` with respect to Lebesgue measure. -/
recall lconvolution

-- Proof sketch: unfold `MeasureTheory.lconvolution`; on the additive commutative group
-- `Fin n → ℝ`, rewrite the canonical integrand `g (-y + x)` as `g (x - y)`.
/-- The additive `ENNReal` convolution on `Fin n → ℝ` is given by the textbook formula
`(f * g) (x) = ∫⁻ y, f y * g (x - y)`. -/
theorem lconvolution_apply_eq_lintegral_sub
    {n : ℕ} (f g : (Fin n → ℝ) → ENNReal) (x : Fin n → ℝ) :
    (f ⋆ₗ g) x = ∫⁻ y, f y * g (x - y) := by
  simpa [sub_eq_add_neg, add_comm] using
    (lconvolution_def : (f ⋆ₗ g) x = ∫⁻ y, f y * g (-y + x))

/- Definition 14.17 (2): For finite measures on the coordinate model `Fin n → ℝ` of `ℝ^n`, the
textbook convolution is the canonical additive measure convolution `MeasureTheory.Measure.conv`;
the result is again finite by the standard finiteness instance for measure convolution. -/
recall Measure.conv

-- Proof sketch: rewrite `(μ ∗ ν) (Set.Iic x)` as the lower integral of the indicator of
-- `Set.Iic x`, then apply the owner theorem `MeasureTheory.Measure.lintegral_conv`.
/-- The additive convolution of finite measures on `Fin n → ℝ` has the textbook lower-orthant
formula on sets `(-∞, x] = Set.Iic x`. -/
theorem conv_apply_Iic_eq_lintegral_indicator
    {n : ℕ} (μ ν : Measure (Fin n → ℝ)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (x : Fin n → ℝ) :
    (μ ∗ ν) (Set.Iic x) =
      ∫⁻ u, ∫⁻ v, (Set.Iic x).indicator (fun _ ↦ (1 : ENNReal)) (u + v) ∂ν ∂μ := by
  let φ : (Fin n → ℝ) → ENNReal := (Set.Iic x).indicator (fun _ ↦ (1 : ENNReal))
  calc
    (μ ∗ ν) (Set.Iic x)
        = ∫⁻ z, φ z ∂(μ ∗ ν) := by
            symm
            exact lintegral_indicator_one measurableSet_Iic
    _ = ∫⁻ u, ∫⁻ v, φ (u + v) ∂ν ∂μ := by
          simpa using
            (Measure.lintegral_conv
              (measurable_const.indicator measurableSet_Iic) :
                ∫⁻ z, φ z ∂(μ ∗ ν) =
                  ∫⁻ u, ∫⁻ v, φ (u + v) ∂ν ∂μ)
