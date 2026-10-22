/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open scoped Convolution ENNReal MeasureTheory

/-- The total mass of the convolution is the product of the total masses whenever the right-hand
measure is `s`-finite. -/
theorem measure_conv_univ_eq_mul {n : ℕ} {μ ν : Measure (Fin n → ℝ)} [SFinite ν] :
    (μ ∗ ν) Set.univ = μ Set.univ * ν Set.univ := by
  rw [Measure.conv, Measure.map_apply measurable_add MeasurableSet.univ, Set.preimage_univ,
    show (Set.univ : Set ((Fin n → ℝ) × (Fin n → ℝ))) = Set.univ ×ˢ Set.univ by
      ext x
      simp]
  show (μ.prod ν) (Set.univ ×ˢ Set.univ) = μ Set.univ * ν Set.univ
  exact Measure.prod_prod Set.univ Set.univ

/-
Lemma 14.18 (measurability): for nonnegative measurable functions on `Fin n → ℝ`, the
convolution with respect to Lebesgue measure is measurable. This is exactly the canonical owner
theorem `MeasureTheory.measurable_lconvolution`, specialized in the textbook to `μ = volume`.
-/
recall MeasureTheory.measurable_lconvolution

/-
Lemma 14.18 (commutativity for functions): on `Fin n → ℝ`, additive convolution of nonnegative
functions with respect to Lebesgue measure is commutative. This is exactly the canonical owner
theorem `MeasureTheory.lconvolution_comm`, specialized to `μ = volume`.
-/
recall MeasureTheory.lconvolution_comm

section FunctionConvolution

variable {n : ℕ} {f g : (Fin n → ℝ) → ℝ≥0∞}

/-- Lemma 14.18: the Lebesgue integral of the convolution of two measurable nonnegative functions
on `ℝ^n` is the product of their Lebesgue integrals. -/
theorem lintegral_lconvolution_eq_lintegral_mul (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ x, (f ⋆ₗ g) x ∂(volume : Measure (Fin n → ℝ)) =
      (∫⁻ x, f x ∂(volume : Measure (Fin n → ℝ))) *
        ∫⁻ x, g x ∂(volume : Measure (Fin n → ℝ)) := by
  let μ : Measure (Fin n → ℝ) := volume
  change ∫⁻ x, (f ⋆ₗ[μ] g) x ∂μ = (∫⁻ x, f x ∂μ) * ∫⁻ x, g x ∂μ
  rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ,
    ← conv_withDensity_eq_lconvolution hf hg, measure_conv_univ_eq_mul]
  rw [withDensity_apply _ MeasurableSet.univ, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ, setLIntegral_univ]

end FunctionConvolution

/-
Lemma 14.18 (commutativity for measures): additive convolution of `s`-finite measures on
`Fin n → ℝ` is commutative. This is exactly the canonical owner theorem
`MeasureTheory.Measure.conv_comm`.
-/
recall MeasureTheory.Measure.conv_comm
