/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_7.WellPosed
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1.Blur2D
public import Mathlib.Analysis.Fourier.Convolution

public section

noncomputable section

open scoped Convolution FourierTransform

/-!
Remark 5.1. The source discusses the atmospheric-optics point spread function
`k = |𝓕⁻¹ {A * exp (Complex.I * φ)}|^2` and its power spectrum
`|𝓕 {k}|^2`, then observes that zeros in the corresponding frequency response
remove Fourier modes from the blurred image and thereby lead to nonuniqueness in
the inverse problem. This file keeps that Fourier/power-spectrum mechanism as
the source-facing Chapter 5 API, and records the Definition 2.7
operator-theoretic consequence only as a bridge.
-/

namespace Blur2D

/-- The Euclidean coordinate pairing on `ℝ × ℝ`, written explicitly so the
continuous Fourier-side Chapter 5 API remains available on product
coordinates. -/
def coordinatePairing : (ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ) →ₗ[ℝ] ℝ where
  toFun := fun p ↦
    { toFun := fun ξ ↦ p.1 * ξ.1 + p.2 * ξ.2
      map_add' := by
        rintro ⟨ξ₁, ξ₂⟩ ⟨η₁, η₂⟩
        change p.1 * (ξ₁ + η₁) + p.2 * (ξ₂ + η₂) =
          (p.1 * ξ₁ + p.2 * ξ₂) + (p.1 * η₁ + p.2 * η₂)
        rw [mul_add, mul_add]
        ac_rfl
      map_smul' := by
        intro a ξ
        calc
          p.1 * (a * ξ.1) + p.2 * (a * ξ.2)
              = (p.1 * a) * ξ.1 + (p.2 * a) * ξ.2 := by
                  rw [mul_assoc, mul_assoc]
          _ = (a * p.1) * ξ.1 + (a * p.2) * ξ.2 := by
                rw [mul_comm p.1 a, mul_comm p.2 a]
          _ = a * (p.1 * ξ.1) + a * (p.2 * ξ.2) := by
                rw [← mul_assoc, ← mul_assoc]
          _ = a * (p.1 * ξ.1 + p.2 * ξ.2) := by
                rw [mul_add] }
  map_add' := by
    intro p q
    apply LinearMap.ext
    rintro ⟨x₁, x₂⟩
    change (p.1 + q.1) * x₁ + (p.2 + q.2) * x₂ =
      (p.1 * x₁ + p.2 * x₂) + (q.1 * x₁ + q.2 * x₂)
    rw [add_mul, add_mul]
    ac_rfl
  map_smul' := by
    intro a p
    apply LinearMap.ext
    rintro ⟨x₁, x₂⟩
    calc
      (a * p.1) * x₁ + (a * p.2) * x₂
          = a * (p.1 * x₁) + a * (p.2 * x₂) := by
              rw [← mul_assoc, ← mul_assoc]
      _ = a * (p.1 * x₁ + p.2 * x₂) := by
            rw [mul_add]

/-- The continuous two-dimensional Fourier transform on `ℝ × ℝ`, written with
the explicit coordinate pairing used in Remark 5.1. -/
abbrev fourierTransform2D (f : (ℝ × ℝ) → ℂ) : (ℝ × ℝ) → ℂ :=
  VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume coordinatePairing f

/-- Remark 5.1. The frequency response of the real-valued translation-invariant
point spread function `κ`, viewed through the complex Fourier transform. -/
abbrev frequencyResponse (κ : (ℝ × ℝ) → ℝ) : (ℝ × ℝ) → ℂ :=
  fourierTransform2D fun p ↦ (κ p : ℂ)

/-- Remark 5.1. The power spectrum of the real-valued point spread function `κ`
is the squared modulus of its frequency response. -/
def powerSpectrum (κ : (ℝ × ℝ) → ℝ) : (ℝ × ℝ) → ℝ :=
  fun ξ ↦ Complex.normSq (frequencyResponse κ ξ)

/-- Remark 5.1. The power spectrum vanishes exactly where the frequency
response vanishes. -/
@[simp] theorem powerSpectrum_eq_zero_iff {κ : (ℝ × ℝ) → ℝ} {ξ : ℝ × ℝ} :
    powerSpectrum κ ξ = 0 ↔ frequencyResponse κ ξ = 0 := by
  simp [powerSpectrum]

/-- Helper for Remark 5.1.1-extra-1: `coordinatePairing` is additive in its
first argument, so the Fourier phase splits over translated variables. -/
lemma coordinatePairing_add_left (p q ξ : ℝ × ℝ) :
    coordinatePairing (p + q) ξ = coordinatePairing p ξ + coordinatePairing q ξ := by
  -- Apply linearity in the first argument to the evaluation point `ξ`.
  have hAdd :=
    congrArg (fun L : (ℝ × ℝ) →ₗ[ℝ] ℝ => L ξ) (coordinatePairing.map_add p q)
  exact hAdd

/-- Helper for Remark 5.1.1-extra-1: the explicit bilinear phase map is
continuous on `((ℝ × ℝ) × (ℝ × ℝ))`. -/
lemma coordinatePairing_continuous :
    Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ coordinatePairing p.1 p.2) := by
  -- Expand to coordinate projections and use continuity of addition and multiplication.
  have h₁ : Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ p.1.1 * p.2.1) :=
    continuous_fst.fst.mul continuous_snd.fst
  have h₂ : Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ p.1.2 * p.2.2) :=
    continuous_fst.snd.mul continuous_snd.snd
  change Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ p.1.1 * p.2.1 + p.1.2 * p.2.2)
  change Continuous
    (((fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ p.1.1 * p.2.1) +
      fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ p.1.2 * p.2.2))
  exact h₁.add h₂

/-- Helper for Remark 5.1.1-extra-1: the Fourier transform of the convolution
can be rewritten as a symmetric double integral using `coordinatePairing`. -/
lemma fourierTransform2D_convolution_eq_integral {f g : (ℝ × ℝ) → ℂ}
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) (ξ : ℝ × ℝ) :
    fourierTransform2D (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ =
      ∫ y, ∫ x, 𝐞 (-coordinatePairing (y + x) ξ) • (f x * g y) := by
  calc
    _ = fourierTransform2D (g ⋆[(ContinuousLinearMap.mul ℂ ℂ).flip] f) ξ := by
          rw [MeasureTheory.convolution_flip]
    _ = ∫ x, 𝐞 (-coordinatePairing x ξ) • ∫ y, f (x - y) * g y := by
          rfl
    _ = ∫ x, ∫ y, 𝐞 (-coordinatePairing x ξ) • (f (x - y) * g y) := by
          congr
          ext x
          simpa [Circle.smul_def] using
            (MeasureTheory.integral_const_mul (↑(𝐞 (-coordinatePairing x ξ)) : ℂ)
              (fun y : ℝ × ℝ ↦ f (x - y) * g y)).symm
    _ = ∫ y, ∫ x, 𝐞 (-coordinatePairing x ξ) • (f (x - y) * g y) := by
          refine MeasureTheory.integral_integral_swap ?_
          have hMul := hg.convolution_integrand (ContinuousLinearMap.mul ℂ ℂ).flip hf
          have hPhaseCont :
              Continuous (fun p : ((ℝ × ℝ) × (ℝ × ℝ)) ↦ 𝐞 (-coordinatePairing p.1 ξ)) := by
            exact
              Real.continuous_fourierChar.comp
                ((coordinatePairing_continuous.comp (continuous_fst.prodMk continuous_const)).neg)
          refine hMul.mono ?_ ?_
          · exact hPhaseCont.aestronglyMeasurable.smul hMul.aestronglyMeasurable
          · filter_upwards with ⟨x, y⟩ using by
              simp [mul_comm]
    _ = ∫ y, ∫ x, 𝐞 (-coordinatePairing (y + x) ξ) • (f x * g y) := by
          congr
          ext y
          -- Translate the inner integral so the source term depends on `x` instead of `x - y`.
          have hTranslate :=
            MeasureTheory.integral_sub_right_eq_self
              (fun x : ℝ × ℝ ↦ 𝐞 (-coordinatePairing (y + x) ξ) • (f x * g y)) y
              (μ := MeasureTheory.volume)
          simpa [sub_eq_add_neg, add_assoc] using hTranslate

/-- Helper for Remark 5.1.1-extra-1: convolution becomes pointwise
multiplication after applying `fourierTransform2D`. -/
lemma fourierTransform2D_convolution_eq_mul {f g : (ℝ × ℝ) → ℂ}
    (hf : MeasureTheory.Integrable f) (hg : MeasureTheory.Integrable g) (ξ : ℝ × ℝ) :
    fourierTransform2D (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) ξ =
      fourierTransform2D f ξ * fourierTransform2D g ξ := by
  -- Route correction: the product type here does not expose the standard inner-product
  -- Fourier API, so we factor the phase directly in the explicit `coordinatePairing` model.
  calc
    _ = ∫ y, ∫ x, 𝐞 (-coordinatePairing (y + x) ξ) • (f x * g y) :=
      fourierTransform2D_convolution_eq_integral hf hg ξ
    _ = ∫ y, ∫ x, (𝐞 (-coordinatePairing x ξ) • f x) * (𝐞 (-coordinatePairing y ξ) • g y) := by
          congr
          ext y
          congr
          ext x
          rw [coordinatePairing_add_left]
          simp [Circle.smul_def, AddChar.map_add_eq_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = ∫ y, (∫ x, 𝐞 (-coordinatePairing x ξ) • f x) * (𝐞 (-coordinatePairing y ξ) • g y) := by
          congr
          ext y
          rw [MeasureTheory.integral_mul_const]
    _ = (∫ x, 𝐞 (-coordinatePairing x ξ) • f x) * (∫ y, 𝐞 (-coordinatePairing y ξ) • g y) := by
          rw [MeasureTheory.integral_const_mul]
    _ = fourierTransform2D f ξ * fourierTransform2D g ξ := by
          simp [fourierTransform2D, VectorFourier.fourierIntegral]

/-- Remark 5.1.1-extra-1. If the Fourier transform of `f` is supported in the zero set of
the frequency response of `κ`, then the blurred image has identically zero
Fourier spectrum. This is the source-facing Fourier-side loss-of-information
mechanism behind the remark. -/
theorem blurredSpectrum_eq_zero_of_frequencyResponse_support
    {κ : (ℝ × ℝ) → ℝ} {f : (ℝ × ℝ) → ℂ}
    (hκ : MeasureTheory.Integrable fun p ↦ (κ p : ℂ))
    (hf : MeasureTheory.Integrable f)
    (hSupport : ∀ ξ : ℝ × ℝ, frequencyResponse κ ξ ≠ 0 → fourierTransform2D f ξ = 0) :
    ∀ ξ : ℝ × ℝ,
      fourierTransform2D (f ⋆[ContinuousLinearMap.mul ℂ ℂ] fun p ↦ (κ p : ℂ)) ξ = 0 := by
  intro ξ
  -- Rewrite the blurred spectrum as the product of the source spectrum and the PSF response.
  have hConv :
      fourierTransform2D (f ⋆[ContinuousLinearMap.mul ℂ ℂ] fun p ↦ (κ p : ℂ)) ξ =
        fourierTransform2D f ξ * frequencyResponse κ ξ := by
    simpa [frequencyResponse] using
      (fourierTransform2D_convolution_eq_mul
        (f := f) (g := fun p ↦ (κ p : ℂ)) hf hκ ξ)
  rw [hConv]
  by_cases hresp : frequencyResponse κ ξ = 0
  · -- If the response vanishes, the product is zero immediately.
    simp [hresp]
  · -- Otherwise the support hypothesis forces the source Fourier mode to vanish.
    rw [hSupport ξ hresp]
    simp

/-- Remark 5.1. The same Fourier-mode loss can be stated in terms of the power
spectrum `|𝓕 {κ}|^2`: if `𝓕 f` is supported where the power spectrum vanishes,
then the blurred image has zero Fourier spectrum. -/
theorem blurredSpectrum_eq_zero_of_powerSpectrum_support
    {κ : (ℝ × ℝ) → ℝ} {f : (ℝ × ℝ) → ℂ}
    (hκ : MeasureTheory.Integrable fun p ↦ (κ p : ℂ))
    (hf : MeasureTheory.Integrable f)
    (hSupport : ∀ ξ : ℝ × ℝ, powerSpectrum κ ξ ≠ 0 → fourierTransform2D f ξ = 0) :
    ∀ ξ : ℝ × ℝ,
      fourierTransform2D (f ⋆[ContinuousLinearMap.mul ℂ ℂ] fun p ↦ (κ p : ℂ)) ξ = 0 := by
  refine blurredSpectrum_eq_zero_of_frequencyResponse_support hκ hf ?_
  intro ξ hξ
  exact hSupport ξ (by simpa [powerSpectrum_eq_zero_iff] using hξ)

/-- Remark 5.1. A nonzero null-space image gives two distinct reconstructions
for the same blurred datum, so Definition 2.7 clause `(ii)` fails. -/
theorem exists_distinct_preimages_of_nonzeroNullImage
    {κ : (ℝ × ℝ) → ℝ}
    (hNull :
      ∃ f : (ℝ × ℝ) → ℝ, f ≠ 0 ∧ operator (translationInvariantKernel κ) f = 0) :
    ∃ f₁ f₂ : (ℝ × ℝ) → ℝ,
      f₁ ≠ f₂ ∧
        operator (translationInvariantKernel κ) f₁ =
          operator (translationInvariantKernel κ) f₂ := by
  rcases hNull with ⟨f, hf_ne, hf_zero⟩
  refine ⟨f, 0, hf_ne, ?_⟩
  have hZero : operator (translationInvariantKernel κ) (0 : (ℝ × ℝ) → ℝ) = 0 := by
    funext p
    rw [operator_apply]
    simp
  simpa [hZero] using hf_zero

/-- Remark 5.1. A nontrivial null space prevents injectivity of the
translation-invariant blur operator. -/
theorem not_injective_of_nonzeroNullImage
    {κ : (ℝ × ℝ) → ℝ}
    (hNull :
      ∃ f : (ℝ × ℝ) → ℝ, f ≠ 0 ∧ operator (translationInvariantKernel κ) f = 0) :
    ¬ Function.Injective (operator (translationInvariantKernel κ)) := by
  intro hInj
  rcases exists_distinct_preimages_of_nonzeroNullImage hNull with ⟨f₁, f₂, hne, hEq⟩
  exact hne (hInj hEq)

/-- Remark 5.1. Once the translation-invariant blur operator has a nontrivial
null space, the inverse problem fails Definition 2.7 and is ill-posed. -/
theorem illPosed_of_nonzeroNullImage
    {κ : (ℝ × ℝ) → ℝ}
    (hNull :
      ∃ f : (ℝ × ℝ) → ℝ, f ≠ 0 ∧ operator (translationInvariantKernel κ) f = 0) :
    OperatorEquation.illPosed (operator (translationInvariantKernel κ)) := by
  intro hWellPosed
  exact not_injective_of_nonzeroNullImage hNull hWellPosed.injective

end Blur2D
