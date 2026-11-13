/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.RefinedEndpoint.Period1024
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace ConsensusADMM.RefinedEndpoint.Certificate

open Period1024
open scoped RealInnerProductSpace

theorem phase_add (h : Coordinate) (i j : Phase) :
    phase h (i + j) = phase h i * phase h j := by
  simp only [phase, mul_add, map_add, AddCircle.toCircle_add, Circle.coe_mul]

/-- The common character reduces every Gram product to one cyclic displacement. -/
theorem phase_mul_star (h : Coordinate) (i j : Phase) :
    phase h j * star (phase h i) = phase h (j - i) := by
  have hunit : phase h i * star (phase h i) = 1 := by
    rw [Complex.star_def, Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, phase_norm, one_pow, Complex.ofReal_one]
  calc
    phase h j * star (phase h i) =
        (phase h (j - i) * phase h i) * star (phase h i) := by
      rw [← phase_add, sub_add_cancel]
    _ = phase h (j - i) := by rw [mul_assoc, hunit, mul_one]

private theorem normalized_product_re (u v a b : ℂ) (n : ℝ) :
    (v * ((n : ℂ) * b) * star (u * ((n : ℂ) * a))).re =
      n ^ 2 * ((v * star u) * (b * star a)).re := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

/-- The actual normalized Fourier Gram formula. All irrational normalization
factors cancel before any numerical enclosure is used. -/
theorem normalized_fourier_inner (a b : Coordinate → ℂ) (i j : Phase) :
    inner ℝ (fourierFamily phase (fun h ↦ (normalization h : ℂ) * a h) i)
      (fourierFamily phase (fun h ↦ (normalization h : ℂ) * b h) j) =
      ∑ h, (Period1024.multiplicity h / ADMM.RefinedEndpoint.Data.period) *
        (phase h (j - i) * (b h * star (a h))).re := by
  rw [fourierFamily_inner]
  apply Finset.sum_congr rfl
  intro h _
  rw [normalized_product_re, normalization_sq, phase_mul_star]

theorem eta_inner (i j : Phase) :
    inner ℝ (eta i) (eta j) =
      ∑ h, (Period1024.multiplicity h / ADMM.RefinedEndpoint.Data.period) *
        (phase h (j - i) * (etaCoefficient h * star (etaCoefficient h))).re := by
  exact normalized_fourier_inner etaCoefficient etaCoefficient i j

theorem scaledMultiplier_inner (i j : Phase) :
    inner ℝ (scaledMultiplier i) (scaledMultiplier j) =
      ∑ h, (Period1024.multiplicity h / ADMM.RefinedEndpoint.Data.period) *
        (phase h (j - i) *
          (multiplierCoefficient h * star (multiplierCoefficient h))).re := by
  exact normalized_fourier_inner multiplierCoefficient multiplierCoefficient i j

theorem eta_scaledMultiplier_inner (i j : Phase) :
    inner ℝ (eta i) (scaledMultiplier j) =
      ∑ h, (Period1024.multiplicity h / ADMM.RefinedEndpoint.Data.period) *
        (phase h (j - i) *
          (multiplierCoefficient h * star (etaCoefficient h))).re := by
  exact normalized_fourier_inner etaCoefficient multiplierCoefficient i j

@[simp] theorem etaCoefficient_re (h : Coordinate) :
    (etaCoefficient h).re =
      ((factor h).etaRe : ℝ) / ADMM.RefinedEndpoint.Data.denominator := by
  simp [etaCoefficient]

@[simp] theorem etaCoefficient_im (h : Coordinate) :
    (etaCoefficient h).im =
      ((factor h).etaIm : ℝ) / ADMM.RefinedEndpoint.Data.denominator := by
  simp [etaCoefficient]

@[simp] theorem multiplierCoefficient_re (h : Coordinate) :
    (multiplierCoefficient h).re = ((factor h).wRe : ℝ) / ADMM.RefinedEndpoint.Data.denominator := by
  simp [multiplierCoefficient]

@[simp] theorem multiplierCoefficient_im (h : Coordinate) :
    (multiplierCoefficient h).im = ((factor h).wIm : ℝ) / ADMM.RefinedEndpoint.Data.denominator := by
  simp [multiplierCoefficient]

/-- The real part of a complex Gram product, with the plus-sine convention
used by the original rational certificate. -/
theorem gram_product_re (u a b : ℂ) :
    (u * (b * star a)).re =
      u.re * (b.re * a.re + b.im * a.im) +
        u.im * (b.re * a.im - b.im * a.re) := by
  simp [Complex.mul_re, Complex.mul_im]
  ring

noncomputable def rationalModeMultiplicity (h : Coordinate) : ℚ :=
  if mode h = ADMM.RefinedEndpoint.Data.period / 2 then 1 else 2

/-- Common rational normalization after the square roots have cancelled. -/
noncomputable def modeWeight (h : Coordinate) : ℚ :=
  rationalModeMultiplicity h / ADMM.RefinedEndpoint.Data.period /
    (ADMM.RefinedEndpoint.Data.denominator : ℚ) ^ 2

noncomputable def firstGramCoefficient (h : Coordinate) : ℚ :=
  modeWeight h * (((factor h).etaRe : ℚ) ^ 2 + ((factor h).etaIm : ℚ) ^ 2)

noncomputable def secondGramCoefficient (h : Coordinate) : ℚ :=
  modeWeight h * (((factor h).wRe : ℚ) ^ 2 + ((factor h).wIm : ℚ) ^ 2)

noncomputable def crossRealCoefficient (h : Coordinate) : ℚ :=
  modeWeight h * ((factor h).etaRe * (factor h).wRe + (factor h).etaIm * (factor h).wIm)

noncomputable def crossSineCoefficient (h : Coordinate) : ℚ :=
  modeWeight h * ((factor h).etaIm * (factor h).wRe - (factor h).etaRe * (factor h).wIm)

theorem modeWeight_cast (h : Coordinate) :
    (modeWeight h : ℝ) = Period1024.multiplicity h / ADMM.RefinedEndpoint.Data.period /
      (ADMM.RefinedEndpoint.Data.denominator : ℝ) ^ 2 := by
  by_cases hm : mode h = ADMM.RefinedEndpoint.Data.period / 2 <;>
    simp [modeWeight, rationalModeMultiplicity, Period1024.multiplicity, hm]

/-- The first diagonal Gram block is a rational cosine sum. -/
theorem eta_inner_rational (i j : Phase) :
    inner ℝ (eta i) (eta j) =
      ∑ h, (firstGramCoefficient h : ℝ) * (phase h (j - i)).re := by
  rw [eta_inner]
  apply Finset.sum_congr rfl
  intro h _
  rw [gram_product_re]
  simp only [etaCoefficient_re, etaCoefficient_im]
  simp only [firstGramCoefficient, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
    Rat.cast_intCast, modeWeight_cast]
  ring

/-- The multiplier diagonal Gram block is a rational cosine sum. -/
theorem scaledMultiplier_inner_rational (i j : Phase) :
    inner ℝ (scaledMultiplier i) (scaledMultiplier j) =
      ∑ h, (secondGramCoefficient h : ℝ) * (phase h (j - i)).re := by
  rw [scaledMultiplier_inner]
  apply Finset.sum_congr rfl
  intro h _
  rw [gram_product_re]
  simp only [multiplierCoefficient_re, multiplierCoefficient_im]
  simp only [secondGramCoefficient, Rat.cast_mul, Rat.cast_add, Rat.cast_pow,
    Rat.cast_intCast, modeWeight_cast]
  ring

/-- The cross Gram block is exactly the rational cosine-plus-sine formula. -/
theorem eta_scaledMultiplier_inner_rational (i j : Phase) :
    inner ℝ (eta i) (scaledMultiplier j) =
      ∑ h, ((crossRealCoefficient h : ℝ) * (phase h (j - i)).re +
        (crossSineCoefficient h : ℝ) * (phase h (j - i)).im) := by
  rw [eta_scaledMultiplier_inner]
  apply Finset.sum_congr rfl
  intro h _
  rw [gram_product_re]
  simp only [etaCoefficient_re, etaCoefficient_im,
    multiplierCoefficient_re, multiplierCoefficient_im]
  simp only [crossRealCoefficient, crossSineCoefficient, Rat.cast_mul, Rat.cast_add,
    Rat.cast_sub, Rat.cast_intCast, modeWeight_cast]
  ring

end ConsensusADMM.RefinedEndpoint.Certificate
