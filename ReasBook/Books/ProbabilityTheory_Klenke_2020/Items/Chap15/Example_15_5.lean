/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

noncomputable section

/-- The standard log-normal law on `ℝ`, defined as the image of the standard Gaussian law under
exponentiation. -/
def standardLogNormalMeasure : Measure ℝ :=
  (gaussianReal 0 1).map Real.exp

/-- The density of the standard log-normal law on `ℝ`, extended by `0` on `(-∞, 0]`. -/
def standardLogNormalDensityReal (x : ℝ) : ℝ :=
  if 0 < x then gaussianPDFReal 0 1 (Real.log x) / x else 0

/-- The oscillatory perturbation of the standard log-normal density by the factor
`1 + α sin(2π log x)` for `α ∈ [-1, 1]`. -/
def logNormalPerturbationDensityReal (α : Set.Icc (-1 : ℝ) 1) (x : ℝ) : ℝ :=
  standardLogNormalDensityReal x * (1 + α.1 * Real.sin (2 * Real.pi * Real.log x))

/-- The measure with density `logNormalPerturbationDensityReal α` with respect to Lebesgue
measure. -/
def logNormalPerturbationMeasure (α : Set.Icc (-1 : ℝ) 1) : Measure ℝ :=
  volume.withDensity (fun x ↦ ENNReal.ofReal (logNormalPerturbationDensityReal α x))

/-- Helper for Example 15.5: the standard log-normal density is measurable. -/
private lemma measurable_standardLogNormalDensityReal : Measurable standardLogNormalDensityReal := by
  -- Proof comment: the density is a measurable positive-branch formula glued with `0` on
  -- the nonpositive half-line.
  refine Measurable.piecewise measurableSet_Ioi ?_ measurable_const
  simpa [standardLogNormalDensityReal] using
    ((ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp Real.measurable_log).div measurable_id

/-- Helper for Example 15.5: the standard log-normal density is nonnegative. -/
private lemma standardLogNormalDensityReal_nonneg (x : ℝ) : 0 ≤ standardLogNormalDensityReal x := by
  by_cases hx : 0 < x
  · -- Proof comment: on `(0, ∞)` the density is a nonnegative Gaussian factor divided by `x`.
    simp [standardLogNormalDensityReal, hx, div_nonneg,
      ProbabilityTheory.gaussianPDFReal_nonneg, le_of_lt hx]
  · -- Proof comment: on `(-∞, 0]` the density is defined to be `0`.
    simp [standardLogNormalDensityReal, hx]

/-- Helper for Example 15.5: the perturbed log-normal density is measurable. -/
private lemma measurable_logNormalPerturbationDensityReal (α : Set.Icc (-1 : ℝ) 1) :
    Measurable (logNormalPerturbationDensityReal α) := by
  -- Proof comment: multiply the measurable base density by the oscillatory measurable factor.
  refine measurable_standardLogNormalDensityReal.mul ?_
  fun_prop

/-- Helper for Example 15.5: the oscillatory factor preserves nonnegativity for `α ∈ [-1, 1]`. -/
private lemma logNormalPerturbationDensityReal_nonneg (α : Set.Icc (-1 : ℝ) 1) (x : ℝ) :
    0 ≤ logNormalPerturbationDensityReal α x := by
  have hα : |α.1| ≤ 1 := by
    exact abs_le.mpr α.2
  have hsin : |Real.sin (2 * Real.pi * Real.log x)| ≤ 1 := Real.abs_sin_le_one _
  have hmul : -1 ≤ α.1 * Real.sin (2 * Real.pi * Real.log x) := by
    have habs : |α.1 * Real.sin (2 * Real.pi * Real.log x)| ≤ 1 := by
      calc
        |α.1 * Real.sin (2 * Real.pi * Real.log x)|
            = |α.1| * |Real.sin (2 * Real.pi * Real.log x)| := by rw [abs_mul]
        _ ≤ 1 * 1 := by gcongr
        _ = 1 := by ring
    linarith [abs_le.mp habs]
  -- Proof comment: the perturbation factor is nonnegative, so multiplying by the base density
  -- preserves nonnegativity.
  refine mul_nonneg (standardLogNormalDensityReal_nonneg x) ?_
  linarith

/-- Helper for Example 15.5: integrating a test function against the standard log-normal density
matches integrating its pullback along `Real.exp` against the standard Gaussian density. -/
private lemma integral_mul_standardLogNormalDensityReal_eq_gaussian (g : ℝ → ℝ) :
    ∫ x, g x * standardLogNormalDensityReal x = ∫ y, g (Real.exp y) * gaussianPDFReal 0 1 y := by
  -- Route correction: instead of mixing the piecewise density normalization with `log` transport,
  -- first push the integral forward along `Real.exp`, then cancel the Jacobian on the positive
  -- line using the explicit value of `standardLogNormalDensityReal (Real.exp y)`.
  have himage :
      ∫ x in (Real.exp '' Set.univ), g x * standardLogNormalDensityReal x =
        ∫ y, Real.exp y * (g (Real.exp y) * standardLogNormalDensityReal (Real.exp y)) := by
    simpa using
      (MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
        (f := Real.exp) (f' := Real.exp) (s := Set.univ) MeasurableSet.univ
        (fun y _ ↦ Real.hasDerivAt_exp y |>.hasDerivWithinAt)
        (fun x hx y hy hxy ↦ Real.exp_monotone hxy) (fun x ↦ g x * standardLogNormalDensityReal x))
  calc
    ∫ x, g x * standardLogNormalDensityReal x
        = ∫ x, Set.indicator (Set.Ioi (0 : ℝ))
            (fun x ↦ g x * standardLogNormalDensityReal x) x := by
            refine integral_congr_ae ?_
            filter_upwards with x
            by_cases hx : 0 < x
            · simp [hx]
            · simp [standardLogNormalDensityReal, hx]
    _ = ∫ x in Set.Ioi (0 : ℝ), g x * standardLogNormalDensityReal x := by
          rw [MeasureTheory.integral_indicator measurableSet_Ioi]
    _ = ∫ x in (Real.exp '' Set.univ), g x * standardLogNormalDensityReal x := by
          simp [Set.image_univ, Real.range_exp]
    _ = ∫ y, Real.exp y * (g (Real.exp y) * standardLogNormalDensityReal (Real.exp y)) := himage
    _ = ∫ y, g (Real.exp y) * gaussianPDFReal 0 1 y := by
          refine integral_congr_ae ?_
          filter_upwards with y
          have hy : 0 < Real.exp y := Real.exp_pos y
          rw [standardLogNormalDensityReal, if_pos hy, Real.log_exp]
          field_simp

/-- Helper for Example 15.5: the standard log-normal density is integrable on `ℝ`. -/
private lemma integrable_standardLogNormalDensityReal : Integrable standardLogNormalDensityReal := by
  have hIoi : IntegrableOn standardLogNormalDensityReal (Set.Ioi (0 : ℝ)) := by
    have htransport :=
      (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        (f := Real.exp) (f' := Real.exp) (s := Set.univ) MeasurableSet.univ
        (fun y _ ↦ (Real.hasDerivAt_exp y).hasDerivWithinAt)
        (fun x hx y hy hxy ↦ Real.exp_monotone hxy) standardLogNormalDensityReal)
    have hgauss :
        IntegrableOn (fun y ↦ Real.exp y * standardLogNormalDensityReal (Real.exp y)) Set.univ := by
      refine (integrable_gaussianPDFReal 0 1).integrableOn.congr_fun ?_ MeasurableSet.univ
      intro y hy
      have hy' : 0 < Real.exp y := Real.exp_pos y
      simp [standardLogNormalDensityReal, hy', Real.log_exp]
      field_simp [hy'.ne']
    simpa [Set.image_univ, Real.range_exp] using htransport.mpr hgauss
  have hIic : IntegrableOn standardLogNormalDensityReal (Set.Iic (0 : ℝ)) := by
    have hzero : IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Iic (0 : ℝ)) := by
      simp [IntegrableOn]
    refine hzero.congr_fun ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := by simpa using hx
    simp [standardLogNormalDensityReal, not_lt.mpr hx']
  simpa [IntegrableOn, Set.Iic_union_Ioi] using hIic.union hIoi

-- Proof sketch: apply the one-dimensional change-of-variables formula to the pushforward of the
-- standard Gaussian law under `Real.exp`, which yields the textbook density
-- `x ↦ gaussianPDFReal 0 1 (log x) / x` on `(0, ∞)`.
/-- The standard log-normal law is the image of the standard Gaussian law under exponentiation,
and this image measure has density `standardLogNormalDensityReal` with respect to Lebesgue
measure. -/
theorem standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal :
    standardLogNormalMeasure =
      volume.withDensity (fun x ↦ ENNReal.ofReal (standardLogNormalDensityReal x)) := by
  -- Proof comment: compare both measures on measurable sets, using the bridge lemma on indicator
  -- functions to convert the pushforward side into the with-density integral.
  ext s hs
  calc
    standardLogNormalMeasure s
        = (gaussianReal 0 1).map Real.exp s := by rfl
    _ = gaussianReal 0 1 (Real.exp ⁻¹' s) := by
          rw [Measure.map_apply (by fun_prop) hs]
    _ = ENNReal.ofReal (∫ y in Real.exp ⁻¹' s, gaussianPDFReal 0 1 y) := by
          simpa using ProbabilityTheory.gaussianReal_apply_eq_integral (μ := 0) (v := 1)
            one_ne_zero (Real.exp ⁻¹' s)
    _ = ENNReal.ofReal (∫ y, Set.indicator (Real.exp ⁻¹' s) (gaussianPDFReal 0 1) y) := by
          have hs_pre : MeasurableSet (Real.exp ⁻¹' s) := Real.measurable_exp hs
          congr 1
          rw [← MeasureTheory.integral_indicator hs_pre]
    _ = ENNReal.ofReal (∫ y, Set.indicator s (fun x ↦ (1 : ℝ)) (Real.exp y) * gaussianPDFReal 0 1 y) := by
          congr 1
          refine integral_congr_ae ?_
          filter_upwards with y
          by_cases hy : Real.exp y ∈ s <;> simp [Set.indicator, hy]
    _ = ENNReal.ofReal (∫ x, Set.indicator s (fun x ↦ (1 : ℝ)) x * standardLogNormalDensityReal x) := by
          rw [← integral_mul_standardLogNormalDensityReal_eq_gaussian]
    _ = ENNReal.ofReal (∫ x in s, standardLogNormalDensityReal x) := by
          congr 1
          rw [← MeasureTheory.integral_indicator hs]
          refine integral_congr_ae ?_
          filter_upwards with x
          by_cases hx : x ∈ s <;> simp [Set.indicator, hx]
    _ = volume.withDensity (fun x ↦ ENNReal.ofReal (standardLogNormalDensityReal x)) s := by
          rw [MeasureTheory.withDensity_apply _ hs]
          simpa [IntegrableOn] using
            (ofReal_integral_eq_lintegral_ofReal
              (μ := volume.restrict s) (f := standardLogNormalDensityReal)
              integrable_standardLogNormalDensityReal.integrableOn
              (ae_of_all _ fun x ↦ standardLogNormalDensityReal_nonneg x))

-- Proof sketch: rewrite the integral using
-- `standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal`, so the moment becomes
-- `E[exp(nY)]` for a standard Gaussian `Y`, and then evaluate the Gaussian moment-generating
-- function at `n`.
/-- The `n`th moment of the standard log-normal law equals `exp (n^2 / 2)`. -/
theorem standardLogNormalMeasure_moment (n : ℕ) :
    moment id n standardLogNormalMeasure = Real.exp (((n : ℝ) ^ 2) / 2) := by
  -- Proof comment: pull the moment back through `Real.exp` and identify the result with the
  -- Gaussian mgf at `t = n`.
  rw [standardLogNormalMeasure, ProbabilityTheory.moment_def]
  rw [MeasureTheory.integral_map (μ := gaussianReal 0 1) (φ := Real.exp) (by fun_prop) (by fun_prop)]
  have hpow : (fun x : ℝ ↦ (id ^ n) (Real.exp x)) = fun x ↦ Real.exp (x * n) := by
    funext x
    simpa [Pi.pow_apply, mul_comm] using (Real.exp_nat_mul x n).symm
  rw [hpow]
  have hmgf := congrFun (ProbabilityTheory.mgf_id_gaussianReal (μ := 0) (v := 1)) (n : ℝ)
  simpa [ProbabilityTheory.mgf, mul_comm] using hmgf

/-- Helper for Example 15.5: the standard Gaussian expectation of `sin (2πx)` vanishes by oddness.
-/
private lemma gaussianSineExpectation_eq_zero :
    ∫ y, Real.sin (2 * Real.pi * y) ∂(gaussianReal (0 : ℝ) (1 : NNReal)) = 0 := by
  let γ : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)
  have hsymm : γ.map (fun y : ℝ ↦ -y) = γ := by
    simpa [γ] using
      (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have hEq :
      ∫ y, Real.sin (2 * Real.pi * y) ∂γ =
        ∫ y, Real.sin (2 * Real.pi * (-y)) ∂γ := by
    -- Proof comment: reflect the centered Gaussian through `y ↦ -y`; the law stays unchanged.
    calc
      ∫ y, Real.sin (2 * Real.pi * y) ∂γ
          = ∫ y, Real.sin (2 * Real.pi * y) ∂Measure.map (fun y : ℝ ↦ -y) γ := by
              simpa [hsymm]
      _ = ∫ y, Real.sin (2 * Real.pi * (-y)) ∂γ := by
            rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  have hNeg :
      ∫ y, Real.sin (2 * Real.pi * (-y)) ∂γ =
        -∫ y, Real.sin (2 * Real.pi * y) ∂γ := by
    -- Proof comment: the sine kernel is odd, so reflection negates the integral.
    have hfun :
        (fun y : ℝ ↦ Real.sin (2 * Real.pi * (-y))) =
          fun y ↦ -Real.sin (2 * Real.pi * y) := by
      funext y
      have harg : 2 * Real.pi * (-y) = -(2 * Real.pi * y) := by ring
      rw [harg, Real.sin_neg]
    rw [hfun, MeasureTheory.integral_neg]
  have hzero : ∫ y, Real.sin (2 * Real.pi * y) ∂γ = -∫ y, Real.sin (2 * Real.pi * y) ∂γ :=
    hEq.trans hNeg
  linarith

/-- Helper for Example 15.5: integer shifts preserve the vanishing Gaussian sine expectation. -/
private lemma gaussianShiftedSineExpectation_eq_zero (n : ℕ) :
    ∫ y, Real.sin (2 * Real.pi * y) ∂(gaussianReal (n : ℝ) (1 : NNReal)) = 0 := by
  have hmap :
      (gaussianReal (0 : ℝ) (1 : NNReal)).map (fun y : ℝ ↦ y + (n : ℝ)) =
        gaussianReal (n : ℝ) (1 : NNReal) := by
    simpa using
      (ProbabilityTheory.gaussianReal_map_add_const
        (μ := (0 : ℝ)) (v := (1 : NNReal)) (n : ℝ))
  -- Proof comment: rewrite the shifted Gaussian as the pushforward of the centered one, then use
  -- the period `sin (x + n * 2π) = sin x`.
  calc
    ∫ y, Real.sin (2 * Real.pi * y) ∂(gaussianReal (n : ℝ) (1 : NNReal))
        = ∫ y, Real.sin (2 * Real.pi * y)
            ∂Measure.map (fun y : ℝ ↦ y + (n : ℝ)) (gaussianReal (0 : ℝ) (1 : NNReal)) := by
              rw [← hmap]
    _ = ∫ y, Real.sin (2 * Real.pi * (y + (n : ℝ))) ∂(gaussianReal (0 : ℝ) (1 : NNReal)) := by
          rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ y, Real.sin (2 * Real.pi * y) ∂(gaussianReal (0 : ℝ) (1 : NNReal)) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          have hperiod :
              Real.sin (2 * Real.pi * (y + (n : ℝ))) = Real.sin (2 * Real.pi * y) := by
            have harg :
                2 * Real.pi * (y + (n : ℝ)) = 2 * Real.pi * y + n * (2 * Real.pi) := by ring
            rw [harg, Real.sin_add_nat_mul_two_pi]
          simpa using hperiod
    _ = 0 := gaussianSineExpectation_eq_zero

private lemma integral_gaussianPDFReal_mul_sin_two_pi_eq_zero :
    ∫ y, gaussianPDFReal 0 1 y * Real.sin (2 * Real.pi * y) = 0 := by
  -- Proof comment: convert the density integral to a Gaussian expectation and reuse oddness.
  calc
    ∫ y, gaussianPDFReal 0 1 y * Real.sin (2 * Real.pi * y)
        = ∫ y, Real.sin (2 * Real.pi * y) ∂(gaussianReal (0 : ℝ) (1 : NNReal)) := by
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
              (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
                (μ := (0 : ℝ)) (v := (1 : NNReal))
                (f := fun y : ℝ ↦ Real.sin (2 * Real.pi * y)) one_ne_zero).symm
    _ = 0 := gaussianSineExpectation_eq_zero

/-- Helper for Example 15.5: tilting the standard Gaussian density by `exp (ny)` produces the
shifted Gaussian density with mean `n` up to the factor `exp (n^2 / 2)`. -/
private lemma exp_nat_mul_gaussianPDFReal_eq_shifted (n : ℕ) (y : ℝ) :
    Real.exp ((n : ℝ) * y) * gaussianPDFReal 0 1 y =
      Real.exp (((n : ℝ) ^ 2) / 2) * gaussianPDFReal (n : ℝ) 1 y := by
  -- Proof comment: expand both Gaussian densities once and complete the square in the exponent.
  have hexp :
      Real.exp ((n : ℝ) * y) *
          Real.exp (-(y - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))) =
        Real.exp (((n : ℝ) ^ 2) / 2) *
          Real.exp (-(y - (n : ℝ)) ^ 2 / (2 * ((1 : NNReal) : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    norm_num
    ring
  rw [ProbabilityTheory.gaussianPDFReal_def, ProbabilityTheory.gaussianPDFReal_def]
  calc
    Real.exp ((n : ℝ) * y) *
        ((√(2 * Real.pi * (1 : NNReal)))⁻¹ *
          Real.exp (-(y - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ))))
        = (√(2 * Real.pi * (1 : NNReal)))⁻¹ *
            (Real.exp ((n : ℝ) * y) *
              Real.exp (-(y - 0) ^ 2 / (2 * ((1 : NNReal) : ℝ)))) := by ring
    _ = (√(2 * Real.pi * (1 : NNReal)))⁻¹ *
          (Real.exp (((n : ℝ) ^ 2) / 2) *
            Real.exp (-(y - (n : ℝ)) ^ 2 / (2 * ((1 : NNReal) : ℝ)))) := by rw [hexp]
    _ = Real.exp (((n : ℝ) ^ 2) / 2) *
          ((√(2 * Real.pi * (1 : NNReal)))⁻¹ *
            Real.exp (-(y - (n : ℝ)) ^ 2 / (2 * ((1 : NNReal) : ℝ)))) := by ring

/-- Helper for Example 15.5: the Gaussian tilt appearing after the substitution still has zero
oscillatory integral. -/
private lemma integral_exp_nat_mul_gaussianPDFReal_mul_sin_two_pi_eq_zero (n : ℕ) :
    ∫ y, Real.exp ((n : ℝ) * y) * gaussianPDFReal 0 1 y * Real.sin (2 * Real.pi * y) = 0 := by
  -- Proof comment: normalize the exponential tilt to the shifted Gaussian density and then use
  -- the shifted sine-expectation lemma.
  calc
    ∫ y, Real.exp ((n : ℝ) * y) * gaussianPDFReal 0 1 y * Real.sin (2 * Real.pi * y)
        = ∫ y,
            (Real.exp (((n : ℝ) ^ 2) / 2) * gaussianPDFReal (n : ℝ) 1 y) *
              Real.sin (2 * Real.pi * y) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with y
            rw [exp_nat_mul_gaussianPDFReal_eq_shifted]
    _ = Real.exp (((n : ℝ) ^ 2) / 2) *
          ∫ y, gaussianPDFReal (n : ℝ) 1 y * Real.sin (2 * Real.pi * y) := by
            simpa [mul_assoc] using
              (MeasureTheory.integral_const_mul
                (Real.exp (((n : ℝ) ^ 2) / 2))
                (fun y : ℝ ↦ gaussianPDFReal (n : ℝ) 1 y * Real.sin (2 * Real.pi * y)))
    _ = Real.exp (((n : ℝ) ^ 2) / 2) *
          ∫ y, Real.sin (2 * Real.pi * y) ∂(gaussianReal (n : ℝ) (1 : NNReal)) := by
            congr 1
            simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using
              (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
                (μ := (n : ℝ)) (v := (1 : NNReal))
                (f := fun y : ℝ ↦ Real.sin (2 * Real.pi * y)) one_ne_zero).symm
    _ = 0 := by rw [gaussianShiftedSineExpectation_eq_zero, mul_zero]

-- Proof sketch: substitute `y = log x - n` in the integral. After simplifying, the remaining
-- Gaussian-weighted integrand is odd because `sin (2π (y + n)) = sin (2π y)`, so the integral
-- vanishes.
/-- The oscillatory correction term used to build the Stieltjes class has vanishing moments. -/
theorem logNormalOscillatoryMoment_eq_zero (n : ℕ) :
    ∫ x, x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x) = 0 := by
  -- Proof comment: transport the log-normal integral to the Gaussian side and then apply the
  -- tilted Gaussian cancellation lemma.
  calc
    ∫ x, x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x)
        = ∫ y,
            (Real.exp y) ^ n * Real.sin (2 * Real.pi * Real.log (Real.exp y)) *
              gaussianPDFReal 0 1 y := by
            simpa [mul_assoc, mul_left_comm, mul_comm] using
              (integral_mul_standardLogNormalDensityReal_eq_gaussian
                (g := fun x : ℝ ↦ x ^ n * Real.sin (2 * Real.pi * Real.log x)))
    _ = ∫ y,
          Real.exp ((n : ℝ) * y) * gaussianPDFReal 0 1 y *
            Real.sin (2 * Real.pi * y) := by
          refine MeasureTheory.integral_congr_ae ?_
          filter_upwards with y
          rw [Real.log_exp, Real.exp_nat_mul]
          ring
    _ = 0 := integral_exp_nat_mul_gaussianPDFReal_mul_sin_two_pi_eq_zero n

/-- Helper for Example 15.5: the base `n`th-moment integrand is integrable. -/
private lemma integrable_pow_mul_standardLogNormalDensityReal (n : ℕ) :
    Integrable (fun x : ℝ ↦ x ^ n * standardLogNormalDensityReal x) := by
  have hIoi : IntegrableOn (fun x : ℝ ↦ x ^ n * standardLogNormalDensityReal x) (Set.Ioi (0 : ℝ)) := by
    have htransport :=
      (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        (f := Real.exp) (f' := Real.exp) (s := Set.univ) MeasurableSet.univ
        (fun y _ ↦ (Real.hasDerivAt_exp y).hasDerivWithinAt)
        (fun x hx y hy hxy ↦ Real.exp_monotone hxy)
        (fun x : ℝ ↦ x ^ n * standardLogNormalDensityReal x))
    have hgauss :
        IntegrableOn
          (fun y : ℝ ↦ Real.exp y * ((Real.exp y) ^ n * standardLogNormalDensityReal (Real.exp y)))
          Set.univ := by
      refine ((ProbabilityTheory.integrable_gaussianPDFReal (n : ℝ) 1).const_mul
        (Real.exp (((n : ℝ) ^ 2) / 2))).integrableOn.congr_fun ?_ MeasurableSet.univ
      intro y hy
      have hy' : 0 < Real.exp y := Real.exp_pos y
      simp [standardLogNormalDensityReal, hy', Real.log_exp]
      have hcancel :
          Real.exp y * ((Real.exp y) ^ n * (gaussianPDFReal 0 1 y / Real.exp y)) =
            (Real.exp y) ^ n * gaussianPDFReal 0 1 y := by
        field_simp [hy'.ne']
      have htilt :
          (Real.exp y) ^ n * gaussianPDFReal 0 1 y =
            Real.exp (((n : ℝ) ^ 2) / 2) * gaussianPDFReal (n : ℝ) 1 y := by
        have hexp : (Real.exp y) ^ n = Real.exp ((n : ℝ) * y) := by
          simpa [mul_comm] using (Real.exp_nat_mul y n).symm
        calc
          (Real.exp y) ^ n * gaussianPDFReal 0 1 y
              = Real.exp ((n : ℝ) * y) * gaussianPDFReal 0 1 y := by rw [hexp]
          _ = Real.exp (((n : ℝ) ^ 2) / 2) * gaussianPDFReal (n : ℝ) 1 y :=
                exp_nat_mul_gaussianPDFReal_eq_shifted n y
      rw [hcancel, htilt]
    simpa [Set.image_univ, Real.range_exp] using htransport.mpr hgauss
  have hIic : IntegrableOn (fun x : ℝ ↦ x ^ n * standardLogNormalDensityReal x) (Set.Iic (0 : ℝ)) := by
    have hzero : IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Iic (0 : ℝ)) := by
      simp [IntegrableOn]
    refine hzero.congr_fun ?_ measurableSet_Iic
    intro x hx
    have hx' : x ≤ 0 := by simpa using hx
    simp [standardLogNormalDensityReal, not_lt.mpr hx']
  -- Proof comment: the density vanishes on `(-∞, 0]`, so only the transported positive branch
  -- contributes.
  simpa [IntegrableOn, Set.Iic_union_Ioi] using hIic.union hIoi

/-- Helper for Example 15.5: the oscillatory `n`th-moment correction integrand is integrable. -/
private lemma integrable_pow_mul_standardLogNormalDensityReal_mul_sin (n : ℕ) :
    Integrable (fun x : ℝ ↦
      x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x)) := by
  -- Proof comment: the oscillatory factor is uniformly bounded by `1`, so the correction term is
  -- dominated by the already integrable base moment integrand.
  have hsin :
      Measurable (fun x : ℝ ↦ Real.sin (2 * Real.pi * Real.log x)) := by
    exact Real.continuous_sin.measurable.comp ((measurable_const).mul Real.measurable_log)
  have hmeas :
      AEStronglyMeasurable
        (fun x : ℝ ↦ x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x))
        volume := by
    exact
      (((measurable_id.pow_const n).aestronglyMeasurable.mul
          measurable_standardLogNormalDensityReal.aestronglyMeasurable).mul
        hsin.aestronglyMeasurable)
  refine MeasureTheory.Integrable.mono' (integrable_pow_mul_standardLogNormalDensityReal n).norm
    hmeas ?_
  filter_upwards with x
  calc
    ‖x ^ n * standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x)‖
        = ‖x ^ n * standardLogNormalDensityReal x‖ *
            ‖Real.sin (2 * Real.pi * Real.log x)‖ := by rw [norm_mul]
    _ ≤ ‖x ^ n * standardLogNormalDensityReal x‖ * 1 := by
          gcongr
          simpa [Real.norm_eq_abs] using Real.abs_sin_le_one (2 * Real.pi * Real.log x)
    _ = ‖x ^ n * standardLogNormalDensityReal x‖ := by rw [mul_one]

/-- Helper for Example 15.5: the standard log-normal moment integral equals the corresponding
moment of the log-normal measure. -/
private lemma integral_pow_mul_standardLogNormalDensityReal_eq_moment (n : ℕ) :
    ∫ x, x ^ n * standardLogNormalDensityReal x = moment id n standardLogNormalMeasure := by
  -- Proof comment: rewrite the standard log-normal law through its density and then identify the
  -- resulting integral with the moment definition.
  rw [standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal, ProbabilityTheory.moment_def]
  rw [integral_withDensity_eq_integral_toReal_smul
    (μ := volume)
    (f := fun x ↦ ENNReal.ofReal (standardLogNormalDensityReal x))
    measurable_standardLogNormalDensityReal.ennreal_ofReal
    (Filter.Eventually.of_forall fun x ↦ by simp)]
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards with x
  rw [ENNReal.toReal_ofReal (standardLogNormalDensityReal_nonneg x)]
  simp [Pi.pow_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]

-- Proof sketch: the bound `|α| ≤ 1` implies that the oscillatory factor
-- `1 + α sin (2π log x)` is nonnegative, so `logNormalPerturbationMeasure α` is a probability
-- measure. The moment identity follows by expanding the perturbed density and using
-- `logNormalOscillatoryMoment_eq_zero` to kill the oscillatory contribution.
/-- Example 15.5: for every `α ∈ [-1, 1]`, the perturbed log-normal density defines a probability
measure whose moments agree with those of the standard log-normal law. -/
theorem logNormalPerturbationMeasure_isProbabilityMeasure_and_sameMoments
    (α : Set.Icc (-1 : ℝ) 1) :
    IsProbabilityMeasure (logNormalPerturbationMeasure α) ∧
      ∀ n : ℕ,
        moment id n (logNormalPerturbationMeasure α) =
          moment id n standardLogNormalMeasure := by
  have hmom :
      ∀ n : ℕ,
      moment id n (logNormalPerturbationMeasure α) =
          moment id n standardLogNormalMeasure := by
    intro n
    -- Proof comment: expand the perturbed density, split the integral into the base log-normal
    -- term and the oscillatory correction, and then kill the correction by the previous theorem.
    calc
      moment id n (logNormalPerturbationMeasure α)
          = ∫ x, x ^ n * logNormalPerturbationDensityReal α x := by
              rw [logNormalPerturbationMeasure, ProbabilityTheory.moment_def]
              rw [integral_withDensity_eq_integral_toReal_smul
                (μ := volume)
                (f := fun x ↦ ENNReal.ofReal (logNormalPerturbationDensityReal α x))
                (measurable_logNormalPerturbationDensityReal α).ennreal_ofReal
                (Filter.Eventually.of_forall fun x ↦ by simp)]
              refine MeasureTheory.integral_congr_ae ?_
              filter_upwards with x
              rw [ENNReal.toReal_ofReal (logNormalPerturbationDensityReal_nonneg α x)]
              simp [Pi.pow_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm]
      _ = ∫ x,
            x ^ n * standardLogNormalDensityReal x +
              α.1 *
                (x ^ n * standardLogNormalDensityReal x *
                  Real.sin (2 * Real.pi * Real.log x)) := by
            refine MeasureTheory.integral_congr_ae ?_
            filter_upwards with x
            simp [logNormalPerturbationDensityReal]
            ring
      _ = (∫ x, x ^ n * standardLogNormalDensityReal x) +
            ∫ x,
              α.1 *
                (x ^ n * standardLogNormalDensityReal x *
                  Real.sin (2 * Real.pi * Real.log x)) := by
            simpa using
              (MeasureTheory.integral_add
                (integrable_pow_mul_standardLogNormalDensityReal n)
                ((integrable_pow_mul_standardLogNormalDensityReal_mul_sin n).const_mul α.1))
      _ = (∫ x, x ^ n * standardLogNormalDensityReal x) +
            α.1 *
              (∫ x,
                x ^ n * standardLogNormalDensityReal x *
                  Real.sin (2 * Real.pi * Real.log x)) := by
            rw [MeasureTheory.integral_const_mul]
      _ = ∫ x, x ^ n * standardLogNormalDensityReal x := by
            simp [logNormalOscillatoryMoment_eq_zero]
      _ = moment id n standardLogNormalMeasure :=
            integral_pow_mul_standardLogNormalDensityReal_eq_moment n
  have hprobReal : (logNormalPerturbationMeasure α).real Set.univ = 1 := by
    have hmoment0 : moment id 0 (logNormalPerturbationMeasure α) = 1 := by
      rw [hmom 0, standardLogNormalMeasure_moment 0]
      norm_num
    simpa [ProbabilityTheory.moment_def] using hmoment0
  exact ⟨(MeasureTheory.isProbabilityMeasure_iff_real).2 hprobReal, hmom⟩
