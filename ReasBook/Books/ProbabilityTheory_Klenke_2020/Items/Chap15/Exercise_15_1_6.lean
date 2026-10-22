/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap04.Exercise_4_2_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap14.Lemma_14_27

open Filter MeasureTheory
open ProbabilityTheory
open scoped ENNReal FourierTransform NNReal Topology

noncomputable section

/-- The inverse-Fourier candidate density attached to the characteristic function of a real
probability measure, built from the canonical owners `MeasureTheory.charFun` and `𝓕⁻`. -/
def charFunInversionDensity (μ : Measure ℝ) : ℝ → ℝ :=
  fun x ↦ Complex.re ((𝓕⁻ fun t : ℝ ↦ charFun μ (-2 * Real.pi * t)) x)

section

variable (μ : Measure ℝ)

/-- Helper for Exercise 15.1.6: precomposing the characteristic function with the Fourier
normalization `t ↦ -2πt` preserves integrability. -/
lemma integrable_scaledCharFun
    (hφ : Integrable (charFun μ) volume) :
    Integrable (fun t : ℝ ↦ charFun μ (-2 * Real.pi * t)) := by
  -- Proof comment: scalar multiplication by a nonzero real number preserves `L¹`-integrability.
  simpa [mul_assoc] using hφ.comp_mul_left' (R := -2 * Real.pi) (by positivity)

/-- Helper for Exercise 15.1.6: the candidate density is the real part of the Fourier transform of
the rescaled characteristic function. -/
lemma charFunInversionDensity_eq_re_fourier_scaledCharFun :
    charFunInversionDensity μ =
      fun x ↦ Complex.re ((𝓕 fun t : ℝ ↦ charFun μ (-2 * Real.pi * t)) (-x)) := by
  -- Proof comment: rewrite the inverse Fourier transform in the definition as a Fourier transform
  -- evaluated at `-x`.
  ext x
  rw [charFunInversionDensity, Real.fourierInv_eq_fourier_neg]

/-- Helper for Exercise 15.1.6: integrability of the candidate density makes the associated
`withDensity` measure finite. -/
lemma withDensity_charFunInversionDensity_isFinite
    (h_int : Integrable (charFunInversionDensity μ)) :
    IsFiniteMeasure (volume.withDensity (ENNReal.ofReal ∘ charFunInversionDensity μ)) := by
  -- Proof comment: the total mass of the `withDensity` measure is the `ofReal`-lintegral of the
  -- candidate density, which is finite for every integrable real-valued function.
  simpa [Function.comp_def] using
    (MeasureTheory.isFiniteMeasure_withDensity_ofReal
      (μ := volume) (f := charFunInversionDensity μ) h_int.hasFiniteIntegral)

/-- Helper for Exercise 15.1.6: the ENNReal density of the Gaussian smoothing
`μ ∗ gaussianReal 0 ε`. -/
def gaussianSmoothedDensity (μ : Measure ℝ) (ε : ℝ≥0) : ℝ → ℝ≥0∞ :=
  fun x ↦ ∫⁻ y, gaussianPDF y ε x ∂μ

/-- Helper for Exercise 15.1.6: the two-variable Gaussian density kernel is measurable. -/
lemma measurable_gaussianPDFKernel (ε : ℝ≥0) :
    Measurable (fun z : ℝ × ℝ ↦ gaussianPDF z.1 ε z.2) := by
  have hreal : Measurable (fun z : ℝ × ℝ ↦ gaussianPDFReal z.1 ε z.2) := by
    change Measurable
      (fun z : ℝ × ℝ ↦ (Real.sqrt (2 * Real.pi * ε))⁻¹ *
        Real.exp (-(z.2 - z.1) ^ 2 / (2 * ε)))
    exact (((measurable_snd.sub measurable_fst).pow_const 2).neg.div_const _).exp.const_mul _
  simpa [ProbabilityTheory.gaussianPDF] using hreal.ennreal_ofReal

/-- Helper for Exercise 15.1.6: for fixed `x`, the Gaussian kernel is measurable in the center
variable. -/
lemma measurable_gaussianPDF_left (ε : ℝ≥0) (x : ℝ) :
    Measurable (fun y : ℝ ↦ gaussianPDF y ε x) := by
  have hreal : Measurable (fun y : ℝ ↦ gaussianPDFReal y ε x) := by
    change Measurable
      (fun y : ℝ ↦ (Real.sqrt (2 * Real.pi * ε))⁻¹ *
        Real.exp (-(x - y) ^ 2 / (2 * ε)))
    exact (((measurable_const.sub measurable_id).pow_const 2).neg.div_const _).exp.const_mul _
  simpa [ProbabilityTheory.gaussianPDF] using hreal.ennreal_ofReal

/-- Helper for Exercise 15.1.6: for fixed `x`, the real-valued Gaussian kernel is measurable in
the center variable. -/
lemma measurable_gaussianPDFReal_left (ε : ℝ≥0) (x : ℝ) :
    Measurable (fun y : ℝ ↦ gaussianPDFReal y ε x) := by
  change Measurable
    (fun y : ℝ ↦ (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-(x - y) ^ 2 / (2 * ε)))
  exact (((measurable_const.sub measurable_id).pow_const 2).neg.div_const _).exp.const_mul _

/-- Helper for Exercise 15.1.6: for fixed center `y`, the real-valued Gaussian profile is
continuous in the spatial variable. -/
lemma continuous_gaussianPDFReal_right (y : ℝ) (ε : ℝ≥0) :
    Continuous (fun x : ℝ ↦ gaussianPDFReal y ε x) := by
  change Continuous
    (fun x : ℝ ↦ (Real.sqrt (2 * Real.pi * ε))⁻¹ * Real.exp (-(x - y) ^ 2 / (2 * ε)))
  exact (Real.continuous_exp.comp
      (((continuous_id.sub continuous_const).pow 2).neg.div_const _)).const_mul _

/-- Helper for Exercise 15.1.6: the Gaussian-smoothed density is measurable in the spatial
variable. -/
lemma measurable_gaussianSmoothedDensity [SFinite μ] (ε : ℝ≥0) :
    Measurable (gaussianSmoothedDensity μ ε) := by
  -- Proof comment: the Gaussian kernel is jointly measurable, so integrating out the first
  -- variable preserves measurability.
  have hgauss : Measurable (Function.uncurry fun y x ↦ gaussianPDF y ε x) := by
    simpa [Function.uncurry] using measurable_gaussianPDFKernel ε
  simpa [gaussianSmoothedDensity] using
    (Measurable.lintegral_prod_left (μ := μ) (f := fun y x ↦ gaussianPDF y ε x) hgauss)

/-- Helper for Exercise 15.1.6: the translated Gaussian convolution kernel is the Gaussian
density kernel over Lebesgue measure. -/
lemma gaussianTranslationKernel_eq_densityKernel {ε : ℝ≥0} (hε : ε ≠ 0) :
    dirac_convolution_kernel (gaussianReal 0 ε) =
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ)) (fun y x ↦ gaussianPDF y ε x) := by
  -- Proof comment: each row of the translation kernel is `δ_y ∗ gaussianReal 0 ε`, which is the
  -- Gaussian law translated by `y` and therefore has density `gaussianPDF y ε`.
  have hgauss : Measurable (Function.uncurry fun y x ↦ gaussianPDF y ε x) := by
    simpa [Function.uncurry] using measurable_gaussianPDFKernel ε
  ext y s hs
  rw [dirac_convolution_kernel_apply,
    Kernel.withDensity_apply' (Kernel.const ℝ (volume : Measure ℝ)) hgauss]
  simp only [Kernel.const_apply]
  have hmap :
      (gaussianReal 0 ε).map (fun z : ℝ ↦ y + z) = gaussianReal y ε := by
    simpa using (ProbabilityTheory.gaussianReal_map_const_add (μ := 0) (v := ε) y)
  rw [Measure.dirac_conv, hmap]
  simpa using gaussianReal_apply y hε s

/-- Helper for Exercise 15.1.6: Gaussian convolution equals Lebesgue `withDensity` with the
integrated Gaussian kernel. -/
lemma gaussianConv_eq_withDensity_integratedKernel [IsProbabilityMeasure μ] {ε : ℝ≥0}
    (hε : ε ≠ 0) :
    μ ∗ gaussianReal 0 ε = volume.withDensity (fun x ↦ ∫⁻ y, gaussianPDF y ε x ∂μ) := by
  -- Proof comment: evaluate the Chap. 14 convolution kernel identity at the base point, then swap
  -- the two nonnegative integrals by Tonelli.
  have hkernelComp :
      dirac_convolution_kernel (gaussianReal 0 ε) ∘ₘ μ = μ ∗ gaussianReal 0 ε := by
    have hconst :=
      congrArg
        (fun κ : Kernel ℝ ℝ => κ (0 : ℝ))
        (dirac_convolution_kernel_comp_const_eq_const_conv
          (μ := μ) (ν := gaussianReal 0 ε))
    simpa [Kernel.comp_apply] using hconst
  have hgauss : Measurable (Function.uncurry fun y x ↦ gaussianPDF y ε x) := by
    simpa [Function.uncurry] using measurable_gaussianPDFKernel ε
  calc
    μ ∗ gaussianReal 0 ε = dirac_convolution_kernel (gaussianReal 0 ε) ∘ₘ μ := hkernelComp.symm
    _ =
        (Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
          (fun y x ↦ gaussianPDF y ε x)) ∘ₘ μ := by
          rw [gaussianTranslationKernel_eq_densityKernel (hε := hε)]
    _ = volume.withDensity (fun x ↦ ∫⁻ y, gaussianPDF y ε x ∂μ) := by
          ext s hs
          rw [Measure.bind_apply hs (Kernel.aemeasurable _), withDensity_apply _ hs]
          simp_rw [Kernel.withDensity_apply' _ hgauss]
          let g : ℝ → ℝ → ℝ≥0∞ := fun y x ↦ s.indicator (fun x ↦ gaussianPDF y ε x) x
          have hgMeas : Measurable (Function.uncurry g) := by
            have hpair : Measurable (fun z : ℝ × ℝ ↦ gaussianPDF z.1 ε z.2) := by
              exact measurable_gaussianPDFKernel ε
            simpa [g, Function.uncurry] using hpair.indicator (measurable_snd hs)
          -- Proof comment: rewrite both restricted integrals using indicators, then swap the
          -- order of integration once.
          calc
            ∫⁻ y, ∫⁻ x in s, gaussianPDF y ε x ∂volume ∂μ
                = ∫⁻ y, ∫⁻ x, g y x ∂volume ∂μ := by
                    simp_rw [g, ← lintegral_indicator hs]
            _ = ∫⁻ x, ∫⁻ y, g y x ∂μ ∂volume := by
                    rw [lintegral_lintegral_swap hgMeas.aemeasurable]
            _ = ∫⁻ x, s.indicator (fun x ↦ ∫⁻ y, gaussianPDF y ε x ∂μ) x ∂volume := by
                    refine lintegral_congr_ae (Filter.Eventually.of_forall ?_)
                    intro x
                    by_cases hx : x ∈ s
                    · simp [g, hx]
                    · simp [g, hx]
            _ = ∫⁻ x in s, ∫⁻ y, gaussianPDF y ε x ∂μ ∂volume := by
                    rw [lintegral_indicator hs]

/-- Helper for Exercise 15.1.6: convolving with a nondegenerate Gaussian produces an explicit
Lebesgue density. -/
lemma gaussianSmoothedLaw_eq_withDensity [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0) :
    μ ∗ gaussianReal 0 ε = volume.withDensity (gaussianSmoothedDensity μ ε) := by
  -- Proof comment: evaluate both measures on measurable sets, rewrite the convolution by Tonelli,
  -- and identify each translated Gaussian slice with its explicit density.
  simpa [gaussianSmoothedDensity] using
    gaussianConv_eq_withDensity_integratedKernel (μ := μ) hε

/-- Helper for Exercise 15.1.6: every Gaussian smoothing keeps total mass equal to `1`. -/
lemma lintegral_gaussianSmoothedDensity_eq_one [IsProbabilityMeasure μ] {ε : ℝ≥0}
    (hε : ε ≠ 0) :
    ∫⁻ x, gaussianSmoothedDensity μ ε x ∂volume = 1 := by
  -- Proof comment: the smoothed law is still a probability measure, and the preceding density
  -- description turns its total mass into the Lebesgue integral of the smoothed density.
  have hUniv :=
    congrArg
      (fun ν : Measure ℝ => ν Set.univ)
      (gaussianSmoothedLaw_eq_withDensity (μ := μ) hε)
  simpa [withDensity_apply, gaussianSmoothedDensity] using hUniv.symm

/-- Helper for Exercise 15.1.6: a Gaussian density never exceeds its peak value
`(√(2 * π * ε))⁻¹`. -/
lemma gaussianPDFReal_le_peak {ε : ℝ≥0} (hε : ε ≠ 0) (x y : ℝ) :
    gaussianPDFReal y ε x ≤ (Real.sqrt (2 * Real.pi * ε))⁻¹ := by
  -- Proof comment: the exponential factor in the Gaussian kernel is at most `1` because its
  -- exponent is nonpositive.
  rw [gaussianPDFReal]
  have hexp : Real.exp (-(x - y) ^ 2 / (2 * (ε : ℝ))) ≤ 1 := by
    -- Proof comment: the quadratic term is nonnegative and the Gaussian variance is positive.
    refine Real.exp_le_one_iff.mpr ?_
    exact div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (sq_nonneg (x - y)))
      (by positivity : 0 ≤ (2 : ℝ) * ε)
  have hcoef : 0 ≤ (Real.sqrt (2 * Real.pi * ε))⁻¹ := by
    positivity
  -- Proof comment: multiplying by the nonnegative prefactor preserves the bound.
  simpa [mul_comm, mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hexp hcoef

/-- Helper for Exercise 15.1.6: every Gaussian-smoothed density value is finite. -/
lemma gaussianSmoothedDensity_lt_top [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0)
    (x : ℝ) :
    gaussianSmoothedDensity μ ε x < ∞ := by
  -- Proof comment: dominate the kernel by the Gaussian peak and use that `μ` has total mass `1`.
  have hbound :
      gaussianSmoothedDensity μ ε x ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi * ε))⁻¹) := by
    calc
      gaussianSmoothedDensity μ ε x = ∫⁻ y, gaussianPDF y ε x ∂μ := rfl
      _ ≤ ∫⁻ y, ENNReal.ofReal ((Real.sqrt (2 * Real.pi * ε))⁻¹) ∂μ := by
        refine lintegral_mono fun y ↦ ?_
        -- Proof comment: apply the pointwise peak bound inside the nonnegative integral.
        exact ENNReal.ofReal_le_ofReal (gaussianPDFReal_le_peak (hε := hε) x y)
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * ε))⁻¹) * μ Set.univ := by
        rw [lintegral_const]
      _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi * ε))⁻¹) := by
        simp [measure_univ]
  -- Proof comment: the dominating constant is a finite `ENNReal`, so the smoothed density is too.
  exact lt_of_le_of_lt hbound <| by
    simpa using
      (ENNReal.ofReal_lt_top : ENNReal.ofReal ((Real.sqrt (2 * Real.pi * ε))⁻¹) < ∞)

/-- Helper for Exercise 15.1.6: the real-valued Gaussian-smoothed density is integrable. -/
lemma integrable_gaussianSmoothedDensityToReal [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0) :
    Integrable (fun x ↦ (gaussianSmoothedDensity μ ε x).toReal) := by
  -- Proof comment: the smoothed density has total mass `1`, so its `toReal` version lies in `L¹`.
  have hfinite : ∫⁻ x, gaussianSmoothedDensity μ ε x ∂volume ≠ ∞ := by
    rw [lintegral_gaussianSmoothedDensity_eq_one (μ := μ) hε]
    simp
  exact integrable_toReal_of_lintegral_ne_top
    ((measurable_gaussianSmoothedDensity (μ := μ) ε).aemeasurable) hfinite

/-- Helper for Exercise 15.1.6: the Gaussian-smoothed density is a continuous complex-valued `L¹`
function on `ℝ`. -/
lemma gaussianSmoothedDensityToReal_regular [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0) :
    Continuous (fun x ↦ ((gaussianSmoothedDensity μ ε x).toReal : ℂ)) ∧
      Integrable (fun x ↦ ((gaussianSmoothedDensity μ ε x).toReal : ℂ)) := by
  -- Proof comment: rewrite the smoothed density as an integral of the continuous Gaussian kernel
  -- against the probability measure `μ`, and then apply dominated convergence in the parameter.
  have hrepr :
      (fun x ↦ (gaussianSmoothedDensity μ ε x).toReal) = fun x ↦ ∫ y, gaussianPDFReal y ε x ∂μ := by
    ext x
    have hmeas : AEMeasurable (fun y ↦ gaussianPDF y ε x) μ := by
      -- Proof comment: the Gaussian kernel is measurable in the integration variable.
      exact (measurable_gaussianPDF_left ε x).aemeasurable
    have htop : ∀ᵐ y ∂μ, gaussianPDF y ε x < ∞ := by
      -- Proof comment: every Gaussian kernel value is a finite `ENNReal`.
      exact Filter.Eventually.of_forall fun _ ↦ gaussianPDF_lt_top
    calc
      (gaussianSmoothedDensity μ ε x).toReal = ∫ y, (gaussianPDF y ε x).toReal ∂μ := by
        rw [gaussianSmoothedDensity, MeasureTheory.integral_toReal hmeas htop]
      _ = ∫ y, gaussianPDFReal y ε x ∂μ := by
        congr with y
        rw [toReal_gaussianPDF]
  have hcontReal : Continuous (fun x ↦ (gaussianSmoothedDensity μ ε x).toReal) := by
    rw [hrepr]
    apply MeasureTheory.continuous_of_dominated
    · intro x
      -- Proof comment: each Gaussian slice is measurable as a function of the integration
      -- variable.
      exact (measurable_gaussianPDFReal_left ε x).aestronglyMeasurable
    · intro x
      -- Proof comment: the peak bound gives a single integrable dominator, independent of `x`.
      exact Filter.Eventually.of_forall fun y ↦ by
        calc
          ‖gaussianPDFReal y ε x‖ = gaussianPDFReal y ε x := by
            rw [Real.norm_of_nonneg (gaussianPDFReal_nonneg y ε x)]
          _ ≤ (Real.sqrt (2 * Real.pi * ε))⁻¹ := gaussianPDFReal_le_peak (hε := hε) x y
    · exact integrable_const ((Real.sqrt (2 * Real.pi * ε))⁻¹)
    · -- Proof comment: for each fixed center `y`, the Gaussian profile is continuous in `x`.
      exact Filter.Eventually.of_forall fun y ↦ by
        exact continuous_gaussianPDFReal_right y ε
  have hIntComplex :
      Integrable (fun x ↦ ((gaussianSmoothedDensity μ ε x).toReal : ℂ)) := by
    -- Proof comment: the complex-valued version is just the `Complex.ofReal` image of the real
    -- `L¹` density.
    simpa using (integrable_gaussianSmoothedDensityToReal (μ := μ) hε).ofReal
  refine ⟨?_, hIntComplex⟩
  -- Proof comment: continuity survives the final coercion from `ℝ` to `ℂ`.
  simpa using Complex.continuous_ofReal.comp hcontReal

/-- Helper for Exercise 15.1.6: the characteristic function of a Lebesgue `withDensity` measure
is the Fourier transform of its complexified density at the normalized frequency. -/
lemma charFun_withDensity_eq_fourierToReal {f : ℝ → ℝ≥0∞}
    (hf_meas : AEMeasurable f volume) (hf_lt_top : ∀ᵐ x ∂volume, f x < ∞) :
    charFun (volume.withDensity f) =
      fun t : ℝ ↦ 𝓕 (fun x : ℝ ↦ ((f x).toReal : ℂ)) (-(2 * Real.pi)⁻¹ * t) := by
  ext t
  -- Proof comment: rewrite the characteristic function integral against `withDensity`,
  -- then recognize the resulting oscillatory integral as the real Fourier transform.
  rw [MeasureTheory.charFun_apply_real]
  rw [integral_withDensity_eq_integral_toReal_smul₀
    (μ := volume) (f := f) hf_meas hf_lt_top]
  simpa [Real.fourier_eq, smul_eq_mul, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (Real.fourier_real_eq_integral_exp_smul (fun x : ℝ ↦ ((f x).toReal : ℂ))
      (-(2 * Real.pi)⁻¹ * t)).symm

/-- Helper for Exercise 15.1.6: for a nonnegative real density, the preceding Fourier rewrite can
be stated directly in terms of the original real-valued function. -/
lemma charFun_withDensity_ofReal_eq_fourier
    {f : ℝ → ℝ} (hf_nonneg : ∀ x, 0 ≤ f x) (hf_int : Integrable f) :
    charFun (volume.withDensity (ENNReal.ofReal ∘ f)) =
      fun t : ℝ ↦ 𝓕 (fun x : ℝ ↦ ((f x : ℝ) : ℂ)) (-(2 * Real.pi)⁻¹ * t) := by
  have hf_aemeas : AEMeasurable (ENNReal.ofReal ∘ f) volume := by
    -- Proof comment: integrable functions are almost everywhere strongly measurable, so applying
    -- `ENNReal.ofReal` preserves the measurability needed for `withDensity`.
    exact hf_int.aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hf_lt_top : ∀ᵐ x ∂volume, (ENNReal.ofReal (f x)) < ∞ := by
    -- Proof comment: every `ENNReal.ofReal` value is finite.
    exact Filter.Eventually.of_forall fun _ ↦ by simp
  -- Proof comment: after rewriting the `withDensity` characteristic function on the ENNReal side,
  -- nonnegativity identifies the `toReal` density with the original real-valued function.
  rw [charFun_withDensity_eq_fourierToReal (hf_meas := hf_aemeas) (hf_lt_top := hf_lt_top)]
  have htoReal :
      (fun x : ℝ ↦ ((((ENNReal.ofReal ∘ f) x).toReal : ℝ) : ℂ)) =
        fun x : ℝ ↦ ((f x : ℝ) : ℂ) := by
    funext x
    simp [ENNReal.toReal_ofReal (hf_nonneg x)]
  ext t
  simpa using congrArg (fun h : ℝ → ℂ => 𝓕 h (-(2 * Real.pi)⁻¹ * t)) htoReal

/-- Helper for Exercise 15.1.6: Gaussian damping makes the rescaled characteristic function
integrable on the Fourier side. -/
lemma integrable_dampedScaledCharFun [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0) :
    Integrable (fun s : ℝ ↦ charFun μ (-2 * Real.pi * s) *
      Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))) := by
  let g : ℝ → ℂ := fun s ↦ Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))
  have hεposNN : 0 < ε := by
    exact pos_iff_ne_zero.mpr hε
  have hεpos : 0 < (ε : ℝ) := by
    exact_mod_cast hεposNN
  have hg : Integrable g := by
    -- Proof comment: a strictly positive Gaussian exponent gives an `L¹` complex Gaussian.
    have hbreal : 0 < 2 * Real.pi ^ 2 * (ε : ℝ) := by
      positivity
    have hgReal :
        Integrable (fun s : ℝ ↦ Real.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))) := by
      simpa using integrable_exp_neg_mul_sq hbreal
    simpa [g, Complex.ofReal_exp] using
      (hgReal.ofReal :
        Integrable
          (fun s : ℝ ↦
            (((Real.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))) : ℝ) : ℂ))
          volume)
  refine Integrable.mono' hg.norm ?_ ?_
  · -- Proof comment: the damped characteristic function is measurable as a product of measurable
    -- factors.
    fun_prop
  · -- Proof comment: `‖charFun μ‖ ≤ 1`, so the Gaussian factor is a pointwise `L¹` majorant.
    filter_upwards with s
    have hchar_norm : ‖charFun μ (-2 * Real.pi * s)‖ ≤ 1 :=
      norm_charFun_le_one (μ := μ) (-2 * Real.pi * s)
    calc
      ‖charFun μ (-2 * Real.pi * s) * Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))‖
          = ‖charFun μ (-2 * Real.pi * s)‖ * ‖g s‖ := by
              simp [g]
      _ ≤ 1 * ‖g s‖ := by
              exact mul_le_mul_of_nonneg_right hchar_norm (norm_nonneg _)
      _ = ‖g s‖ := by ring

/-- Helper for Exercise 15.1.6: the complexified Gaussian-smoothed density is the inverse Fourier
transform of the Gaussian-damped rescaled characteristic function. -/
lemma gaussianSmoothedDensityToComplex_eq_fourierInv_dampedScaledCharFun
    [IsProbabilityMeasure μ] {ε : ℝ≥0} (hε : ε ≠ 0) :
    (fun x : ℝ ↦ ((gaussianSmoothedDensity μ ε x).toReal : ℂ)) =
      𝓕⁻ (fun s : ℝ ↦ charFun μ (-2 * Real.pi * s) *
        Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))) := by
  let f : ℝ → ℂ := fun x ↦ ((gaussianSmoothedDensity μ ε x).toReal : ℂ)
  have hreg := gaussianSmoothedDensityToReal_regular (μ := μ) hε
  have hcont : Continuous f := by
    -- Proof comment: reuse the regularity package already established for each Gaussian
    -- smoothing.
    simpa [f] using hreg.1
  have hint : Integrable f := by
    -- Proof comment: the same regularity package supplies the `L¹` hypothesis for Fourier
    -- inversion.
    simpa [f] using hreg.2
  have hchar :
      charFun (volume.withDensity (gaussianSmoothedDensity μ ε)) =
        fun t : ℝ ↦ 𝓕 f (-(2 * Real.pi)⁻¹ * t) := by
    -- Proof comment: the characteristic function of a `withDensity` measure is exactly the
    -- Fourier transform of the complexified density at the normalized frequency.
    simpa [f] using
      (charFun_withDensity_eq_fourierToReal (f := gaussianSmoothedDensity μ ε)
        ((measurable_gaussianSmoothedDensity (μ := μ) ε).aemeasurable)
        (Filter.Eventually.of_forall fun x ↦ gaussianSmoothedDensity_lt_top (μ := μ) hε x))
  have hfourier :
      𝓕 f =
        fun s : ℝ ↦ charFun μ (-2 * Real.pi * s) *
          Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2)) := by
    ext s
    have hs := congrFun hchar (-2 * Real.pi * s)
    have hsmoothed :=
      congrArg (fun ν : Measure ℝ => charFun ν (-2 * Real.pi * s))
        (gaussianSmoothedLaw_eq_withDensity (μ := μ) hε)
    have hs' :
        charFun (μ ∗ gaussianReal 0 ε) (-2 * Real.pi * s) =
          𝓕 f (-(2 * Real.pi)⁻¹ * (-2 * Real.pi * s)) :=
      hsmoothed.trans hs
    rw [MeasureTheory.charFun_conv, ProbabilityTheory.charFun_gaussianReal] at hs'
    -- Proof comment: evaluating at the normalized frequency `-2πs` turns the Gaussian factor
    -- into the damping term `exp (-(2π²ε)s²)`.
    have harg : -(2 * Real.pi : ℝ)⁻¹ * (-2 * Real.pi * s) = s := by
      field_simp [Real.pi_ne_zero]
    calc
      𝓕 f s = 𝓕 f (-(2 * Real.pi)⁻¹ * (-2 * Real.pi * s)) := by rw [harg]
      _ = charFun μ (-2 * Real.pi * s) *
            Complex.exp
              (↑(-2 * Real.pi * s) * ↑0 * Complex.I - ↑↑ε * ↑(-2 * Real.pi * s) ^ 2 / 2) := by
          exact hs'.symm
      _ = charFun μ (-2 * Real.pi * s) *
            Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2)) := by
          have hExpArg :
              (↑(-2 * Real.pi * s) * ↑0 * Complex.I - ↑↑ε * ↑(-2 * Real.pi * s) ^ 2 / 2 : ℂ) =
                -((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2) := by
            norm_num
            ring_nf
          rw [hExpArg]
  have hfourierInt : Integrable (𝓕 f) := by
    -- Proof comment: the previous Gaussian-damping lemma supplies the Fourier-side `L¹`
    -- assumption needed for inversion.
    rw [hfourier]
    exact integrable_dampedScaledCharFun (μ := μ) hε
  -- Proof comment: Fourier inversion now identifies the smoothed density with the inverse
  -- transform of its damped characteristic function.
  calc
    f = 𝓕⁻ (𝓕 f) := by
      symm
      exact Continuous.fourierInv_fourier_eq hcont hint hfourierInt
    _ = 𝓕⁻ (fun s : ℝ ↦ charFun μ (-2 * Real.pi * s) *
        Complex.exp (-((2 * Real.pi ^ 2 * (ε : ℝ)) * s ^ 2))) := by
          rw [hfourier]

/-- Helper for Exercise 15.1.6: the explicit Gaussian smoothing sequence converges pointwise to
the inverse Fourier transform of the rescaled characteristic function. -/
lemma gaussianSmoothedDensitySeq_tendsto_fourierInvScaledCharFun
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        ((gaussianSmoothedDensity μ ⟨((n : ℝ) + 1)⁻¹, by positivity⟩ x).toReal : ℂ))
      atTop
      (𝓝 ((𝓕⁻ fun s : ℝ ↦ charFun μ (-2 * Real.pi * s)) x)) := by
  let g : ℝ → ℂ := fun s ↦ charFun μ (-2 * Real.pi * s)
  let modulated : ℝ → ℂ :=
    fun s ↦ Complex.exp (↑(2 * Real.pi * inner ℝ s x) * Complex.I) * g s
  let εn : ℕ → ℝ≥0 := fun n ↦ ⟨((n : ℝ) + 1)⁻¹, by positivity⟩
  let cn : ℕ → ℝ := fun n ↦ (2 * Real.pi ^ 2 * (εn n : ℝ))⁻¹
  have hmodulated : Integrable modulated := by
    have hg : Integrable g := by
      simpa [g] using integrable_scaledCharFun (μ := μ) hφ
    refine Integrable.mono' hg.norm ?_ ?_
    · -- Proof comment: the oscillatory factor is measurable, so the modulated function is too.
      fun_prop
    · -- Proof comment: the modulation has unit norm, so it does not change the `L¹` majorant.
      filter_upwards with s
      simp [modulated, g, Complex.norm_exp]
  have hcn_inv : ∀ n : ℕ, (cn n)⁻¹ = 2 * Real.pi ^ 2 * (εn n : ℝ) := by
    intro n
    have hne : 2 * Real.pi ^ 2 * (εn n : ℝ) ≠ 0 := by
      have hεn : 0 < (εn n : ℝ) := by
        dsimp [εn]
        positivity
      positivity
    simp [cn]
  have hcn : Tendsto cn atTop atTop := by
    -- Proof comment: after rewriting, the Gaussian parameter grows linearly like `(n + 1)/(2π²)`.
    have hbase : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      by
        simpa [add_comm] using
          (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    have hcn_def : cn = fun n : ℕ ↦ (2 * Real.pi ^ 2 : ℝ)⁻¹ * ((n : ℝ) + 1) := by
      funext n
      have htwoPiSq : (2 * Real.pi ^ 2 : ℝ) ≠ 0 := by
        positivity
      have hn : ((n : ℝ) + 1) ≠ 0 := by
        positivity
      dsimp [cn, εn]
      field_simp [htwoPiSq, hn]
    rw [hcn_def]
    exact hbase.const_mul_atTop (by positivity : 0 < (2 * Real.pi ^ 2 : ℝ)⁻¹)
  have hgauss :
      Tendsto
        (fun n : ℕ ↦ ∫ s, Complex.exp (-(cn n)⁻¹ * ‖s‖ ^ 2) • modulated s)
        atTop
        (𝓝 (∫ s, modulated s)) :=
    (Real.tendsto_integral_cexp_sq_smul hmodulated).comp hcn
  convert hgauss using 1
  · ext n
    have hεn : εn n ≠ 0 := by
      have hεn_pos : 0 < (εn n : ℝ) := by
        dsimp [εn]
        positivity
      exact ne_of_gt hεn_pos
    have hfourier :=
      congrFun
        (gaussianSmoothedDensityToComplex_eq_fourierInv_dampedScaledCharFun (μ := μ) hεn) x
    rw [Real.fourierInv_eq'] at hfourier
    calc
      ((gaussianSmoothedDensity μ (εn n) x).toReal : ℂ)
          = ∫ s,
              Complex.exp (↑(2 * Real.pi * inner ℝ s x) * Complex.I) *
                (charFun μ (-2 * Real.pi * s) *
                  Complex.exp (-((2 * Real.pi ^ 2 * ((εn n : ℝ))) * s ^ 2))) := by
              simpa [smul_eq_mul, mul_assoc, mul_left_comm, mul_comm] using hfourier
      _ = ∫ s, Complex.exp (-(cn n)⁻¹ * ‖s‖ ^ 2) • modulated s := by
            congr with s
            have hexp :
                Complex.exp (-((2 * Real.pi ^ 2 * (εn n : ℝ)) * s ^ 2)) =
                  Complex.exp (-(cn n)⁻¹ * ‖s‖ ^ 2) := by
              have hsq : (((|s| : ℝ) : ℂ) ^ 2) = (s : ℂ) ^ 2 := by
                exact_mod_cast (sq_abs s)
              rw [Real.norm_eq_abs]
              rw [hcn_inv n, hsq]
              congr 1
              norm_num
            rw [hexp]
            simp [modulated, g, smul_eq_mul, mul_left_comm, mul_comm]
  · -- Proof comment: the limit integral is exactly the inverse Fourier transform of `g`.
    rw [Real.fourierInv_eq']
    simp [modulated, g, smul_eq_mul, mul_left_comm, mul_comm]

/-- Helper for Exercise 15.1.6: the inverse-Fourier candidate density agrees with the complex
inverse Fourier transform of the rescaled characteristic function. -/
lemma ofReal_charFunInversionDensity_eq_fourierInv_scaledCharFun
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ) volume) :
    (fun x : ℝ ↦ ((charFunInversionDensity μ x : ℝ) : ℂ)) =
      𝓕⁻ (fun s : ℝ ↦ charFun μ (-2 * Real.pi * s)) := by
  ext x
  have hseq :=
    gaussianSmoothedDensitySeq_tendsto_fourierInvScaledCharFun (μ := μ) hφ x
  have him :
      Tendsto
        (fun n : ℕ ↦
          Complex.im
            (((gaussianSmoothedDensity μ ⟨((n : ℝ) + 1)⁻¹, by positivity⟩ x).toReal : ℂ)))
        atTop
        (𝓝 (Complex.im ((𝓕⁻ fun s : ℝ ↦ charFun μ (-2 * Real.pi * s)) x))) :=
    Complex.continuous_im.continuousAt.tendsto.comp hseq
  have him_zero :
      Complex.im ((𝓕⁻ fun s : ℝ ↦ charFun μ (-2 * Real.pi * s)) x) = 0 := by
    -- Proof comment: every Gaussian-smoothed term is real-valued, so the limit has zero
    -- imaginary part as well.
    have hzero :
        Tendsto
          (fun _ : ℕ ↦ (0 : ℝ))
          atTop
          (𝓝 (Complex.im ((𝓕⁻ fun s : ℝ ↦ charFun μ (-2 * Real.pi * s)) x))) := by
      refine him.congr' ?_
      exact Filter.Eventually.of_forall fun n ↦ by simp
    exact tendsto_nhds_unique hzero tendsto_const_nhds
  have hcharNeg :
      (fun s : ℝ ↦ (starRingEnd ℂ) (charFun μ (2 * Real.pi * s))) =
        fun s : ℝ ↦ charFun μ (-2 * Real.pi * s) := by
    funext s
    calc
      (starRingEnd ℂ) (charFun μ (2 * Real.pi * s))
          = charFun μ (-(2 * Real.pi * s)) := by
              exact (MeasureTheory.charFun_neg (μ := μ) (2 * Real.pi * s)).symm
      _ = charFun μ (-2 * Real.pi * s) := by
          congr 1
          ring
  refine Complex.ext ?_ ?_
  · -- Proof comment: the real parts match by definition of `charFunInversionDensity`.
    simp [charFunInversionDensity]
  · -- Proof comment: the left-hand side is real, and the right-hand side has just been shown to
    -- be real as well.
    simpa [hcharNeg] using him_zero.symm

/-- Helper for Exercise 15.1.6: the inverse-Fourier candidate density is nonnegative and
integrable. -/
lemma charFunInversionDensity_nonneg_integrable
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ) volume) :
    (∀ x : ℝ, 0 ≤ charFunInversionDensity μ x) ∧ Integrable (charFunInversionDensity μ) := by
  let εn : ℕ → ℝ≥0 := fun n ↦ ⟨((n : ℝ) + 1)⁻¹, by positivity⟩
  let fSeq : ℕ → ℝ → ℝ := fun n x ↦ (gaussianSmoothedDensity μ (εn n) x).toReal
  have hPointwise :
      ∀ x : ℝ, Tendsto (fun n : ℕ ↦ fSeq n x) atTop (𝓝 (charFunInversionDensity μ x)) := by
    intro x
    -- Proof comment: take real parts in the complex Gaussian approximation limit.
    simpa [fSeq, εn, charFunInversionDensity] using
      (Complex.continuous_re.continuousAt.tendsto.comp
        (gaussianSmoothedDensitySeq_tendsto_fourierInvScaledCharFun (μ := μ) hφ x))
  have hNonneg : ∀ x : ℝ, 0 ≤ charFunInversionDensity μ x := by
    intro x
    -- Proof comment: each Gaussian-smoothed density is nonnegative, and `[0, ∞)` is closed.
    refine isClosed_Ici.mem_of_tendsto (hPointwise x) ?_
    exact Filter.Eventually.of_forall fun n ↦ by
      simp [fSeq]
  have hfSeqInt : ∀ n : ℕ, Integrable (fSeq n) := by
    intro n
    have hεn : εn n ≠ 0 := by
      have hεn_pos : 0 < (εn n : ℝ) := by
        dsimp [εn]
        positivity
      exact ne_of_gt hεn_pos
    -- Proof comment: each Gaussian smoothing already has an `L¹` real-valued density.
    simpa [fSeq, εn] using integrable_gaussianSmoothedDensityToReal (μ := μ) hεn
  have hfSeqNonneg : ∀ n : ℕ, 0 ≤ᵐ[volume] fSeq n := by
    intro n
    exact Filter.Eventually.of_forall fun x ↦ by
      simp [fSeq]
  have hPointwiseAe :
      ∀ᵐ x ∂volume, Tendsto (fun n : ℕ ↦ fSeq n x) atTop (𝓝 (charFunInversionDensity μ x)) :=
    Filter.Eventually.of_forall hPointwise
  have hIntegralEqOne : ∀ n : ℕ, ∫ x, fSeq n x = 1 := by
    intro n
    have hεn : εn n ≠ 0 := by
      have hεn_pos : 0 < (εn n : ℝ) := by
        dsimp [εn]
        positivity
      exact ne_of_gt hεn_pos
    have hmeas : AEMeasurable (gaussianSmoothedDensity μ (εn n)) := by
      exact (measurable_gaussianSmoothedDensity (μ := μ) (ε := εn n)).aemeasurable
    have htop :
        ∀ᵐ x ∂volume, gaussianSmoothedDensity μ (εn n) x < ∞ :=
      Filter.Eventually.of_forall fun x ↦ gaussianSmoothedDensity_lt_top (μ := μ) hεn x
    -- Proof comment: the real integral of each smoothed density is the total mass of the
    -- smoothed probability law, namely `1`.
    calc
      ∫ x, fSeq n x = (∫⁻ x, gaussianSmoothedDensity μ (εn n) x ∂volume).toReal := by
        simp [fSeq, MeasureTheory.integral_toReal hmeas htop]
      _ = 1 := by
        rw [lintegral_gaussianSmoothedDensity_eq_one (μ := μ) hεn]
        norm_num
  have hIntegralTendsto :
      Tendsto (fun n : ℕ ↦ ∫ x, fSeq n x) atTop (𝓝 (1 : ℝ)) := by
    -- Proof comment: the smoothed densities all have mass `1`, so their integrals are constant.
    refine Tendsto.congr' ?_ tendsto_const_nhds
    exact Filter.Eventually.of_forall fun n ↦ (hIntegralEqOne n).symm
  have hAestrong :
      AEStronglyMeasurable (charFunInversionDensity μ) volume :=
    aestronglyMeasurable_of_tendsto_ae atTop
      (fun n ↦ (hfSeqInt n).aestronglyMeasurable) hPointwiseAe
  have hLintegralNeTop :
      ∫⁻ x, ENNReal.ofReal (charFunInversionDensity μ x) ∂volume ≠ ⊤ :=
    lintegral_ofReal_limit_ne_top hfSeqInt hfSeqNonneg hPointwiseAe hIntegralTendsto
  have hIntegrable : Integrable (charFunInversionDensity μ) := by
    -- Proof comment: Fatou upgrades the pointwise limit of the mass-one Gaussian densities to a
    -- genuine `L¹` density.
    exact
      (lintegral_ofReal_ne_top_iff_integrable hAestrong
        (Filter.Eventually.of_forall hNonneg)).1 hLintegralNeTop
  exact ⟨hNonneg, hIntegrable⟩

-- Proof sketch: first compute the inverse-Fourier density for the Gaussian mollifiers
-- `gaussianReal 0 ε`; then identify the densities of `μ ∗ gaussianReal 0 ε` by Fourier inversion
-- and pass to the limit as `ε → 0`.
/-- Exercise 15.1.6: if a probability measure on `ℝ` has integrable characteristic function, then
it is absolutely continuous with respect to Lebesgue measure, with density given by the inverse
Fourier transform of its characteristic function. -/
theorem probabilityMeasure_eq_withDensity_of_integrable_charFun
    [IsProbabilityMeasure μ] (hφ : Integrable (charFun μ) volume) :
    μ = volume.withDensity (ENNReal.ofReal ∘ charFunInversionDensity μ) := by
  let g : ℝ → ℂ := fun s ↦ charFun μ (-2 * Real.pi * s)
  rcases charFunInversionDensity_nonneg_integrable (μ := μ) hφ with ⟨hNonneg, hInt⟩
  letI : IsFiniteMeasure (volume.withDensity (ENNReal.ofReal ∘ charFunInversionDensity μ)) :=
    withDensity_charFunInversionDensity_isFinite (μ := μ) hInt
  have hgConj :
      g = fun s : ℝ ↦ (starRingEnd ℂ) (charFun μ (2 * Real.pi * s)) := by
    funext s
    dsimp [g]
    calc
      charFun μ (-2 * Real.pi * s) = charFun μ (-(2 * Real.pi * s)) := by
        congr 1
        ring
      _ = (starRingEnd ℂ) (charFun μ (2 * Real.pi * s)) := by
          exact MeasureTheory.charFun_neg (μ := μ) (2 * Real.pi * s)
  have hgCont : Continuous g := by
    -- Proof comment: the rescaled characteristic function inherits continuity from `charFun μ`.
    have hscale : Continuous (fun s : ℝ ↦ 2 * Real.pi * s) := by
      continuity
    rw [hgConj]
    exact Continuous.star <| (MeasureTheory.continuous_charFun (μ := μ)).comp hscale
  have hgInt : Integrable g := by
    -- Proof comment: the Fourier-side input is the fixed rescaling of the integrable
    -- characteristic function.
    simpa [g] using integrable_scaledCharFun (μ := μ) hφ
  have hFourierg :
      𝓕 g = fun x : ℝ ↦ ((charFunInversionDensity μ (-x) : ℝ) : ℂ) := by
    ext x
    have hInv :=
      congrFun (ofReal_charFunInversionDensity_eq_fourierInv_scaledCharFun (μ := μ) hφ) (-x)
    rw [Real.fourierInv_eq_fourier_neg] at hInv
    rw [hgConj]
    simpa using hInv.symm
  have hFourierInt : Integrable (𝓕 g) := by
    rw [hFourierg]
    have hOfRealNeg :
        Integrable (fun x : ℝ ↦ ((charFunInversionDensity μ (-x) : ℝ) : ℂ)) := by
      simpa using hInt.comp_neg.ofReal
    simpa using hOfRealNeg
  -- Proof comment: compare the two finite measures by their characteristic functions, then use
  -- Fourier inversion on the rescaled characteristic function `g`.
  refine Measure.ext_of_charFun ?_
  funext t
  rw [charFun_withDensity_ofReal_eq_fourier hNonneg hInt]
  rw [ofReal_charFunInversionDensity_eq_fourierInv_scaledCharFun (μ := μ) hφ]
  have hFourierInv := Continuous.fourier_fourierInv_eq hgCont hgInt hFourierInt
  simpa [g, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using
    (congrFun hFourierInv (-(2 * Real.pi)⁻¹ * t)).symm

-- Proof sketch: apply dominated convergence to the oscillatory integral defining
-- `charFunInversionDensity μ`, using the `L¹` majorant `t ↦ ‖charFun μ t‖`.
/-- The inverse-Fourier density attached to an integrable characteristic function is continuous. -/
theorem charFunInversionDensity_continuous
    (hφ : Integrable (charFun μ) volume) :
    Continuous (charFunInversionDensity μ) := by
  -- Rewrite the inverse transform as an ordinary Fourier transform of a rescaled
  -- characteristic function so the standard continuity theorem applies.
  let g : ℝ → ℂ := fun t ↦ charFun μ (-2 * Real.pi * t)
  have hscaled : Integrable g := by
    simpa [g] using integrable_scaledCharFun μ hφ
  have hfourier : Continuous (𝓕 g) := by
    simpa [Real.fourier_eq] using
      (VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (innerSL ℝ).continuous₂ hscaled)
  -- Taking real parts preserves continuity and matches the definition of
  -- `charFunInversionDensity μ` after simplifying the sign change in `𝓕⁻`.
  have hrepr := charFunInversionDensity_eq_re_fourier_scaledCharFun μ
  rw [hrepr]
  exact Complex.continuous_re.comp (hfourier.comp continuous_neg)

-- Proof sketch: bound the oscillatory integral uniformly by the `L¹` norm of the characteristic
-- function.
/-- The inverse-Fourier density is pointwise bounded by the `L¹` norm of the characteristic
function. -/
theorem norm_charFunInversionDensity_le_integral_norm
    (hφ : Integrable (charFun μ) volume) (x : ℝ) :
    ‖charFunInversionDensity μ x‖ ≤ ∫ t, ‖charFun μ t‖ := by
  let g : ℝ → ℂ := fun t ↦ charFun μ (-2 * Real.pi * t)
  have hgInt : Integrable g := by
    simpa [g] using integrable_scaledCharFun μ hφ
  rw [charFunInversionDensity_eq_re_fourier_scaledCharFun]
  -- Proof comment: first bound the real part by the complex norm of the Fourier transform.
  refine (RCLike.norm_re_le_norm ((𝓕 g) (-x))).trans ?_
  calc
    ‖𝓕 g (-x)‖ ≤ ∫ t, ‖g t‖ := by
      -- Proof comment: the Fourier transform is uniformly bounded by the `L¹` norm of its input.
      rw [Real.fourier_eq]
      refine (norm_integral_le_integral_norm
        (f := fun t : ℝ ↦ Real.fourierChar (-inner ℝ t (-x)) • g t)).trans ?_
      have hnorm :
          (fun t : ℝ ↦ ‖Real.fourierChar (-inner ℝ t (-x)) • g t‖) = fun t : ℝ ↦ ‖g t‖ := by
        funext t
        simp [Circle.norm_smul]
      rw [hnorm]
    _ = |(-2 * Real.pi : ℝ)⁻¹| * ∫ t, ‖charFun μ t‖ := by
      -- Proof comment: rescaling the frequency variable contributes the Jacobian factor
      -- `|(-2π)⁻¹|`.
      change ∫ t, ‖charFun μ (-2 * Real.pi * t)‖ =
        |(-2 * Real.pi : ℝ)⁻¹| * ∫ t, ‖charFun μ t‖
      simpa using
        (MeasureTheory.Measure.integral_comp_mul_left
          (g := fun t : ℝ ↦ ‖charFun μ t‖) (-2 * Real.pi))
    _ ≤ ∫ t, ‖charFun μ t‖ := by
      -- Proof comment: the Jacobian factor is at most `1`, so the rescaled `L¹` norm is bounded
      -- by the original one.
      have hcoeff : |(-2 * Real.pi : ℝ)⁻¹| ≤ 1 := by
        have h2pi : (1 : ℝ) ≤ 2 * Real.pi := by
          linarith [Real.pi_gt_three]
        have hinv : (2 * Real.pi : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2pi
        simpa [abs_inv, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
          abs_of_pos Real.pi_pos] using hinv
      have hnonneg : 0 ≤ ∫ t, ‖charFun μ t‖ := by
        exact integral_nonneg fun t ↦ norm_nonneg _
      simpa using mul_le_mul_of_nonneg_right hcoeff hnonneg

-- Proof sketch: apply `norm_charFunInversionDensity_le_integral_norm` uniformly in `x`.
/-- The inverse-Fourier density attached to an integrable characteristic function is bounded. -/
theorem charFunInversionDensity_bounded
    (hφ : Integrable (charFun μ) volume) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, ‖charFunInversionDensity μ x‖ ≤ C := by
  refine ⟨∫ t, ‖charFun μ t‖, ?_, ?_⟩
  · -- Proof comment: the `L¹` norm of the characteristic function is nonnegative.
    exact integral_nonneg fun t ↦ norm_nonneg _
  · -- Proof comment: reuse the pointwise norm estimate with a constant independent of `x`.
    intro x
    exact norm_charFunInversionDensity_le_integral_norm (μ := μ) hφ x

end
