/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Theorem_3_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Corollary_15_32
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Example_15_5

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

noncomputable section

/- Recall for Example 15.33, item (i): the Gaussian law `N_{μ,σ²}` has moment-generating
function `t ↦ exp (μ t + σ² t² / 2)`. -/
recall ProbabilityTheory.mgf_id_gaussianReal

/-- Helper for Example 15.33: a Gaussian law has finite exponential moments of `|x|` at every
real rate. -/
lemma gaussianRealIntegrableExpAbs (μ : ℝ) (σ2 : NNReal) (t : ℝ) :
    Integrable (fun x : ℝ ↦ Real.exp (|t| * |x|)) (gaussianReal μ σ2) := by
  -- Proof comment: combine the explicit Gaussian exponential moments at `t` and `-t`, then
  -- convert the two one-sided bounds into the absolute-value exponential bound.
  exact ProbabilityTheory.integrable_exp_abs_mul_abs
    (μ := gaussianReal μ σ2) (X := id) (t := t)
    (by simpa using ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := μ) (v := σ2) t)
    (by simpa using ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := μ) (v := σ2) (-t))

-- Proof sketch: combine the explicit Gaussian moment-generating function with Corollary 15.32 to
-- put the source statement into the chapter's canonical owner abstraction
-- `Measure.IsMomentDeterminate`.
/-- Gaussian case of Example 15.33 (1): item (i). A Gaussian law on `ℝ` is moment determinate. -/
theorem isMomentDeterminate_gaussianReal (μ : ℝ) (σ2 : NNReal) :
    Measure.IsMomentDeterminate (gaussianReal μ σ2) := by
  -- Proof comment: Corollary 15.32 applies once we supply one strictly positive exponential
  -- moment for `|x|`; for Gaussians the helper gives this immediately at `t = 1`.
  have hExp : Integrable (fun x : ℝ ↦ Real.exp (1 * |x|)) (gaussianReal μ σ2) := by
    simpa using gaussianRealIntegrableExpAbs μ σ2 1
  exact
    (method_of_moments_of_integrable_exp_abs (μ := gaussianReal μ σ2) zero_lt_one hExp).2

/-- Companion corollary: equality of all moments identifies a Gaussian law. -/
theorem gaussianReal_eq_of_forall_moment_eq
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (μ : ℝ) (σ2 : NNReal)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_mom : ∀ n : ℕ, moment id n ν = moment id n (gaussianReal μ σ2)) :
    ν = gaussianReal μ σ2 := by
  symm
  exact Measure.IsMomentDeterminate.eq_of_forall_moment_eq
    (μ := gaussianReal μ σ2) (ν := ν) (isMomentDeterminate_gaussianReal μ σ2) hν_moments
    (fun n ↦ (h_mom n).symm)

-- Proof sketch: the Gaussian exponential integrability set is all of `ℝ`, so
-- `analyticOn_complexMGF` applies on the whole complex plane to the complex mgf
-- `z ↦ exp (μ z + σ² z² / 2)`. Restricting to the imaginary axis recovers the analytic
-- characteristic function.
/-- Gaussian case of Example 15.33 (2): item (i). The characteristic function of a Gaussian law is
analytic on `ℝ`. -/
theorem gaussianReal_charFun_analytic (μ : ℝ) (σ2 : NNReal) :
    AnalyticOn ℝ (charFun (gaussianReal μ σ2)) Set.univ := by
  -- Proof comment: the same exponential-integrability input used for moment determinacy gives the
  -- analytic characteristic-function conclusion from Corollary 15.32.
  have hExp : Integrable (fun x : ℝ ↦ Real.exp (1 * |x|)) (gaussianReal μ σ2) := by
    simpa using gaussianRealIntegrableExpAbs μ σ2 1
  exact
    (method_of_moments_of_integrable_exp_abs (μ := gaussianReal μ σ2) zero_lt_one hExp).1

/-- Companion theorem: the complex moment-generating function of a Gaussian law is entire. -/
theorem gaussianReal_complexMGF_entire (μ : ℝ) (σ2 : NNReal) :
    AnalyticOn ℂ (complexMGF id (gaussianReal μ σ2)) Set.univ := by
  -- Proof comment: for Gaussian laws the real integrability strip is all of `ℝ`, so the general
  -- analyticity theorem for the complex mgf upgrades directly to an entire-function statement.
  simpa using
    (ProbabilityTheory.analyticOn_complexMGF (X := id) (μ := gaussianReal μ σ2))

/-- Helper for Example 15.33: rewrite integration against `expMeasure θ` as integration against
its real-valued density, viewed as a complex scalar factor. -/
private theorem integralExpMeasure_eq_integral_density {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℂ} :
    ∫ x, f x ∂expMeasure θ = ∫ x, (exponentialPDFReal θ x : ℂ) * f x := by
  -- Proof comment: expand `expMeasure` as a `withDensity` measure and rewrite the density as a
  -- complex-valued scalar multiplier.
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := gammaPDF 1 θ)
      (measurable_gammaPDFReal 1 θ).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [gammaPDF, exponentialPDFReal, gammaPDFReal_nonneg zero_lt_one hθ x]
  rfl

/-- Helper for Example 15.33: the exponential law of rate `θ` is supported on `[0, ∞)` almost
everywhere. -/
private theorem aeNonnegExpMeasure {θ : ℝ} (hθ : 0 < θ) :
    ∀ᵐ x ∂expMeasure θ, 0 ≤ x := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hIic0_real : (expMeasure θ).real (Set.Iic 0) = 0 := by
    rw [
      ← ProbabilityTheory.cdf_eq_real (μ := expMeasure θ) 0,
      ProbabilityTheory.cdf_expMeasure_eq hθ 0
    ]
    simp
  have hIic0 : expMeasure θ (Set.Iic 0) = 0 := by
    rw [MeasureTheory.Measure.real_def] at hIic0_real
    exact ((ENNReal.toReal_eq_zero_iff _).1 hIic0_real).resolve_right (measure_ne_top _ _)
  have hIio0 : expMeasure θ (Set.Iio 0) = 0 := by
    refine MeasureTheory.measure_mono_null (μ := expMeasure θ) ?_ hIic0
    intro x hx
    exact le_of_lt (show x < 0 from hx)
  -- Proof comment: the bad set is exactly `Iio 0`, whose mass vanishes by the cdf formula at `0`.
  rw [ae_iff]
  simpa [not_le] using hIio0

/-- Helper for Example 15.33: normalize the exponential density kernel to the `Ici 0` indicator
form used by the improper-integral API. -/
private lemma expMeasureDensityKernel_eq_indicator (θ : ℝ) (z : ℂ) (x : ℝ) :
    (exponentialPDFReal θ x : ℂ) * Complex.exp (z * x) =
      Set.indicator (Set.Ici (0 : ℝ))
        (fun y : ℝ ↦ (θ : ℂ) * Complex.exp ((z - θ) * y)) x := by
  by_cases hx : 0 ≤ x
  · -- Proof comment: on the support, merge the density and exponential factor into one exponent.
    calc
      (exponentialPDFReal θ x : ℂ) * Complex.exp (z * x)
          = (((θ : ℂ) * Complex.exp (-((θ : ℂ) * x))) * Complex.exp (z * x)) := by
              simp [exponentialPDFReal, gammaPDFReal, hx]
      _ = (θ : ℂ) * Complex.exp ((z - θ) * x) := by
            rw [mul_assoc, ← Complex.exp_add]
            congr 1
            ring
      _ = Set.indicator (Set.Ici (0 : ℝ))
            (fun y : ℝ ↦ (θ : ℂ) * Complex.exp ((z - θ) * y)) x := by
            simp [hx]
  · -- Proof comment: off the support `Ici 0`, the exponential density vanishes identically.
    calc
      (exponentialPDFReal θ x : ℂ) * Complex.exp (z * x) = 0 := by
          simp [exponentialPDFReal, gammaPDFReal, hx]
      _ = Set.indicator (Set.Ici (0 : ℝ))
            (fun y : ℝ ↦ (θ : ℂ) * Complex.exp ((z - θ) * y)) x := by
            simp [hx]

/-- Helper for Example 15.33: normalize the reciprocal from `z - θ` to `θ - z` in the complex
exponential-law formula. -/
private lemma complexReciprocalSub_eq {θ : ℝ} {z : ℂ} (hz : z.re < θ) :
    (-(1 : ℂ)) / (z - θ) = 1 / ((θ : ℂ) - z) := by
  have hz_ne : z - (θ : ℂ) ≠ 0 := by
    intro hz0
    have hre : z.re - θ = 0 := by
      simpa [Complex.sub_re] using congrArg Complex.re hz0
    linarith
  have hneg_ne : -((z - (θ : ℂ))) ≠ 0 := neg_ne_zero.mpr hz_ne
  -- Proof comment: `θ - z` is exactly the negation of `z - θ`, so the reciprocal changes sign.
  rw [show ((θ : ℂ) - z) = -(z - θ) by ring]
  field_simp [hz_ne, hneg_ne]

/-- Helper for Example 15.33: the complex moment-generating function of `expMeasure θ` is the
textbook rational function on the half-plane `Re z < θ`. -/
private theorem expMeasure_complexMGF_formula (θ : ℝ) (hθ : 0 < θ) {z : ℂ} (hz : z.re < θ) :
    complexMGF id (expMeasure θ) z = (θ : ℂ) / ((θ : ℂ) - z) := by
  have hneg : (z - θ).re < 0 := by
    simpa [Complex.sub_re] using sub_lt_zero.mpr hz
  rw [ProbabilityTheory.complexMGF, integralExpMeasure_eq_integral_density hθ]
  calc
    ∫ x, (exponentialPDFReal θ x : ℂ) * Complex.exp (z * x)
        = ∫ x,
            Set.indicator (Set.Ici (0 : ℝ))
              (fun y : ℝ ↦ (θ : ℂ) * Complex.exp ((z - θ) * y)) x := by
            -- Proof comment: rewrite the density kernel into the `Ici`-indicator normal form.
            refine integral_congr_ae ?_
            filter_upwards with x
            exact expMeasureDensityKernel_eq_indicator θ z x
    _ = ∫ x in Set.Ici (0 : ℝ), (θ : ℂ) * Complex.exp ((z - θ) * x) := by
          rw [integral_indicator measurableSet_Ici]
    _ = ∫ x in Set.Ioi (0 : ℝ), (θ : ℂ) * Complex.exp ((z - θ) * x) := by
          rw [integral_Ici_eq_integral_Ioi]
    _ = (θ : ℂ) * ∫ x in Set.Ioi (0 : ℝ), Complex.exp ((z - θ) * x) := by
          simpa using
            (integral_const_mul (μ := volume.restrict (Set.Ioi (0 : ℝ))) (θ : ℂ)
              (fun x : ℝ ↦ Complex.exp ((z - θ) * x)))
    _ = (θ : ℂ) * (-Complex.exp ((z - θ) * 0) / (z - θ)) := by
          simpa using congrArg ((θ : ℂ) * ·) (integral_exp_mul_complex_Ioi hneg 0)
    _ = (θ : ℂ) / ((θ : ℂ) - z) := by
          -- Proof comment: the improper integral contributes exactly the reciprocal
          -- `1 / (θ - z)` after the explicit sign normalization.
          rw [mul_zero, Complex.exp_zero, complexReciprocalSub_eq hz, mul_one_div]

/-- Helper for Example 15.33: the exponential law has an integrable exponential moment of `|x|`
at the half-rate `θ / 2`. -/
private theorem expMeasure_integrableExpAbs_halfRate (θ : ℝ) (hθ : 0 < θ) :
    Integrable (fun x : ℝ ↦ Real.exp ((θ / 2) * |x|)) (expMeasure θ) := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hcomplex :
      complexMGF id (expMeasure θ) (θ / 2 : ℂ) = (θ : ℂ) / ((θ : ℂ) - θ / 2) :=
    expMeasure_complexMGF_formula θ hθ (z := (θ / 2 : ℂ)) (by simp [hθ])
  have hcomplex' :
      complexMGF id (expMeasure θ) (θ / 2 : ℝ) = (θ : ℂ) / ((θ : ℂ) - θ / 2) := by
    simpa using hcomplex
  have hmgf : mgf id (expMeasure θ) (θ / 2) = θ / (θ - θ / 2) := by
    rw [ProbabilityTheory.complexMGF_ofReal] at hcomplex'
    exact Complex.ofReal_injective <| by simpa using hcomplex'
  have hmgf_pos : 0 < mgf id (expMeasure θ) (θ / 2) := by
    rw [hmgf]
    have hden : 0 < θ - θ / 2 := by linarith
    exact div_pos hθ hden
  have hInt :
      Integrable (fun x : ℝ ↦ Real.exp ((θ / 2) * x)) (expMeasure θ) :=
    (mgf_pos_iff).1 hmgf_pos
  -- Proof comment: on the support of `expMeasure θ`, we have `|x| = x`, so the absolute-value
  -- exponential reduces to the ordinary exponential moment.
  refine hInt.congr ?_
  filter_upwards [aeNonnegExpMeasure hθ] with x hx
  rw [abs_of_nonneg hx]

/-- Helper for Example 15.33: the boundary rate `θ` does not belong to
`integrableExpSet id (expMeasure θ)`. -/
private theorem expMeasure_boundary_not_mem_integrableExpSet (θ : ℝ) (hθ : 0 < θ) :
    θ ∉ integrableExpSet id (expMeasure θ) := by
  intro hθ_mem
  have hDensityInt :
      Integrable (fun x : ℝ ↦ Real.exp (θ * x) * (gammaPDF 1 θ x).toReal) volume := by
    rw [expMeasure, gammaMeasure] at hθ_mem
    exact
      (integrable_withDensity_iff (μ := volume)
        (f := gammaPDF 1 θ)
        (hf := (measurable_gammaPDFReal 1 θ).ennreal_ofReal)
        (hflt := ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)).1 hθ_mem
  have hIndicatorInt : Integrable (Set.indicator (Set.Ici (0 : ℝ)) (fun _ : ℝ ↦ θ)) volume := by
    refine hDensityInt.congr ?_
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · have hpdf : (gammaPDF 1 θ x).toReal = θ * Real.exp (-(θ * x)) := by
        have hgamma_nonneg :
            0 ≤ θ ^ (1 : ℝ) / Real.Gamma 1 * x ^ (1 - 1) * Real.exp (-(θ * x)) := by
          positivity
        simpa [gammaPDF, gammaPDFReal, hx, Real.Gamma_one] using
          (ENNReal.toReal_ofReal hgamma_nonneg)
      -- Proof comment: on the support `Ici 0`, the exponential weight exactly cancels the decay
      -- of the density, leaving the constant function `θ`.
      rw [hpdf]
      calc
        Real.exp (θ * x) * (θ * Real.exp (-(θ * x)))
            = θ * (Real.exp (θ * x) * Real.exp (-(θ * x))) := by ring
        _ = θ * Real.exp 0 := by
              rw [← Real.exp_add]
              congr 1
              ring
        _ = Set.indicator (Set.Ici (0 : ℝ)) (fun _ : ℝ ↦ θ) x := by
              simp [hx]
    · simp [gammaPDF, gammaPDFReal, hx]
  have hConstInt : IntegrableOn (fun _ : ℝ ↦ θ) (Set.Ici (0 : ℝ)) volume := by
    simpa [integrable_indicator_iff measurableSet_Ici] using hIndicatorInt
  have hFinite : volume (Set.Ici (0 : ℝ)) < ∞ := by
    have hConstIff :=
      (integrableOn_const_iff (show ‖θ‖ₑ ≠ ∞ by finiteness)
        (μ := volume) (s := Set.Ici (0 : ℝ)) (C := θ)).1 hConstInt
    rcases hConstIff with hzero | hfinite
    · exact (hθ.ne' <| by simpa using hzero).elim
    · exact hfinite
  simp [Real.volume_Ici] at hFinite

-- Proof sketch: evaluate the exponential-density integral explicitly on `(0, ∞)`, which is
-- the standard geometric-series integral after the substitution `u = (θ - t) x`.
/-- Exponential case of Example 15.33 (3): item (ii). For the exponential law with rate `θ > 0`,
the moment-generating function is `t ↦ θ / (θ - t)` on `(-∞, θ)`. -/
theorem expMeasure_mgf_eq (θ : ℝ) (hθ : 0 < θ) {t : ℝ} (ht : t < θ) :
    mgf id (expMeasure θ) t = θ / (θ - t) := by
  -- Proof comment: specialize the complex half-plane formula to the real parameter `t`.
  exact Complex.ofReal_injective <| by
    simpa [ProbabilityTheory.complexMGF_ofReal] using
      (expMeasure_complexMGF_formula θ hθ (z := (t : ℂ)) (by simpa using ht))

-- Proof sketch: the explicit mgf on `(-∞, θ)` supplies the exponential integrability input for
-- Corollary 15.32, so the textbook uniqueness statement is best expressed via
-- `Measure.IsMomentDeterminate`.
/-- Exponential case of Example 15.33 (4): item (ii). The exponential law with rate `θ > 0` is
moment determinate. -/
theorem isMomentDeterminate_expMeasure (θ : ℝ) (hθ : 0 < θ) :
    Measure.IsMomentDeterminate (expMeasure θ) := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  -- Proof comment: the half-rate exponential moment of `|x|` feeds directly into Corollary 15.32.
  exact
    (method_of_moments_of_integrable_exp_abs
      (μ := expMeasure θ) (by linarith) (expMeasure_integrableExpAbs_halfRate θ hθ)).2

/-- Companion corollary: equality of all moments identifies the exponential law of rate `θ`. -/
theorem expMeasure_eq_of_forall_moment_eq
    {ν : Measure ℝ} [IsProbabilityMeasure ν] (θ : ℝ) (hθ : 0 < θ)
    (hν_moments : ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) ν)
    (h_mom : ∀ n : ℕ, moment id n ν = moment id n (expMeasure θ)) :
    ν = expMeasure θ := by
  symm
  exact Measure.IsMomentDeterminate.eq_of_forall_moment_eq
    (μ := expMeasure θ) (ν := ν) (isMomentDeterminate_expMeasure θ hθ) hν_moments
    (fun n ↦ (h_mom n).symm)

-- Proof sketch: compute the complex mgf on the open half-plane `Re z < θ` by the same density
-- integral as in the real case, now with complex parameter `z`. The resulting rational function is
-- holomorphic there and restricts on the imaginary axis to the textbook characteristic function.
/-- Exponential case of Example 15.33 (5): item (ii). The characteristic function of the
exponential law with rate `θ > 0` is analytic on `ℝ`. -/
theorem expMeasure_charFun_analytic (θ : ℝ) (hθ : 0 < θ) :
    AnalyticOn ℝ (charFun (expMeasure θ)) Set.univ := by
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  -- Proof comment: the same half-rate exponential integrability witness gives analyticity of the
  -- characteristic function.
  exact
    (method_of_moments_of_integrable_exp_abs
      (μ := expMeasure θ) (by linarith) (expMeasure_integrableExpAbs_halfRate θ hθ)).1

/-- Companion theorem: the complex moment-generating function of the exponential law of rate `θ`
is `z ↦ θ / (θ - z)` on the half-plane `Re z < θ`. -/
theorem expMeasure_complexMGF_eq (θ : ℝ) (hθ : 0 < θ) {z : ℂ} (hz : z.re < θ) :
    complexMGF id (expMeasure θ) z = (θ : ℂ) / ((θ : ℂ) - z) := by
  -- Proof comment: expose the shared density-normalized formula as the public theorem.
  exact expMeasure_complexMGF_formula θ hθ hz

-- Proof sketch: once `t ≥ θ`, the density representation reduces to the divergent integral of
-- `exp (-(θ - t) x)` over `[0, ∞)`, so the defining exponential moment cannot be integrable.
/-- Exponential case of Example 15.33 (6): item (ii). For the exponential law with rate `θ > 0`,
the exponential moment at `t` is infinite whenever `t ≥ θ`. -/
theorem expMeasure_not_mem_integrableExpSet_of_ge (θ : ℝ) (hθ : 0 < θ) {t : ℝ}
    (ht : θ ≤ t) :
    t ∉ integrableExpSet id (expMeasure θ) := by
  by_cases hteq : t = θ
  · simpa [hteq] using expMeasure_boundary_not_mem_integrableExpSet θ hθ
  intro ht_mem
  letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
  have hzero_mem : (0 : ℝ) ∈ integrableExpSet id (expMeasure θ) := by
    simp [integrableExpSet]
  have hconv : Convex ℝ (integrableExpSet id (expMeasure θ)) := convex_integrableExpSet
  have ht_pos : 0 < t := lt_of_lt_of_le hθ ht
  have hratio_nonneg : 0 ≤ θ / t := by positivity
  have hratio_sub_nonneg : 0 ≤ 1 - θ / t := by
    have hratio_le_one : θ / t ≤ 1 := (div_le_iff₀ ht_pos).2 (by simpa using ht)
    linarith
  have htheta_mem' :
      (θ / t) • t + (1 - θ / t) • (0 : ℝ) ∈ integrableExpSet id (expMeasure θ) :=
    hconv ht_mem hzero_mem hratio_nonneg hratio_sub_nonneg (by ring)
  have hrepr : (θ / t) • t + (1 - θ / t) • (0 : ℝ) = θ := by
    have hmul : (θ / t) * t = θ := by
      field_simp [ht_pos.ne']
    -- Proof comment: express `θ` as the convex combination of `t` and `0` with weight `θ / t`.
    calc
      (θ / t) • t + (1 - θ / t) • (0 : ℝ) = (θ / t) * t + (1 - θ / t) * 0 := by
        simp [smul_eq_mul]
      _ = θ := by simp [hmul]
  have htheta_mem : θ ∈ integrableExpSet id (expMeasure θ) := by
    rwa [hrepr] at htheta_mem'
  exact expMeasure_boundary_not_mem_integrableExpSet θ hθ htheta_mem

/- Example 15.33 (7): Item (iii). If `X = exp Y` with `Y ∼ N(0,1)`, then
`E[X^n] = exp (n² / 2)`. This is exactly the standard log-normal moment formula from
Example 15.5. -/
recall standardLogNormalMeasure_moment

/-- Helper for Example 15.33: the standard log-normal density is measurable. -/
private lemma measurable_standardLogNormalDensityReal :
    Measurable standardLogNormalDensityReal := by
  -- Proof comment: the density is the positive-branch `log` pullback of the Gaussian density,
  -- glued with `0` on the nonpositive half-line.
  refine Measurable.piecewise measurableSet_Ioi ?_ measurable_const
  simpa [standardLogNormalDensityReal] using
    ((ProbabilityTheory.measurable_gaussianPDFReal 0 1).comp Real.measurable_log).div
      measurable_id

/-- Helper for Example 15.33: the standard log-normal density is nonnegative. -/
private lemma standardLogNormalDensityReal_nonneg (x : ℝ) :
    0 ≤ standardLogNormalDensityReal x := by
  by_cases hx : 0 < x
  · -- Proof comment: on `(0, ∞)` the density is a nonnegative Gaussian factor divided by `x`.
    simp [standardLogNormalDensityReal, hx, div_nonneg,
      ProbabilityTheory.gaussianPDFReal_nonneg, le_of_lt hx]
  · -- Proof comment: on `(-∞, 0]` the density is defined to be `0`.
    simp [standardLogNormalDensityReal, hx]

/-- Helper for Example 15.33: the parameter-`1` perturbation density is measurable. -/
private lemma measurable_logNormalPerturbationDensityReal (α : Set.Icc (-1 : ℝ) 1) :
    Measurable (logNormalPerturbationDensityReal α) := by
  -- Proof comment: multiply the measurable base density by the measurable oscillatory factor.
  refine measurable_standardLogNormalDensityReal.mul ?_
  fun_prop

/-- Helper for Example 15.33: the parameter-`1` perturbation density is measurable. -/
private lemma measurable_logNormalPerturbationDensityReal_one :
    Measurable (logNormalPerturbationDensityReal ⟨1, by simp⟩) := by
  -- Proof comment: this is the special case of the general perturbation-density measurability.
  simpa using measurable_logNormalPerturbationDensityReal ⟨1, by simp⟩

/-- Helper for Example 15.33: the parameter-`1` perturbation density is pointwise bounded by
twice the standard log-normal density. -/
private lemma logNormalPerturbationDensityReal_one_nonneg_le_two_mul (x : ℝ) :
    0 ≤ logNormalPerturbationDensityReal ⟨1, by simp⟩ x ∧
      logNormalPerturbationDensityReal ⟨1, by simp⟩ x ≤
        2 * standardLogNormalDensityReal x := by
  have hbase : 0 ≤ standardLogNormalDensityReal x := standardLogNormalDensityReal_nonneg x
  have hsin :
      -1 ≤ Real.sin (2 * Real.pi * Real.log x) ∧
        Real.sin (2 * Real.pi * Real.log x) ≤ 1 := by
    exact abs_le.mp (Real.abs_sin_le_one _)
  -- Proof comment: the factor `1 + sin(2π log x)` stays in `[0, 2]`, so multiplying by the
  -- nonnegative base density preserves nonnegativity and gives the factor-two domination.
  constructor
  · rw [logNormalPerturbationDensityReal]
    nlinarith
  · rw [logNormalPerturbationDensityReal]
    nlinarith

-- Proof sketch: use the oscillatory Stieltjes family from Example 15.5. A nontrivial
-- `logNormalPerturbationMeasure α` is a second probability measure with the same moments as
-- `standardLogNormalMeasure`, so the Chapter 15 owner notion of moment determinacy fails for
-- the standard log-normal law itself.
/-- Helper for Example 15.33: on the interval
`[exp (1 / 6), exp (1 / 3)]`, the oscillatory log-normal correction is strictly positive. -/
private lemma standardLogNormalOscillationPosOnWitnessInterval
    {x : ℝ}
    (hx : x ∈ Set.Icc (Real.exp (1 / 6 : ℝ)) (Real.exp (1 / 3 : ℝ))) :
    0 < standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x) := by
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos (1 / 6 : ℝ)) hx.1
  have hlogLower : (1 / 6 : ℝ) ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    exact hx.1
  have hlogUpper : Real.log x ≤ (1 / 3 : ℝ) := by
    rw [Real.log_le_iff_le_exp hxpos]
    exact hx.2
  have hsinPos : 0 < Real.sin (2 * Real.pi * Real.log x) := by
    apply Real.sin_pos_of_mem_Ioo
    constructor
    · nlinarith [Real.pi_pos, hlogLower]
    · nlinarith [Real.pi_pos, hlogUpper]
  have hdensityPos : 0 < standardLogNormalDensityReal x := by
    rw [standardLogNormalDensityReal, if_pos hxpos]
    exact div_pos (ProbabilityTheory.gaussianPDFReal_pos 0 1 (Real.log x) one_ne_zero) hxpos
  -- Proof comment: both the base log-normal density and the sine factor are strictly positive on
  -- this witness interval, so their product is strictly positive as well.
  exact mul_pos hdensityPos hsinPos

/-- Helper for Example 15.33: the witness interval carries strictly more mass under the parameter
`1` perturbation than under the standard log-normal law. -/
private lemma logNormalPerturbationMeasure_witnessInterval_gt_standard :
    standardLogNormalMeasure (Set.Icc (Real.exp (1 / 6 : ℝ)) (Real.exp (1 / 3 : ℝ))) <
      logNormalPerturbationMeasure ⟨1, by simp⟩
        (Set.Icc (Real.exp (1 / 6 : ℝ)) (Real.exp (1 / 3 : ℝ))) := by
  let s : Set ℝ := Set.Icc (Real.exp (1 / 6 : ℝ)) (Real.exp (1 / 3 : ℝ))
  have hs : MeasurableSet s := measurableSet_Icc
  have hvol : volume s ≠ 0 := by
    have hs_pos : 0 < volume s := by
      have hexp_lt : Real.exp (1 / 6 : ℝ) < Real.exp (1 / 3 : ℝ) := by
        exact Real.exp_lt_exp.mpr (by norm_num)
      simpa [s, Real.volume_Icc] using ENNReal.ofReal_pos.mpr (sub_pos.mpr hexp_lt)
    exact hs_pos.ne'
  have hfi :
      ∫⁻ x in s, ENNReal.ofReal (standardLogNormalDensityReal x) ∂volume ≠ ∞ := by
    have hstd_apply :
        standardLogNormalMeasure s =
          ∫⁻ x in s, ENNReal.ofReal (standardLogNormalDensityReal x) ∂volume := by
      rw [standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal,
        MeasureTheory.withDensity_apply _ hs]
    rw [← hstd_apply]
    have hs_le_one : standardLogNormalMeasure s ≤ 1 := by
      calc
        standardLogNormalMeasure s ≤ standardLogNormalMeasure Set.univ :=
          MeasureTheory.measure_mono (subset_univ s)
        _ = 1 := by
              rw [standardLogNormalMeasure, Measure.map_apply (by fun_prop) MeasurableSet.univ]
              simp
    exact (lt_of_le_of_lt hs_le_one (by simp)).ne
  have hlt :
      ∀ᵐ x ∂volume,
        x ∈ s →
          ENNReal.ofReal (standardLogNormalDensityReal x) <
            ENNReal.ofReal (logNormalPerturbationDensityReal ⟨1, by simp⟩ x) := by
    filter_upwards with x hx
    have hosc : 0 < standardLogNormalDensityReal x * Real.sin (2 * Real.pi * Real.log x) :=
      standardLogNormalOscillationPosOnWitnessInterval hx
    have hbase : 0 ≤ standardLogNormalDensityReal x := standardLogNormalDensityReal_nonneg x
    have hreal :
        standardLogNormalDensityReal x <
          logNormalPerturbationDensityReal ⟨1, by simp⟩ x := by
      rw [logNormalPerturbationDensityReal]
      nlinarith
    have hpert_pos : 0 < logNormalPerturbationDensityReal ⟨1, by simp⟩ x := by
      rw [logNormalPerturbationDensityReal]
      nlinarith
    exact (ENNReal.ofReal_lt_ofReal_iff hpert_pos).2 hreal
  -- Proof comment: rewrite both measures as restricted density integrals on the fixed interval,
  -- then apply strict monotonicity to the pointwise density comparison.
  rw [standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal,
    logNormalPerturbationMeasure, MeasureTheory.withDensity_apply _ hs,
    MeasureTheory.withDensity_apply _ hs]
  exact MeasureTheory.setLIntegral_strict_mono hs hvol
    measurable_logNormalPerturbationDensityReal_one.ennreal_ofReal hfi hlt

/-- Helper for Example 15.33: the perturbation with parameter `α = 1` changes the mass of one
fixed positive interval, so it cannot equal the standard log-normal law. -/
private theorem logNormalPerturbationMeasureOne_ne_standardLogNormalMeasure :
    logNormalPerturbationMeasure ⟨1, by simp⟩ ≠ standardLogNormalMeasure := by
  intro hEq
  have hWitness := logNormalPerturbationMeasure_witnessInterval_gt_standard
  have hApply :=
    congrArg
      (fun μ : Measure ℝ ↦
        μ (Set.Icc (Real.exp (1 / 6 : ℝ)) (Real.exp (1 / 3 : ℝ)))) hEq
  exact hWitness.ne hApply.symm

/-- Log-normal case of Example 15.33 (8): item (iii). The standard log-normal law is not
determined by its moments. -/
theorem standardLogNormal_not_moment_determinate :
    ¬ Measure.IsMomentDeterminate standardLogNormalMeasure := by
  intro hdet
  let α : Set.Icc (-1 : ℝ) 1 := ⟨1, by simp⟩
  rcases logNormalPerturbationMeasure_isProbabilityMeasure_and_sameMoments α with ⟨hαprob, hαmom⟩
  have hαmoments :
      ∀ n : ℕ, Integrable (fun x : ℝ ↦ |x| ^ n) (logNormalPerturbationMeasure α) := by
    intro n
    have hstd :
        Integrable (fun x : ℝ ↦ |x| ^ n * standardLogNormalDensityReal x) volume := by
      have hstd_law :
          Integrable (fun x : ℝ ↦ |x| ^ n)
            (volume.withDensity fun x ↦ ENNReal.ofReal (standardLogNormalDensityReal x)) := by
        simpa [standardLogNormalMeasure_eq_withDensity_standardLogNormalDensityReal] using
          hdet.integrable_abs_pow n
      have hstd_raw :
          Integrable
            (fun x : ℝ ↦ |x| ^ n * (ENNReal.ofReal (standardLogNormalDensityReal x)).toReal)
            volume :=
        (MeasureTheory.integrable_withDensity_iff
          measurable_standardLogNormalDensityReal.ennreal_ofReal
          (Filter.Eventually.of_forall fun x ↦ by simp)
          (g := fun x : ℝ ↦ |x| ^ n)).1 hstd_law
      refine hstd_raw.congr ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (standardLogNormalDensityReal_nonneg x)]
    have hdom :
        Integrable (fun x : ℝ ↦ |x| ^ n * logNormalPerturbationDensityReal α x) volume := by
      have hmeas :
          AEStronglyMeasurable (fun x : ℝ ↦ |x| ^ n * logNormalPerturbationDensityReal α x)
            volume := by
        exact
          ((((measurable_id.abs).pow_const n).mul
              (measurable_logNormalPerturbationDensityReal α))).aestronglyMeasurable
      refine
        Integrable.mono' (hstd.const_mul 2) hmeas ?_
      filter_upwards with x
      rcases logNormalPerturbationDensityReal_one_nonneg_le_two_mul x with ⟨hα_nonneg, hα_le⟩
      have habs_nonneg : 0 ≤ |x| ^ n := pow_nonneg (abs_nonneg x) n
      have hleft_nonneg : 0 ≤ |x| ^ n * logNormalPerturbationDensityReal α x := by
        exact mul_nonneg habs_nonneg hα_nonneg
      have hright_nonneg : 0 ≤ 2 * (|x| ^ n * standardLogNormalDensityReal x) := by
        exact mul_nonneg (by positivity)
          (mul_nonneg habs_nonneg (standardLogNormalDensityReal_nonneg x))
      have hnorm_eq :
          ‖2 * (|x| ^ n * standardLogNormalDensityReal x)‖ =
            2 * (|x| ^ n * standardLogNormalDensityReal x) := by
        simpa [Real.norm_eq_abs] using (abs_of_nonneg hright_nonneg)
      calc
        ‖|x| ^ n * logNormalPerturbationDensityReal α x‖
            = |x| ^ n * logNormalPerturbationDensityReal α x := by
                exact abs_of_nonneg hleft_nonneg
        _ ≤ |x| ^ n * (2 * standardLogNormalDensityReal x) := by
              gcongr
        _ = 2 * (|x| ^ n * standardLogNormalDensityReal x) := by ring
        _ = ‖2 * (|x| ^ n * standardLogNormalDensityReal x)‖ := hnorm_eq.symm
        _ ≤ 2 * (|x| ^ n * standardLogNormalDensityReal x) := le_of_eq hnorm_eq
    have hdom' :
        Integrable
          (fun x : ℝ ↦ |x| ^ n * (ENNReal.ofReal (logNormalPerturbationDensityReal α x)).toReal)
          volume := by
      refine hdom.congr ?_
      filter_upwards with x
      rw [ENNReal.toReal_ofReal (logNormalPerturbationDensityReal_one_nonneg_le_two_mul x).1]
    refine
      (MeasureTheory.integrable_withDensity_iff
        measurable_logNormalPerturbationDensityReal_one.ennreal_ofReal
        (Filter.Eventually.of_forall fun x ↦ by simp)
        (g := fun x : ℝ ↦ |x| ^ n)).2 ?_
    exact hdom'
  have hEq :
      logNormalPerturbationMeasure α = standardLogNormalMeasure := by
    exact (hdet.eq_of_forall_moment_eq hαmoments (fun n ↦ (hαmom n).symm)).symm
  exact logNormalPerturbationMeasureOne_ne_standardLogNormalMeasure hEq

-- Proof sketch: compare the pgf coefficients `p n` with the moment roots and apply the
-- Cauchy--Hadamard root test. This gives the full convergence disk for the pgf power series, not
-- just one point beyond `1`.
/-- Helper for Example 15.33: the singleton mass at `n + 1`, weighted by `(n + 1) ^ (n + 1)`, is
bounded by the `(n + 1)`st moment term of the law. -/
private lemma natPmfMassMulIndexPow_leMomentTerm (p : PMF ℕ) (n : ℕ) :
    p (n + 1) * ((n + 1 : ℝ≥0∞) ^ (n + 1)) ≤
      ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure := by
  have hmono :
      ∫⁻ k, ({n + 1} : Set ℕ).indicator (fun k ↦ (k : ℝ≥0∞) ^ (n + 1)) k ∂p.toMeasure ≤
        ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure := by
    exact
      (MeasureTheory.lintegral_indicator_le
        (fun k : ℕ ↦ (k : ℝ≥0∞) ^ (n + 1)) ({n + 1} : Set ℕ)).trans
        (MeasureTheory.setLIntegral_le_lintegral _ _)
  -- Proof comment: restrict the moment integral to the singleton `{n + 1}` and evaluate that
  -- restricted integral as a constant times the singleton mass.
  calc
    p (n + 1) * ((n + 1 : ℝ≥0∞) ^ (n + 1))
        = p.toMeasure {n + 1} * ((n + 1 : ℝ≥0∞) ^ (n + 1)) := by
            rw [PMF.toMeasure_apply_singleton p (n + 1) (measurableSet_singleton _)]
    _ = ∫⁻ k, ({n + 1} : Set ℕ).indicator (fun k ↦ (k : ℝ≥0∞) ^ (n + 1)) k ∂p.toMeasure := by
          rw [MeasureTheory.lintegral_indicator (measurableSet_singleton _)]
          simp [mul_comm]
    _ ≤ ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure := hmono

/-- Helper for Example 15.33: the strict ENNReal root bound makes the `(n + 1)`st moment term
finite and bounds its real value by `A ^ (n + 1)`. -/
private lemma natPmfMomentTerm_toReal_le_pow_of_root_lt
    (p : PMF ℕ) {A : ℝ} (hA : 0 ≤ A) {n : ℕ}
    (hn :
      (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))) <
        ENNReal.ofReal A) :
    (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure).toReal ≤ A ^ (n + 1) := by
  let momentTerm : ℝ≥0∞ := ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure
  have hMoment_lt :
      momentTerm < ENNReal.ofReal (A ^ (n + 1)) := by
    -- Proof comment: raise the root bound back to the power `n + 1` to recover a direct moment
    -- bound in `ℝ≥0∞`.
    have hn' :
        momentTerm ^ ((((n + 1 : ℕ) : ℝ))⁻¹) < ENNReal.ofReal A := by
      simpa [momentTerm, one_div] using hn
    have hpow :
        momentTerm < (ENNReal.ofReal A) ^ (((n + 1 : ℕ) : ℝ)) := by
      exact
        (ENNReal.rpow_inv_lt_iff (by positivity : 0 < (((n + 1 : ℕ) : ℝ)))).1 hn'
    have hpow' : momentTerm < ENNReal.ofReal (A ^ (((n + 1 : ℕ) : ℝ))) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hA (by positivity)]
      exact hpow
    exact hpow'.trans_eq (congrArg ENNReal.ofReal (Real.rpow_natCast A (n + 1)))
  have hMoment_ne_top : momentTerm ≠ ∞ := (lt_of_lt_of_le hMoment_lt le_top).ne
  -- Proof comment: once the moment term is finite, `ENNReal.toReal` transports the bound to an
  -- ordinary real inequality.
  exact
    (ENNReal.toReal_le_toReal hMoment_ne_top ENNReal.ofReal_ne_top).2 hMoment_lt.le |>.trans_eq
      (ENNReal.toReal_ofReal (pow_nonneg hA _))

/-- Helper for Example 15.33: once the `(n + 1)`st moment term is finite, the singleton mass at
`n + 1` is bounded by that moment term after applying `ENNReal.toReal`. -/
private lemma natPmfCoeff_toReal_le_momentTermToReal
    (p : PMF ℕ) {n : ℕ}
    (hMoment_ne_top :
      (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ≠ ∞) :
    (p (n + 1)).toReal ≤
      (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure).toReal := by
  have hpow_one : (1 : ℝ≥0∞) ≤ ((n + 1 : ℝ≥0∞) ^ (n + 1)) := by
    have hbase : (1 : ℝ≥0∞) ≤ (n + 1 : ℝ≥0∞) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    exact one_le_pow₀ hbase
  have hcoeff_le :
      p (n + 1) ≤ ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure := by
    calc
      p (n + 1) = p (n + 1) * 1 := by simp
      _ ≤ p (n + 1) * ((n + 1 : ℝ≥0∞) ^ (n + 1)) := by gcongr
      _ ≤ ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure :=
        natPmfMassMulIndexPow_leMomentTerm p n
  -- Proof comment: the point mass is finite automatically for a PMF, and the hypothesis gives the
  -- required finiteness of the moment term on the right.
  exact
    (ENNReal.toReal_le_toReal (p.apply_ne_top (n + 1)) hMoment_ne_top).2 hcoeff_le

/-- Helper for Example 15.33: a strict upper bound on the `(n + 1)`st moment root yields a
direct geometric bound on the `(n + 1)`st pgf coefficient. -/
private lemma natPmfCoeffNorm_le_of_momentRoot_lt
    (p : PMF ℕ) {z : ℂ} {A : ℝ} (hA : 0 ≤ A) {n : ℕ}
    (hn :
      (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))) <
        ENNReal.ofReal A) :
    ‖(p (n + 1)).toReal * z ^ (n + 1)‖ ≤ (A * ‖z‖) ^ (n + 1) := by
  -- Route correction: the old `/ (n + 1)` target kept the proof trapped in unnecessary transport.
  -- The main theorem only needs a geometric majorant, so we compare the raw coefficient directly
  -- to the finite moment term and stay in one real/complex norm world.
  let momentTerm : ℝ≥0∞ := ∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure
  have hMoment_lt :
      momentTerm < ENNReal.ofReal (A ^ (n + 1)) := by
    -- Proof comment: the root hypothesis already gives the strict finite bound on the underlying
    -- moment term.
    have hn' :
        momentTerm ^ ((((n + 1 : ℕ) : ℝ))⁻¹) < ENNReal.ofReal A := by
      simpa [momentTerm, one_div] using hn
    have hpow :
        momentTerm < (ENNReal.ofReal A) ^ (((n + 1 : ℕ) : ℝ)) := by
      exact
        (ENNReal.rpow_inv_lt_iff (by positivity : 0 < (((n + 1 : ℕ) : ℝ)))).1 hn'
    have hpow' : momentTerm < ENNReal.ofReal (A ^ (((n + 1 : ℕ) : ℝ))) := by
      rw [← ENNReal.ofReal_rpow_of_nonneg hA (by positivity)]
      exact hpow
    exact hpow'.trans_eq (congrArg ENNReal.ofReal (Real.rpow_natCast A (n + 1)))
  have hMoment_ne_top : momentTerm ≠ ∞ := (lt_of_lt_of_le hMoment_lt le_top).ne
  have hMoment_real :
      momentTerm.toReal ≤ A ^ (n + 1) :=
    natPmfMomentTerm_toReal_le_pow_of_root_lt p hA (n := n) hn
  have hCoeff_real :
      (p (n + 1)).toReal ≤ momentTerm.toReal :=
    natPmfCoeff_toReal_le_momentTermToReal p (n := n) hMoment_ne_top
  -- Proof comment: after rewriting the complex norm as a real product, the bound is just two
  -- monotone multiplications followed by `mul_pow`.
  calc
    ‖(p (n + 1)).toReal * z ^ (n + 1)‖
        = (p (n + 1)).toReal * ‖z‖ ^ (n + 1) := by
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
              norm_pow]
    _ ≤ momentTerm.toReal * ‖z‖ ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_right hCoeff_real (pow_nonneg (norm_nonneg z) _)
    _ ≤ A ^ (n + 1) * ‖z‖ ^ (n + 1) := by
          exact mul_le_mul_of_nonneg_right hMoment_real (pow_nonneg (norm_nonneg z) _)
    _ = (A * ‖z‖) ^ (n + 1) := by rw [mul_pow]

/-- Helper for Example 15.33: inside the reciprocal-radius disk, the shifted pgf coefficients are
eventually bounded by a geometric sequence. -/
private lemma natPmfEventuallyLeGeom_of_norm_lt_invLimsupMomentRoot
    (p : PMF ℕ) {z : ℂ}
    (hz :
      ENNReal.ofReal ‖z‖ <
        (limsup
            (fun n : ℕ ↦
              (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
            atTop)⁻¹)
    (hz0 : z ≠ 0) :
    ∃ A : ℝ, 0 ≤ A ∧ A * ‖z‖ < 1 ∧
      ∀ᶠ n in atTop, ‖(p (n + 1)).toReal * z ^ (n + 1)‖ ≤ (A * ‖z‖) ^ (n + 1) := by
  let momentRoot : ℕ → ℝ≥0∞ :=
    fun n : ℕ ↦ (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ)))
  let β : ℝ≥0∞ := limsup momentRoot atTop
  have hnorm_pos : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hβ_lt_invNorm : β < ENNReal.ofReal (‖z‖⁻¹) := by
    -- Proof comment: rewrite the reciprocal-radius hypothesis once so that `exists_between`
    -- can choose a real radius majorant `A`.
    have hβ_lt_inv : β < (ENNReal.ofReal ‖z‖)⁻¹ := by
      simpa [β, momentRoot] using (ENNReal.lt_inv_iff_lt_inv).1 hz
    simpa [ENNReal.ofReal_inv_of_pos hnorm_pos] using hβ_lt_inv
  rcases ENNReal.lt_iff_exists_real_btwn.1 hβ_lt_invNorm with ⟨A, hA_nonneg, hβA, hA_lt⟩
  have hA_lt_invNorm_real : A < ‖z‖⁻¹ := by
    exact (ENNReal.ofReal_lt_ofReal_iff (inv_pos.mpr hnorm_pos)).1 hA_lt
  have hAz_lt_one : A * ‖z‖ < 1 := by
    have hmul : A * ‖z‖ < ‖z‖⁻¹ * ‖z‖ := by
      exact mul_lt_mul_of_pos_right hA_lt_invNorm_real hnorm_pos
    simpa [hnorm_pos.ne', mul_comm, mul_left_comm, mul_assoc] using hmul
  have htailRoot : ∀ᶠ n in atTop, momentRoot n < ENNReal.ofReal A := by
    exact eventually_lt_of_limsup_lt (by simpa [β] using hβA)
  refine ⟨A, hA_nonneg, hAz_lt_one, ?_⟩
  filter_upwards [htailRoot] with n hn
  -- Proof comment: the rebuilt coefficient lemma consumes the eventual root bound without any
  -- further ENNReal normalization in the main theorem.
  simpa [momentRoot] using natPmfCoeffNorm_le_of_momentRoot_lt p (z := z) hA_nonneg (n := n) hn

/-- Example 15.33 (9): Item (iv). For an `ℕ`-valued law, the pgf power series converges at every
complex point `z` with `|z|` strictly smaller than the reciprocal of the limsup of the extended
moment roots. -/
theorem nat_pmf_pgf_series_summable_of_norm_lt_inv_limsup_moment_root (p : PMF ℕ) {z : ℂ}
    (hz :
      ENNReal.ofReal ‖z‖ <
        (limsup
            (fun n : ℕ ↦
              (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
            atTop)⁻¹) :
    Summable (fun n : ℕ ↦ (p n).toReal * z ^ n) := by
  by_cases hz0 : z = 0
  · subst hz0
    have htail :
        Summable (fun n : ℕ ↦ (p (n + 1)).toReal * (0 : ℂ) ^ (n + 1)) := by
      simp
    -- Proof comment: after the first term, the pgf series at `z = 0` is identically zero.
    simpa using
      (_root_.summable_nat_add_iff (f := fun n : ℕ ↦ (p n).toReal * (0 : ℂ) ^ n) 1).1 htail
  rcases natPmfEventuallyLeGeom_of_norm_lt_invLimsupMomentRoot p hz hz0 with
    ⟨A, hA_nonneg, hAz_lt_one, htailBound⟩
  have hGeom :
      Summable (fun n : ℕ ↦ (A * ‖z‖) ^ (n + 1)) := by
    -- Proof comment: the comparison sequence is just the geometric series with ratio `A * ‖z‖`,
    -- shifted by one index.
    exact
      (_root_.summable_nat_add_iff 1).2
        (summable_geometric_of_lt_one (mul_nonneg hA_nonneg (norm_nonneg z)) hAz_lt_one)
  have hTailSummable :
      Summable (fun n : ℕ ↦ (p (n + 1)).toReal * z ^ (n + 1)) := by
    -- Proof comment: compare the shifted tail termwise against the geometric majorant produced by
    -- the limsup hypothesis.
    exact Summable.of_norm_bounded_eventually_nat hGeom htailBound
  -- Proof comment: summability of the shifted tail is equivalent to summability of the whole pgf
  -- series.
  simpa using
    (_root_.summable_nat_add_iff (f := fun n : ℕ ↦ (p n).toReal * z ^ n) 1).1 hTailSummable

-- Proof sketch: the hypothesis on `p` gives a real convergence point `z > 1` for its pgf by the
-- preceding radius criterion. Applying the Chapter 3 owner theorem
-- `probabilityGeneratingFunctionReal_eq_of_iteratedDeriv_eq_of_summable` then recovers the pgf
-- from its derivatives at `1`.
/-- Consequence of Example 15.33 (10): item (iv). If two `ℕ`-valued laws have root-limsup
strictly smaller than `1` and the same derivatives of their pgfs at `1`, then their pgfs agree. -/
theorem
    nat_pmf_probabilityGeneratingFunctionReal_eq_of_iteratedDeriv_eq_of_limsup_moment_root_lt_one
    {p q : PMF ℕ}
    (hpβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    (hqβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂q.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    (h_deriv :
      ∀ n : ℕ,
        iteratedDeriv n (probabilityGeneratingFunctionReal p) 1 =
          iteratedDeriv n (probabilityGeneratingFunctionReal q) 1) :
    probabilityGeneratingFunctionReal p = probabilityGeneratingFunctionReal q := by
  let βp : ℝ≥0∞ :=
    limsup
      (fun n : ℕ ↦
        (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
      atTop
  let βq : ℝ≥0∞ :=
    limsup
      (fun n : ℕ ↦
        (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂q.toMeasure) ^ (1 / ((n + 1 : ℝ))))
      atTop
  have hpInv : (1 : ℝ≥0∞) < βp⁻¹ := by
    -- Proof comment: `βp < 1` means the reciprocal radius for `p` is strictly larger than `1`.
    simpa [βp] using (ENNReal.one_lt_inv.2 hpβ)
  have hqInv : (1 : ℝ≥0∞) < βq⁻¹ := by
    -- Proof comment: the same reciprocal-radius statement holds for `q`.
    simpa [βq] using (ENNReal.one_lt_inv.2 hqβ)
  rcases ENNReal.lt_iff_exists_real_btwn.1 (lt_min hpInv hqInv) with
    ⟨r, hr_nonneg, hOne, hrq⟩
  have hr : 1 < r := by
    simpa using hOne
  have hpRadius : ENNReal.ofReal r < βp⁻¹ := lt_of_lt_of_le hrq (min_le_left _ _)
  have hqRadius : ENNReal.ofReal r < βq⁻¹ := lt_of_lt_of_le hrq (min_le_right _ _)
  have hpSummableComplex :
      Summable (fun n : ℕ ↦ (p n).toReal * (r : ℂ) ^ n) := by
    -- Proof comment: theorem (9) gives convergence at every complex point inside the reciprocal
    -- limsup radius; here we choose the common real point `r > 1`.
    refine nat_pmf_pgf_series_summable_of_norm_lt_inv_limsup_moment_root (p := p) (z := (r : ℂ)) ?_
    simpa [βp, Complex.norm_real, abs_of_nonneg hr_nonneg] using hpRadius
  have hqSummableComplex :
      Summable (fun n : ℕ ↦ (q n).toReal * (r : ℂ) ^ n) := by
    -- Proof comment: apply the same radius argument to `q`.
    refine nat_pmf_pgf_series_summable_of_norm_lt_inv_limsup_moment_root (p := q) (z := (r : ℂ)) ?_
    simpa [βq, Complex.norm_real, abs_of_nonneg hr_nonneg] using hqRadius
  have hpSummable :
      Summable (fun n : ℕ ↦ (p n).toReal * r ^ n) := by
    -- Proof comment: the complex summability statement is really the real pgf series viewed
    -- through `Complex.ofReal`.
    rw [← Complex.summable_ofReal]
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using hpSummableComplex
  have hqSummable :
      Summable (fun n : ℕ ↦ (q n).toReal * r ^ n) := by
    -- Proof comment: use the same real-to-complex bridge for `q`.
    rw [← Complex.summable_ofReal]
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using hqSummableComplex
  exact probabilityGeneratingFunctionReal_eq_of_iteratedDeriv_eq_of_summable
    hr hpSummable hqSummable h_deriv

-- Proof sketch: the root-limsup hypothesis gives a real convergence point `z > 1` for the pgf by
-- the preceding radius criterion. Equality of moments yields equality of the derivatives of the pgf
-- at `1`, so the previous pgf-uniqueness theorem identifies the pushed-forward law.
/-- Helper for Example 15.33: on a discrete PMF, integrability against `p.toMeasure` is the same
as integrability against the canonical sum of weighted Dirac masses. -/
private theorem natPmfIntegrableExpAbs_sumDiracBridge
    (p : PMF ℕ) {r : ℝ} :
    Integrable (fun k : ℕ ↦ Real.exp (Real.log r * |(k : ℝ)|)) p.toMeasure ↔
      Integrable
        (fun k : ℕ ↦ Real.exp (Real.log r * |(k : ℝ)|))
        (Measure.sum fun k : ℕ ↦ p k • Measure.dirac k) := by
  -- Proof comment: cache the canonical `PMF.toMeasure = sum of weighted diracs` rewrite once, so
  -- the later proof can invoke `integrable_sum_dirac_iff` in a stable normal form.
  have hsum :
      (Measure.sum fun k : ℕ ↦ p k • Measure.dirac k) = p.toMeasure := by
    simpa [PMF.toMeasure_apply_singleton, measurableSet_singleton] using
      (Measure.sum_smul_dirac (μ := p.toMeasure))
  constructor
  · intro h
    simpa [hsum] using h
  · intro h
    simpa [hsum] using h

/-- Helper for Example 15.33: a summable pgf series at a real point `r > 1` gives an integrable
exponential moment for the embedded `ℕ`-valued law. -/
private theorem natPmfIntegrableExpAbs_of_pgfSeriesSummable
    (p : PMF ℕ) {r : ℝ} (hr : 1 < r)
    (hs :
      Summable (fun n : ℕ ↦ (p n).toReal * r ^ n)) :
    Integrable (fun k : ℕ ↦ Real.exp (Real.log r * |(k : ℝ)|)) p.toMeasure := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  have hweight :
      ∀ k : ℕ, Real.exp (Real.log r * |(k : ℝ)|) = r ^ k := by
    intro k
    -- Proof comment: on `ℕ`, `|k| = k`, so the exponential weight is exactly the geometric term.
    rw [abs_of_nonneg (Nat.cast_nonneg k), mul_comm, Real.exp_nat_mul, Real.exp_log hr0]
  have hsumDirac :
      Summable
        (fun k : ℕ ↦
          (p k).toReal * ‖Real.exp (Real.log r * |(k : ℝ)|)‖) := by
    -- Proof comment: after normalizing the exponential weight, the summable norm series is
    -- literally the assumed pgf series.
    have hseries :
        (fun k : ℕ ↦ (p k).toReal * ‖Real.exp (Real.log r * |(k : ℝ)|)‖) =
          fun k : ℕ ↦ (p k).toReal * r ^ k := by
      funext k
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), hweight]
    rw [hseries]
    exact hs
  have hsumMeasure :
      Integrable
        (fun k : ℕ ↦ Real.exp (Real.log r * |(k : ℝ)|))
        (Measure.sum fun k : ℕ ↦ p k • Measure.dirac k) := by
    -- Proof comment: on the discrete sum-of-diracs measure, integrability is equivalent to the
    -- summability of the singleton-weighted norms.
    rw [MeasureTheory.integrable_sum_dirac_iff
      (x := fun k : ℕ ↦ k)
      (c := fun k : ℕ ↦ p k)
      (f := fun k : ℕ ↦ Real.exp (Real.log r * |(k : ℝ)|))
      (fun k ↦ p.apply_ne_top k)]
    simpa using hsumDirac
  exact (natPmfIntegrableExpAbs_sumDiracBridge (p := p) (r := r)).2 hsumMeasure

/-- Consequence of Example 15.33 (11): item (iv). If an `ℕ`-valued law has root-limsup strictly
smaller than `1`, then the associated real-valued law `k ↦ k` is moment determinate. -/
theorem isMomentDeterminate_nat_pmf_of_limsup_moment_root_lt_one
    (p : PMF ℕ)
    (hpβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    :
    IsMomentDeterminate p.toMeasure (fun k : ℕ ↦ (k : ℝ)) := by
  let β : ℝ≥0∞ :=
    limsup
      (fun n : ℕ ↦
        (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
      atTop
  have hInv : (1 : ℝ≥0∞) < β⁻¹ := by
    -- Proof comment: `β < 1` says the reciprocal convergence radius is strictly larger than `1`.
    simpa [β] using (ENNReal.one_lt_inv.2 hpβ)
  rcases ENNReal.lt_iff_exists_real_btwn.1 hInv with ⟨r, hr_nonneg, hOne, hrRadius⟩
  have hr : 1 < r := by
    simpa using hOne
  have hSummableComplex :
      Summable (fun n : ℕ ↦ (p n).toReal * (r : ℂ) ^ n) := by
    -- Proof comment: theorem (9) supplies convergence of the pgf series at the chosen radius.
    refine nat_pmf_pgf_series_summable_of_norm_lt_inv_limsup_moment_root (p := p) (z := (r : ℂ)) ?_
    simpa [β, Complex.norm_real, abs_of_nonneg hr_nonneg] using hrRadius
  have hSummable :
      Summable (fun n : ℕ ↦ (p n).toReal * r ^ n) := by
    -- Proof comment: convert the complex convergence statement back to the real pgf series.
    rw [← Complex.summable_ofReal]
    simpa [Complex.ofReal_mul, Complex.ofReal_pow] using hSummableComplex
  have hExp :
      Integrable (fun k : ℕ ↦ Real.exp (Real.log r * |(k : ℝ)|)) p.toMeasure :=
    natPmfIntegrableExpAbs_of_pgfSeriesSummable p hr hSummable
  -- Proof comment: now apply the chapter owner theorem to the real-valued embedding `ℕ → ℝ`.
  exact
    (method_of_moments_of_integrable_exp_abs_map
      (P := p.toMeasure) (X := fun k : ℕ ↦ (k : ℝ))
      MeasurableEmbedding.natCast.measurable (Real.log_pos hr) hExp).2

/-- Companion corollary: under the same root-growth hypothesis, equality of all moments identifies
an `ℕ`-valued law. -/
theorem nat_pmf_eq_of_forall_moment_eq_of_limsup_moment_root_lt_one
    {p q : PMF ℕ}
    (hpβ :
      limsup
          (fun n : ℕ ↦
            (∫⁻ k, (k : ℝ≥0∞) ^ (n + 1) ∂p.toMeasure) ^ (1 / ((n + 1 : ℝ))))
          atTop < 1)
    (hq_moments : ∀ n : ℕ, Integrable (fun k : ℕ ↦ |(k : ℝ)| ^ n) q.toMeasure)
    (h_mom :
      ∀ n : ℕ,
        moment (fun k : ℕ ↦ (k : ℝ)) n p.toMeasure =
          moment (fun k : ℕ ↦ (k : ℝ)) n q.toMeasure) :
    p = q := by
  let h_det : IsMomentDeterminate p.toMeasure (fun k : ℕ ↦ (k : ℝ)) :=
    isMomentDeterminate_nat_pmf_of_limsup_moment_root_lt_one p hpβ
  let h_nat_embedding : MeasurableEmbedding (fun k : ℕ ↦ (k : ℝ)) :=
    MeasurableEmbedding.natCast
  have hmap :
      p.toMeasure.map (fun k : ℕ ↦ (k : ℝ)) =
        q.toMeasure.map (fun k : ℕ ↦ (k : ℝ)) :=
    h_det.map_eq q.toMeasure (fun k : ℕ ↦ (k : ℝ)) h_nat_embedding.measurable hq_moments h_mom
  exact PMF.toMeasure_injective <| h_nat_embedding.map_injective hmap
