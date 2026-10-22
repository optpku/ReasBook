/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Helper for Exercise 8.2.8: a nonpositive rate makes `expMeasure θ` vanish identically. -/
lemma expMeasure_eq_zero_of_nonpos {θ : ℝ} (hθ : θ ≤ 0) : expMeasure θ = 0 := by
  -- Proof comment: rewrite the exponential law as a `withDensity` measure and show the density
  -- vanishes pointwise because it is zero on `(-∞, 0)` and nonpositive on `[0, ∞)`.
  rw [expMeasure, gammaMeasure]
  have hzero : gammaPDF 1 θ =ᵐ[volume] 0 := by
    filter_upwards with x
    by_cases hx : 0 ≤ x
    · rw [show gammaPDF 1 θ x = exponentialPDF θ x by rfl, exponentialPDF_of_nonneg hx]
      apply ENNReal.ofReal_eq_zero.2
      exact mul_nonpos_of_nonpos_of_nonneg hθ (le_of_lt (Real.exp_pos _))
    · have hx' : x < 0 := by linarith
      simp [show gammaPDF 1 θ x = exponentialPDF θ x by rfl, exponentialPDF_of_neg hx']
  rw [withDensity_congr_ae hzero, withDensity_zero]

/-- Helper for Exercise 8.2.8: a random variable with law `expMeasure θ` must have positive rate.
-/
lemma ratePosOfHasLawExp {X : Ω → ℝ} {θ : ℝ} (hX : HasLaw X (expMeasure θ) P) : 0 < θ := by
  -- Route correction: isolate the nonpositive-rate case as the separate measure-level lemma
  -- `expMeasure_eq_zero_of_nonpos` instead of unfolding `withDensity` inside this contradiction.
  by_contra hθ
  have hθ' : θ ≤ 0 := le_of_not_gt hθ
  have hprob : IsProbabilityMeasure (expMeasure θ) := hX.isProbabilityMeasure_iff.mp inferInstance
  letI : IsProbabilityMeasure (expMeasure θ) := hprob
  have huniv : expMeasure θ Set.univ = 1 := by
    simp
  rw [expMeasure_eq_zero_of_nonpos hθ'] at huniv
  simp at huniv

omit [IsProbabilityMeasure P] in
/-- Helper for Exercise 8.2.8: an exponential random variable is almost surely nonnegative. -/
lemma aeNonnegOfHasLawExp {X : Ω → ℝ} {θ : ℝ} (hX : HasLaw X (expMeasure θ) P) :
    ∀ᵐ ω ∂P, 0 ≤ X ω := by
  -- Proof comment: the exponential density vanishes on `Iio 0`, so the pushforward law gives
  -- zero mass to the negative half-line and `HasLaw.ae_iff` transports the support statement back.
  have hIio : expMeasure θ (Set.Iio 0) = 0 := by
    rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
    rw [show gammaPDF 1 θ = exponentialPDF θ by funext x; rfl]
    exact lintegral_exponentialPDF_of_nonpos (x := 0) le_rfl
  have hAe : ∀ᵐ x ∂expMeasure θ, 0 ≤ x := by
    rw [ae_iff]
    simpa [not_le] using hIio
  have hp : Measurable fun x : ℝ ↦ 0 ≤ x := by fun_prop
  exact (hX.ae_iff (p := fun x : ℝ ↦ 0 ≤ x) hp).2 hAe

/-- Helper for Exercise 8.2.8: rewrite integration against `expMeasure θ` as integration against
its density. -/
lemma integralExpMeasureEqIntegralDensity {θ : ℝ} (hθ : 0 < θ) {f : ℝ → ℝ} :
    ∫ x, f x ∂expMeasure θ = ∫ x, exponentialPDFReal θ x * f x := by
  -- Proof comment: unfold `expMeasure` as a `withDensity` measure and simplify the scalar density.
  rw [expMeasure, gammaMeasure,
    integral_withDensity_eq_integral_toReal_smul (μ := volume) (f := gammaPDF 1 θ)
      (measurable_gammaPDFReal 1 θ).ennreal_ofReal
      (ae_of_all _ fun _ ↦ ENNReal.ofReal_lt_top)]
  refine integral_congr_ae ?_
  filter_upwards with x
  simp [gammaPDF, exponentialPDFReal, gammaPDFReal_nonneg zero_lt_one hθ x, smul_eq_mul]

/-- Helper for Exercise 8.2.8: the identity function is integrable under `expMeasure θ`. -/
lemma integrableIdExpMeasure {θ : ℝ} (hθ : 0 < θ) : Integrable (fun x : ℝ ↦ x) (expMeasure θ) := by
  -- Proof comment: compute the first moment explicitly as `1 / θ`; since this value is nonzero,
  -- the Bochner integral cannot be the default zero integral of a nonintegrable function.
  have hIntegral : (∫ x, x ∂expMeasure θ) = 1 / θ := by
    rw [integralExpMeasureEqIntegralDensity hθ]
    have hIndicator :
        (fun x ↦ exponentialPDFReal θ x * x) =
          Set.indicator (Set.Ici 0) (fun x ↦ (θ * Real.exp (-(θ * x))) * x) := by
      funext x
      by_cases hx : 0 ≤ x
      · simp [exponentialPDFReal, gammaPDFReal, hx]
      · simp [exponentialPDFReal, gammaPDFReal, hx]
    rw [hIndicator, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
    have hRewrite :
        (fun x ↦ (θ * Real.exp (-(θ * x))) * x) =
          fun x ↦ θ * (x ^ ((2 : ℝ) - 1) * Real.exp (-(θ * x))) := by
      funext x
      rw [show ((2 : ℝ) - 1) = 1 by norm_num, Real.rpow_one]
      ring_nf
    rw [hRewrite, integral_const_mul,
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := θ) (by norm_num) hθ,
      Real.Gamma_two]
    field_simp [hθ.ne']
    simp [one_div, hθ.ne']
  apply Integrable.of_integral_ne_zero
  rw [hIntegral]
  exact one_div_ne_zero hθ.ne'

/-- Helper for Exercise 8.2.8: an exponential random variable is integrable. -/
lemma integrableOfHasLawExp {X : Ω → ℝ} {θ : ℝ} (hX : HasLaw X (expMeasure θ) P) :
    Integrable X P := by
  -- Proof comment: once the exponential rate is positive, integrability is a pushforward property
  -- of the identity map under `P.map X = expMeasure θ`.
  have hθ : 0 < θ := ratePosOfHasLawExp hX
  have hId : Integrable (fun x : ℝ ↦ x) (P.map X) := by
    simpa [hX.map_eq] using integrableIdExpMeasure hθ
  simpa using (integrable_map_measure aestronglyMeasurable_id hX.aemeasurable).1 hId

/-- Helper for Exercise 8.2.8: the pointwise minimum of two exponential random variables is
integrable. -/
lemma integrableMinOfHasLawExp {X₁ X₂ : Ω → ℝ} {θ : ℝ}
    (hX₁ : HasLaw X₁ (expMeasure θ) P) (hX₂ : HasLaw X₂ (expMeasure θ) P) :
    Integrable (fun ω ↦ X₁ ω ⊓ X₂ ω) P := by
  -- Proof comment: on the almost-sure support where both variables are nonnegative, the minimum
  -- is itself nonnegative and bounded above by `X₁`, so `Integrable.mono'` closes the estimate.
  have hX₁_int : Integrable X₁ P := integrableOfHasLawExp hX₁
  have hX₁_nonneg : ∀ᵐ ω ∂P, 0 ≤ X₁ ω := aeNonnegOfHasLawExp hX₁
  have hX₂_nonneg : ∀ᵐ ω ∂P, 0 ≤ X₂ ω := aeNonnegOfHasLawExp hX₂
  refine hX₁_int.mono'
    (hX₁.aemeasurable.aestronglyMeasurable.inf hX₂.aemeasurable.aestronglyMeasurable) ?_
  filter_upwards [hX₁_nonneg, hX₂_nonneg] with ω hω₁ hω₂
  have hmin_nonneg : 0 ≤ X₁ ω ⊓ X₂ ω := le_inf hω₁ hω₂
  rw [Real.norm_of_nonneg hmin_nonneg]
  exact inf_le_left

/-- Helper for Exercise 8.2.8: independence identifies the conditional law of `X₂` given `X₁`
with the constant exponential kernel. -/
lemma condDistribSecondGivenFirstAeEqConstExp {X₁ X₂ : Ω → ℝ} {θ : ℝ}
    (hX₁_exp : HasLaw X₁ (expMeasure θ) P) (hX₂_exp : HasLaw X₂ (expMeasure θ) P)
    (h_indep : X₁ ⟂ᵢ[P] X₂) :
    condDistrib X₂ X₁ P =ᵐ[P.map X₁] Kernel.const ℝ (expMeasure θ) := by
  -- Proof comment: independence identifies the joint pushforward with the product of the two
  -- marginals, and the second marginal is exactly `expMeasure θ`.
  letI : IsProbabilityMeasure (expMeasure θ) := hX₂_exp.isProbabilityMeasure_iff.mp inferInstance
  have hpair :
      P.map (fun ω ↦ (X₁ ω, X₂ ω)) = P.map X₁ ⊗ₘ Kernel.const ℝ (expMeasure θ) := by
    calc
      P.map (fun ω ↦ (X₁ ω, X₂ ω)) = (P.map X₁).prod (P.map X₂) := by
        simpa using
          (indepFun_iff_map_prod_eq_prod_map_map hX₁_exp.aemeasurable hX₂_exp.aemeasurable).mp
            h_indep
      _ = (P.map X₁).prod (expMeasure θ) := by rw [hX₂_exp.map_eq]
      _ = P.map X₁ ⊗ₘ Kernel.const ℝ (expMeasure θ) := by
        rw [← Measure.compProd_const]
  exact condDistrib_ae_eq_of_measure_eq_compProd X₁ hX₂_exp.aemeasurable hpair

/-- Helper for Exercise 8.2.8: the exponential density has an explicit antiderivative on
`[0, x]` after multiplying by the identity. -/
lemma expDensityMulId_intervalIntegral {θ x : ℝ} (hθ : 0 < θ) (hx : 0 ≤ x) :
    ∫ y in 0..x, (θ * Real.exp (-(θ * y))) * y =
      1 / θ - (x + 1 / θ) * Real.exp (-(θ * x)) := by
  -- Proof comment: evaluate the interval integral by the fundamental theorem of calculus with the
  -- antiderivative `y ↦ -(y + 1 / θ) * exp (-(θ * y))`.
  let F : ℝ → ℝ := fun y ↦ -(y + 1 / θ) * Real.exp (-(θ * y))
  have hFderiv : ∀ y ∈ Set.Ioo 0 x, HasDerivAt F ((θ * Real.exp (-(θ * y))) * y) y := by
    intro y _
    dsimp [F]
    have hLeft : HasDerivAt (fun t : ℝ ↦ -(t + 1 / θ)) (-1) y := by
      convert (((hasDerivAt_id y).const_add (1 / θ)).neg) using 1
      ext t
      simp
      ring
    have hRight : HasDerivAt (fun t : ℝ ↦ Real.exp (-(θ * t)))
        (-θ * Real.exp (-(θ * y))) y := by
      have hRightNeg :
          HasDerivAt (fun t : ℝ ↦ -Real.exp (-(θ * t))) (θ * Real.exp (-(θ * y))) y :=
        ProbabilityTheory.hasDerivAt_neg_exp_mul_exp (r := θ) (x := y)
      convert hRightNeg.neg using 1
      · ext t
        simp
      · ring
    convert hLeft.mul hRight using 1
    field_simp [hθ.ne']
    ring
  have hFcont : ContinuousOn F (Set.Icc 0 x) := by
    -- Proof comment: the antiderivative is built from continuous algebraic and exponential pieces.
    refine Continuous.continuousOn ?_
    continuity
  have hInt : IntervalIntegrable (fun y ↦ (θ * Real.exp (-(θ * y))) * y) volume 0 x := by
    -- Proof comment: continuity on the closed interval gives interval integrability directly.
    refine ContinuousOn.intervalIntegrable_of_Icc hx ?_
    refine Continuous.continuousOn ?_
    continuity
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx hFcont hFderiv hInt]
  simp [F]
  field_simp [hθ.ne']
  ring

/-- Helper for Exercise 8.2.8: for `x ≥ 0`, integrating `y ↦ x ⊓ y` against the exponential law
with rate `θ` gives `(1 - exp (-(θ * x))) / θ`. -/
lemma integralMinExpOfNonneg {θ x : ℝ} (hθ : 0 < θ) (hx : 0 ≤ x) :
    ∫ y, x ⊓ y ∂expMeasure θ = (1 - Real.exp (-(θ * x))) / θ := by
  -- Route correction: split the exponential expectation under `expMeasure θ`, evaluate the
  -- `Iic x` contribution by an FTC helper, and read the `Ioi x` mass from the exponential CDF.
  have hAeNonneg : ∀ᵐ y ∂expMeasure θ, 0 ≤ y := by
    -- Proof comment: the exponential law charges no negative values.
    rw [ae_iff]
    simpa [not_le] using
      (show expMeasure θ (Set.Iio 0) = 0 by
        rw [expMeasure, gammaMeasure, withDensity_apply _ measurableSet_Iio]
        rw [show gammaPDF 1 θ = exponentialPDF θ by funext y; rfl]
        exact lintegral_exponentialPDF_of_nonpos (x := 0) le_rfl)
  have hMinInt : Integrable (fun y : ℝ ↦ x ⊓ y) (expMeasure θ) := by
    -- Proof comment: on the almost-sure support `{y | 0 ≤ y}`, the minimum is nonnegative and
    -- bounded above by `y`, so the known first moment controls the whole integrand.
    refine (integrableIdExpMeasure hθ).mono'
      ((stronglyMeasurable_const.inf stronglyMeasurable_id).aestronglyMeasurable) ?_
    filter_upwards [hAeNonneg] with y hy
    have hMinNonneg : 0 ≤ x ⊓ y := le_inf hx hy
    rw [Real.norm_of_nonneg hMinNonneg]
    exact inf_le_right
  have hLeft :
      ∫ y in Set.Iic x, x ⊓ y ∂expMeasure θ =
        ∫ y in 0..x, (θ * Real.exp (-(θ * y))) * y := by
    -- Proof comment: on `Iic x`, the minimum collapses to `y`; rewriting the set integral through
    -- the exponential density leaves exactly the finite interval `[0, x]`.
    calc
      ∫ y in Set.Iic x, x ⊓ y ∂expMeasure θ = ∫ y in Set.Iic x, y ∂expMeasure θ := by
        refine setIntegral_congr_fun measurableSet_Iic (fun y hy ↦ ?_)
        exact min_eq_right hy
      _ = ∫ y in 0..x, (θ * Real.exp (-(θ * y))) * y := by
        rw [← integral_indicator measurableSet_Iic, integralExpMeasureEqIntegralDensity hθ]
        have hIndicator :
            (fun y ↦
              exponentialPDFReal θ y * Set.indicator (Set.Iic x) (fun z ↦ z) y) =
              Set.indicator (Set.Icc 0 x) (fun y ↦ (θ * Real.exp (-(θ * y))) * y) := by
          funext y
          rcases le_or_gt y x with hyx | hyx
          · rcases le_or_gt 0 y with hy0 | hy0
            · simp [Set.indicator, hyx, hy0, exponentialPDFReal, gammaPDFReal]
            · simp [Set.indicator, hyx, not_le_of_gt hy0, exponentialPDFReal, gammaPDFReal]
          · rcases le_or_gt 0 y with hy0 | hy0
            · simp [Set.indicator, not_le_of_gt hyx, hy0, exponentialPDFReal, gammaPDFReal]
            · simp [Set.indicator, not_le_of_gt hyx, not_le_of_gt hy0, exponentialPDFReal,
                gammaPDFReal]
        rw [hIndicator, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
          ← intervalIntegral.integral_of_le hx]
  have hRight :
      ∫ y in Set.Ioi x, x ⊓ y ∂expMeasure θ = x * Real.exp (-(θ * x)) := by
    letI : IsProbabilityMeasure (expMeasure θ) := isProbabilityMeasure_expMeasure hθ
    have hIoi :
        (expMeasure θ).real (Set.Ioi x) = Real.exp (-(θ * x)) := by
      have hCdf :
          (expMeasure θ).real (Set.Iic x) = 1 - Real.exp (-(θ * x)) := by
        rw [← ProbabilityTheory.cdf_eq_real (μ := expMeasure θ) x,
          ProbabilityTheory.cdf_expMeasure_eq hθ, if_pos hx]
      calc
        (expMeasure θ).real (Set.Ioi x)
            = 1 - (expMeasure θ).real (Set.Iic x) := by
              simpa [Set.compl_Iic] using
                (MeasureTheory.probReal_compl_eq_one_sub (μ := expMeasure θ) measurableSet_Iic)
        _ = Real.exp (-(θ * x)) := by rw [hCdf]; ring
    calc
      ∫ y in Set.Ioi x, x ⊓ y ∂expMeasure θ = ∫ y in Set.Ioi x, x ∂expMeasure θ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro y hy
        exact min_eq_left (le_of_lt hy)
      _ = (expMeasure θ).real (Set.Ioi x) * x := by
        rw [MeasureTheory.setIntegral_const]
        simp [smul_eq_mul, mul_comm]
      _ = x * Real.exp (-(θ * x)) := by
        rw [hIoi]
        ring
  calc
    ∫ y, x ⊓ y ∂expMeasure θ
        = ∫ y in Set.Iic x, x ⊓ y ∂expMeasure θ
            + ∫ y in Set.Ioi x, x ⊓ y ∂expMeasure θ := by
            symm
            simpa [Set.compl_Iic] using
              (integral_add_compl (μ := expMeasure θ) (f := fun y : ℝ ↦ x ⊓ y)
                measurableSet_Iic hMinInt)
    _ = (∫ y in 0..x, (θ * Real.exp (-(θ * y))) * y) + x * Real.exp (-(θ * x)) := by
          rw [hLeft, hRight]
    _ = (1 / θ - (x + 1 / θ) * Real.exp (-(θ * x))) + x * Real.exp (-(θ * x)) := by
          rw [expDensityMulId_intervalIntegral (θ := θ) (x := x) hθ hx]
    _ = (1 - Real.exp (-(θ * x))) / θ := by
          field_simp [hθ.ne']
          ring

-- Proof sketch: write the conditional expectation of `fun ω ↦ X₁ ω ⊓ X₂ ω` given `X₁`
-- using `ProbabilityTheory.condExp_prod_ae_eq_integral_condDistrib` for the function
-- `(x, y) ↦ x ⊓ y`. The measurability of `X₁` determines the conditioning σ-algebra
-- `MeasurableSpace.comap X₁ (borel ℝ)`, while `HasLaw X₂ (expMeasure θ) P` supplies the
-- `P`-almost-everywhere measurability required by the conditional-distribution API. Independence
-- then identifies the conditional distribution of `X₂` given `X₁` with `expMeasure θ`, and the
-- resulting one-dimensional integral evaluates to `(1 - exp (-θ x)) / θ`.
/-- Exercise 8.2.8: if `X₁` is measurable, `X₁` and `X₂` are independent, and both have
exponential law with common rate `θ`, then the conditional expectation of `X₁ ∧ X₂` given `X₁`
is `(1 - exp (-θ X₁)) / θ` almost surely. Since `P` is a probability measure, the law hypotheses
already force `expMeasure θ` to be a probability measure, hence in particular `θ > 0`. -/
theorem condExp_min_of_indep_exp_ae_eq {X₁ X₂ : Ω → ℝ} {θ : ℝ}
    (hX₁_meas : Measurable X₁)
    (hX₁_exp : HasLaw X₁ (expMeasure θ) P) (hX₂_exp : HasLaw X₂ (expMeasure θ) P)
    (h_indep : X₁ ⟂ᵢ[P] X₂) :
    P[fun ω ↦ X₁ ω ⊓ X₂ ω | MeasurableSpace.comap X₁ (borel ℝ)] =ᵐ[P]
      fun ω ↦ (1 - Real.exp (-(θ * X₁ ω))) / θ := by
  -- Proof comment: first rewrite the conditional expectation as an integral against the
  -- conditional law of `X₂` given `X₁`, then replace that kernel by the constant exponential law.
  have hθ : 0 < θ := ratePosOfHasLawExp hX₁_exp
  have hmin_meas : StronglyMeasurable fun z : ℝ × ℝ ↦ z.1 ⊓ z.2 := by
    fun_prop
  have hmin_int : Integrable (fun ω ↦ X₁ ω ⊓ X₂ ω) P :=
    integrableMinOfHasLawExp hX₁_exp hX₂_exp
  have hcond :
      P[fun ω ↦ X₁ ω ⊓ X₂ ω | MeasurableSpace.comap X₁ (borel ℝ)] =ᵐ[P]
        fun ω ↦ ∫ y, X₁ ω ⊓ y ∂condDistrib X₂ X₁ P (X₁ ω) := by
    simpa using
      (condExp_prod_ae_eq_integral_condDistrib (μ := P) (X := X₁) (Y := X₂)
        hX₁_meas hX₂_exp.aemeasurable hmin_meas hmin_int)
  have hkernel :
      (fun ω ↦ condDistrib X₂ X₁ P (X₁ ω)) =ᵐ[P]
        fun ω ↦ Kernel.const ℝ (expMeasure θ) (X₁ ω) := by
    simpa using
      (condDistribSecondGivenFirstAeEqConstExp hX₁_exp hX₂_exp h_indep).comp_tendsto
        (Measure.tendsto_ae_map hX₁_exp.aemeasurable)
  have hnonneg : ∀ᵐ ω ∂P, 0 ≤ X₁ ω := aeNonnegOfHasLawExp hX₁_exp
  filter_upwards [hcond, hkernel, hnonneg] with ω hω_cond hω_kernel hω_nonneg
  rw [hω_cond, hω_kernel, Kernel.integral_const]
  simpa using integralMinExpOfNonneg hθ hω_nonneg
