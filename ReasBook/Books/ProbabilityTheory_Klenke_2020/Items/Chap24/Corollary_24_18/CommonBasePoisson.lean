/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap24.Corollary_24_18.CommonBasePoissonKernel

open MeasureTheory ProbabilityTheory MeasureTheory.FiniteMeasure
open scoped MeasureTheory ENNReal Topology

noncomputable section

universe u

namespace MeasureTheory.ProbabilityMeasure

/-- Helper for Corollary 24.18: a measurable deterministic Poisson integrand with integrable
truncation has almost surely finite integral on the common base PPP. -/
theorem deterministicPoissonIntegral_ae_ltTop_of_integrableMin
    {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g)
    (hg_int : Integrable (fun y : NNReal ↦ min (1 : ℝ) (g y : ℝ)) nnrealLebesgue) :
    ∀ᵐ ω ∂(P : Measure Ω), (∫⁻ y, (g y : ENNReal) ∂ X ω) < ∞ := by
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ y, (g y : ENNReal) ∂ X ω
  let A : Set Ω := {ω | Y ω < ∞}
  let scaledG : ℕ → NonnegativeMeasurableFunction NNReal := fun n ↦
    ⟨fun y ↦ ENNReal.ofReal (invSuccScaleReal n) * g y,
      measurable_const.mul (measurable_coe_nnreal_ennreal.comp hg_meas)⟩
  let scaledExponent : ℕ → ℝ≥0∞ := fun n ↦
    ∫⁻ y,
      (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledG n y)) ∂nnrealLebesgue
  have hY_meas : Measurable Y := by
    -- Proof comment: the deterministic integral is measurable because the random measure map is.
    refine (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp hg_meas)).comp ?_
    exact hX.1.measurable
  have hA_meas : MeasurableSet A := measurableSet_lt hY_meas measurable_const
  have hs_nonneg : ∀ n, 0 ≤ invSuccScaleReal n := by
    intro n
    have hn : 0 ≤ (n : ℝ) + 1 := by
      positivity
    simpa [invSuccScaleReal] using one_div_nonneg.mpr hn
  have hs_le_one : ∀ n, invSuccScaleReal n ≤ 1 := by
    intro n
    have hn : (0 : ℝ) ≤ n := by
      exact_mod_cast Nat.zero_le n
    have hn' : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      linarith
    simpa [invSuccScaleReal] using inv_le_one_of_one_le₀ hn'
  have hkernel_meas :
      ∀ n, AEStronglyMeasurable
        (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) nnrealLebesgue := by
    intro n
    have h : Measurable (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) := by
      fun_prop
    exact h.aestronglyMeasurable
  have hkernel_nonneg :
      ∀ n,
        0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) := by
    intro n
    filter_upwards with y
    have harg_nonneg : 0 ≤ invSuccScaleReal n * (g y : ℝ) := by
      nlinarith [hs_nonneg n, (g y).2]
    have hle : Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      linarith
    exact sub_nonneg.mpr hle
  have hkernel_int :
      ∀ n,
        Integrable (fun y : NNReal ↦ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))))
          nnrealLebesgue := by
    intro n
    -- Proof comment: each scaled kernel is dominated by the truncated first-moment integrand.
    refine Integrable.mono' hg_int (hkernel_meas n) ?_
    filter_upwards with y
    have hnonneg : 0 ≤ 1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) := by
      have harg_nonneg : 0 ≤ invSuccScaleReal n * (g y : ℝ) := by
        nlinarith [hs_nonneg n, (g y).2]
      have hle : Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        linarith
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))) ≤ min (1 : ℝ) (g y : ℝ) :=
      poissonExpKernel_scale_le_minOne (invSuccScaleReal n) (hs_le_one n) (g y)
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      ∀ n,
        scaledExponent n =
          ENNReal.ofReal
            (∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue) := by
    intro n
    calc
      scaledExponent n
          =
        ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue := by
              refine lintegral_congr_ae ?_
              filter_upwards with y
              simpa [scaledExponent, scaledG, ENNReal.ofReal_mul, hs_nonneg n] using
                poissonLaplaceKernel_scale_eq_ofReal (invSuccScaleReal n) (hs_nonneg n) (g y)
      _ =
        ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hkernel_int n)
              (hkernel_nonneg n)
  have hLeft :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
          (P : Measure Ω))
        Filter.atTop (nhds ((P : Measure Ω) A).toReal) :=
    laplaceInvSucc_tendsto_measureFinite hY_meas
  have hRight :
      Filter.Tendsto (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) Filter.atTop (nhds 1) := by
    have hrewrite :
        (fun n : ℕ ↦ ennrealExpNeg (scaledExponent n)) =
          (fun n : ℕ ↦
            Real.exp
              (-(∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ))))
                  ∂nnrealLebesgue))) := by
      funext n
      have hIntegral_nonneg :
          0 ≤
            ∫ y : NNReal, (1 - Real.exp (-(invSuccScaleReal n * (g y : ℝ)))) ∂nnrealLebesgue :=
        integral_nonneg_of_ae (hkernel_nonneg n)
      have hscaled_ne_top : scaledExponent n ≠ ∞ := by
        rw [hscaledExponent_eq n]
        exact ENNReal.ofReal_ne_top
      rw [ennrealExpNeg, if_neg hscaled_ne_top, hscaledExponent_eq n, ENNReal.toReal_ofReal
        hIntegral_nonneg]
    rw [hrewrite]
    have hcont : Continuous (fun r : ℝ ↦ Real.exp (-r)) :=
      Real.continuous_exp.comp continuous_neg
    -- Proof comment: dominated convergence makes the deterministic exponent vanish.
    simpa using hcont.continuousAt.tendsto.comp
      (poissonLaplaceExponent_invSucc_tendstoZero nnrealLebesgue hg_int)
  have hLaplaceScaled :
      ∀ n,
        ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂(P : Measure Ω) =
          ennrealExpNeg (scaledExponent n) := by
    intro n
    -- Proof comment: specialize the PPP Laplace transform to the scaled deterministic integrand.
    have hlintegral :
        (fun ω ↦ ∫⁻ y, scaledG n y ∂ X ω) =
          (fun ω ↦ ENNReal.ofReal (invSuccScaleReal n) * Y ω) := by
      funext ω
      simpa [scaledG, Y] using
        (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (invSuccScaleReal n))
          (fun y : NNReal ↦ (g y : ℝ≥0∞))
          (measurable_coe_nnreal_ennreal.comp hg_meas))
    have hraw :
        ∫ ω, ennrealExpNeg (∫⁻ y, scaledG n y ∂ X ω) ∂(P : Measure Ω) =
          ennrealExpNeg (scaledExponent n) := by
      simpa [scaledExponent] using
        poisson_point_process_laplaceTransform P nnrealLebesgue X hX (scaledG n)
    have hleftRewrite :
        (fun ω ↦ ennrealExpNeg (∫⁻ y, scaledG n y ∂ X ω)) =
          (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω)) := by
      funext ω
      simpa using congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    simpa [hleftRewrite] using hraw
  have hLeftOne :
      Filter.Tendsto
        (fun n : ℕ ↦ ∫ ω, ennrealExpNeg (ENNReal.ofReal (invSuccScaleReal n) * Y ω) ∂
          (P : Measure Ω))
        Filter.atTop (nhds 1) := by
    simpa [hLaplaceScaled] using hRight
  have hToRealOne : ((P : Measure Ω) A).toReal = 1 :=
    tendsto_nhds_unique hLeft hLeftOne
  have hPA : (P : Measure Ω) A = 1 :=
    (ENNReal.toReal_eq_one_iff ((P : Measure Ω) A)).mp hToRealOne
  exact (mem_ae_iff_prob_eq_one hA_meas).2 hPA

/-- Helper for Corollary 24.18: the common-base deterministic Poisson integral satisfies the
standard Laplace transform formula once its truncation kernel is integrable. -/
theorem deterministicPoissonIntegral_laplaceFormula
    {Ω : Type u} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) (X : Ω → Measure NNReal)
    (hX : ProbabilityTheory.IsPoissonPointProcess nnrealLebesgue P X)
    {g : NNReal → NNReal} (hg_meas : Measurable g)
    (hg_int : Integrable (fun y : NNReal ↦ min (1 : ℝ) (g y : ℝ)) nnrealLebesgue) :
    ∀ t : NNReal,
      ∫ ω, Real.exp (-((t : ℝ) * (∫⁻ y, (g y : ENNReal) ∂ X ω).toReal)) ∂(P : Measure Ω) =
        Real.exp (∫ y : NNReal, (Real.exp (-((t : ℝ) * (g y : ℝ))) - 1) ∂nnrealLebesgue) := by
  intro t
  let Y : Ω → ℝ≥0∞ := fun ω ↦ ∫⁻ y, (g y : ENNReal) ∂ X ω
  let scaledG : NonnegativeMeasurableFunction NNReal :=
    ⟨fun y ↦ ENNReal.ofReal (t : ℝ) * g y,
      measurable_const.mul (measurable_coe_nnreal_ennreal.comp hg_meas)⟩
  let scaledExponent : ℝ≥0∞ := ∫⁻ y,
    (1 : ℝ≥0∞) - ENNReal.ofReal (ennrealExpNeg (scaledG y)) ∂nnrealLebesgue
  have hY_meas : Measurable Y := by
    -- Proof comment: measurability is inherited from the random-measure map.
    refine (Measure.measurable_lintegral (measurable_coe_nnreal_ennreal.comp hg_meas)).comp ?_
    exact hX.1.measurable
  have hAeFinite :
      ∀ᵐ ω ∂(P : Measure Ω), Y ω < ∞ :=
    deterministicPoissonIntegral_ae_ltTop_of_integrableMin P X hX hg_meas hg_int
  have hs_nonneg : 0 ≤ (t : ℝ) := t.2
  have hkernel_meas :
      AEStronglyMeasurable
        (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) nnrealLebesgue := by
    have hmeas : Measurable (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) := by
      fun_prop
    exact hmeas.aestronglyMeasurable
  have hkernel_nonneg :
      0 ≤ᵐ[nnrealLebesgue] fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ))) := by
    filter_upwards with y
    have hle : Real.exp (-((t : ℝ) * (g y : ℝ))) ≤ 1 := by
      refine Real.exp_le_one_iff.mpr ?_
      nlinarith [t.2, (g y).2]
    exact sub_nonneg.mpr hle
  have hkernel_int :
      Integrable (fun y : NNReal ↦ 1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) nnrealLebesgue := by
    have hdom :
        Integrable (fun y : NNReal ↦ max 1 (t : ℝ) * min (1 : ℝ) (g y : ℝ)) nnrealLebesgue :=
      hg_int.const_mul (max 1 (t : ℝ))
    refine Integrable.mono' hdom hkernel_meas ?_
    filter_upwards with y
    have hnonneg : 0 ≤ 1 - Real.exp (-((t : ℝ) * (g y : ℝ))) := by
      have hle : Real.exp (-((t : ℝ) * (g y : ℝ))) ≤ 1 := by
        refine Real.exp_le_one_iff.mpr ?_
        nlinarith [t.2, (g y).2]
      exact sub_nonneg.mpr hle
    have hle :
        1 - Real.exp (-((t : ℝ) * (g y : ℝ))) ≤
          max 1 (t : ℝ) * min (1 : ℝ) (g y : ℝ) :=
      poissonExpKernel_scale_le_maxMulMinOne (t : ℝ) hs_nonneg (g y)
    simpa [Real.norm_of_nonneg hnonneg] using hle
  have hscaledExponent_eq :
      scaledExponent =
        ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue) := by
    calc
      scaledExponent
          =
        ∫⁻ y, ENNReal.ofReal (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue := by
              refine lintegral_congr_ae ?_
              filter_upwards with y
              simpa [scaledExponent, scaledG, ENNReal.ofReal_mul, hs_nonneg] using
                poissonLaplaceKernel_scale_eq_ofReal (t : ℝ) hs_nonneg (g y)
      _ =
        ENNReal.ofReal
          (∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue) := by
            symm
            exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal hkernel_int hkernel_nonneg
  have hraw :
      ∫ ω, ennrealExpNeg (∫⁻ y, scaledG y ∂ X ω) ∂(P : Measure Ω) =
        ennrealExpNeg scaledExponent := by
    simpa [scaledExponent] using
      poisson_point_process_laplaceTransform P nnrealLebesgue X hX scaledG
  have hlintegral :
      (fun ω ↦ ∫⁻ y, scaledG y ∂ X ω) =
        fun ω ↦ ENNReal.ofReal (t : ℝ) * Y ω := by
    funext ω
    simpa [scaledG, Y] using
      (lintegral_const_mul' (μ := X ω) (ENNReal.ofReal (t : ℝ))
        (fun y : NNReal ↦ (g y : ℝ≥0∞))
        (measurable_coe_nnreal_ennreal.comp hg_meas))
  have hleft_ae :
      (fun ω ↦ ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω)) =ᵐ[(P : Measure Ω)]
        (fun ω ↦ Real.exp (-((t : ℝ) * (Y ω).toReal))) := by
    filter_upwards [hAeFinite] with ω hω
    have hω_ne_top : Y ω ≠ ∞ := lt_top_iff_ne_top.mp hω
    have hmul_ne_top : ENNReal.ofReal (t : ℝ) * Y ω ≠ ∞ :=
      ENNReal.mul_ne_top (by simp [t.2]) hω_ne_top
    rw [ennrealExpNeg, if_neg hmul_ne_top, ENNReal.toReal_mul]
    simpa using congrArg (fun r : ℝ ↦ Real.exp (-(r * (Y ω).toReal)))
      (ENNReal.toReal_ofReal t.2)
  calc
    ∫ ω, Real.exp (-((t : ℝ) * (∫⁻ y, (g y : ENNReal) ∂ X ω).toReal)) ∂(P : Measure Ω)
        = ∫ ω, ennrealExpNeg (ENNReal.ofReal (t : ℝ) * Y ω) ∂(P : Measure Ω) := by
            -- Proof comment: on the almost-sure finite event, `ennrealExpNeg` becomes the
            -- ordinary exponential.
            symm
            exact integral_congr_ae hleft_ae
    _ = ∫ ω, ennrealExpNeg (∫⁻ y, scaledG y ∂ X ω) ∂(P : Measure Ω) := by
          congr 1
          funext ω
          symm
          exact congrArg ennrealExpNeg (congrArg (fun f ↦ f ω) hlintegral)
    _ = ennrealExpNeg scaledExponent := hraw
    _ = Real.exp (∫ y : NNReal, (Real.exp (-((t : ℝ) * (g y : ℝ))) - 1) ∂nnrealLebesgue) := by
          rw [hscaledExponent_eq, ennrealExpNeg]
          have hIntegral_nonneg :
              0 ≤ ∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue :=
            integral_nonneg_of_ae hkernel_nonneg
          simp [hIntegral_nonneg]
          rw [show
              -(∫ y : NNReal, (1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue) =
                ∫ y : NNReal, -(1 - Real.exp (-((t : ℝ) * (g y : ℝ)))) ∂nnrealLebesgue by
                symm
                exact integral_neg (f := fun y : NNReal ↦
                  1 - Real.exp (-((t : ℝ) * (g y : ℝ))))]
          refine integral_congr_ae <| Filter.Eventually.of_forall fun y ↦ ?_
          ring

end MeasureTheory.ProbabilityMeasure
