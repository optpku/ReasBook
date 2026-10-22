/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.Asymptotics.Defs
import TR_LALM_theory.Lemma_3_4
import TR_LALM_theory.Lemma_3_5
public import TR_LALM_theory.Theorem_3_6.Admissibility
public import TR_LALM_theory.Theorem_3_6.Complexity
public import TR_LALM_theory.Theorem_3_6.OperationalTrace
public import TR_LALM_theory.Theorem_3_6.Schedule
public import TR_LALM_theory.Theorem_3_6.UniformOutput

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.StochasticRun

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+}

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Theorem 3.6: the stochastic residual mean square only depends
on the almost-everywhere classes of its point and multiplier arguments. -/
private lemma residualMeanSquare_congr
    {x x' : Ω → EuclideanSpace ℝ (Fin n)}
    {multiplier multiplier' : Ω → EuclideanSpace ℝ (Fin m)}
    (hx : x =ᵐ[ℙ] x') (hmultiplier : multiplier =ᵐ[ℙ] multiplier') :
    KKT.Stochastic.residualMeanSquare ℙ f c x multiplier =
      KKT.Stochastic.residualMeanSquare ℙ f c x' multiplier' := by
  rw [KKT.Stochastic.residualMeanSquare_def,
    KKT.Stochastic.residualMeanSquare_def]
  exact lintegral_congr_ae
    (hx.comp₂
      (fun point dual ↦ ENNReal.ofReal (KKT.residual f c point dual ^ 2))
      hmultiplier)

/-- Helper for Theorem 3.6: every stochastic step mean square is
nonnegative. -/
private lemma stepMeanSquare_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.stepMeanSquare k := by
  rw [run.stepMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.step k ω‖

/-- Helper for Theorem 3.6: every stochastic gradient-error mean square is
nonnegative. -/
private lemma gradientErrorMeanSquare_nonneg
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b) (k : ℕ) :
    0 ≤ run.gradientErrorMeanSquare k := by
  rw [run.gradientErrorMeanSquare_def]
  exact integral_nonneg fun ω ↦ sq_nonneg ‖run.gradientError k ω‖

/-- Helper for Theorem 3.6: radial clipping is a measurable map on Euclidean
space. -/
private lemma measurableClip (G : ℝ≥0) :
    Measurable (SPIDER.clip G :
      EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) := by
  unfold SPIDER.clip
  apply Measurable.ite
  · exact measurableSet_le continuous_norm.measurable measurable_const
  · exact measurable_id
  · exact (measurable_const.div continuous_norm.measurable).smul measurable_id

/-- Helper for Theorem 3.6: squared projected-gradient errors are integrable
along a pathwise-admissible stochastic prefix. -/
private lemma integrableGradientErrorSquare
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {K k : ℕ} (h_admissible : run.IsAdmissiblePrefix K) (hk : k < K) :
    Integrable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) ℙ := by
  have hestimate : AEMeasurable (run.gradientEstimate k) ℙ := by
    have hcomposed := (measurableClip h.gradientBound).comp_aemeasurable
      (run.aemeasurable_rawEstimate k)
    have hestimateEq :
        run.gradientEstimate k =
          SPIDER.clip h.gradientBound ∘
            SPIDER.rawEstimate oracle run.point run.sample Q B b k := by
      funext ω
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      rfl
    rw [hestimateEq]
    exact hcomposed
  have hgradientExtension : AEMeasurable
      (fun ω ↦ h.objectiveGradientExtension (run.point k ω)) ℙ :=
    h.measurable_objectiveGradientExtension.comp_aemeasurable
      (run.aemeasurable_point k)
  have hgradientEq :
      (fun ω ↦ h.objectiveGradientExtension (run.point k ω)) =ᵐ[ℙ]
        fun ω ↦ gradient f (run.point k ω) := by
    filter_upwards [] with ω
    have hx : run.point k ω ∈ h.region :=
      (run.pointsInRegion_iff K).mp h_admissible.pointsInRegion k hk ω
    exact h.objectiveGradientExtension_eq hx
  have hgradient : AEMeasurable (fun ω ↦ gradient f (run.point k ω)) ℙ :=
    hgradientExtension.congr hgradientEq
  have herror : AEMeasurable (run.gradientError k) ℙ := by
    have herrorEq :
        run.gradientError k =
          fun ω ↦ run.gradientEstimate k ω - gradient f (run.point k ω) := by
      funext ω
      exact run.gradientError_apply k ω
    rw [herrorEq]
    exact hestimate.sub hgradient
  have hsquareMeasurable :
      AEStronglyMeasurable (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) ℙ :=
    (herror.norm.pow_const 2).aestronglyMeasurable
  have hbound (ω : Ω) :
      ‖(‖run.gradientError k ω‖ ^ 2 : ℝ)‖ ≤
        (2 * (h.gradientBound : ℝ)) ^ 2 := by
    have hx :=
      (run.pointsInRegion_iff K).mp h_admissible.pointsInRegion k hk ω
    have hestimateNorm : ‖run.gradientEstimate k ω‖ ≤ h.gradientBound := by
      rw [run.gradientEstimate_apply, SPIDER.estimate_apply]
      exact SPIDER.norm_clip_le h.gradientBound _
    have hgradientNorm : ‖gradient f (run.point k ω)‖ ≤ h.gradientBound :=
      h.norm_gradient_le _ hx
    have herrorNorm :
        ‖run.gradientError k ω‖ ≤ 2 * (h.gradientBound : ℝ) := by
      rw [run.gradientError_apply]
      calc
        ‖run.gradientEstimate k ω - gradient f (run.point k ω)‖ ≤
            ‖run.gradientEstimate k ω‖ + ‖gradient f (run.point k ω)‖ :=
          norm_sub_le _ _
        _ ≤ 2 * (h.gradientBound : ℝ) := by linarith
    have hclipBoundNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) := by positivity
    have hsquare :=
      (sq_le_sq₀ (norm_nonneg _) hclipBoundNonneg).2 herrorNorm
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
  exact Integrable.mono' (integrable_const _)
    hsquareMeasurable (ae_of_all ℙ hbound)

/-- Helper for Theorem 3.6: adjacent pairs of a nonnegative sequence are
bounded by twice its full prefix sum. -/
private lemma sumAdjacent_le_two_range (a : ℕ → ℝ) (K : ℕ) (hK : 2 ≤ K)
    (ha : ∀ k, 0 ≤ a k) :
    (∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1))) ≤
      2 * ∑ k ∈ Finset.range K, a k := by
  have hinterval : Finset.Icc 1 (K - 1) = Finset.Ico 1 K := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    omega
  have hshift :
      (∑ k ∈ Finset.Icc 1 (K - 1), a (k - 1)) =
        ∑ k ∈ Finset.range (K - 1), a k := by
    rw [hinterval, Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    congr 1
    omega
  have hrangeIndex : K - 1 ≤ K := by omega
  have hrange :
      (∑ k ∈ Finset.range (K - 1), a k) ≤ ∑ k ∈ Finset.range K, a k := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_mono hrangeIndex) (fun k _ _ ↦ ha k)
  have honeLeK : 1 ≤ K := by omega
  have hrangeSplit :
      (∑ k ∈ Finset.range K, a k) =
        a 0 + ∑ k ∈ Finset.Icc 1 (K - 1), a k := by
    rw [hinterval, Finset.sum_range_eq_add_Ico a honeLeK]
  rw [Finset.sum_add_distrib, hshift]
  rw [hrangeSplit]
  linarith [ha 0]

/-- Helper for Theorem 3.6: the stochastic residual comparison constant is
nonnegative for the admissible positive algorithm parameters. -/
private lemma stochasticResidualConstant_nonneg
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    0 ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
      params.multiplierBound := by
  rw [LALM.stochasticResidualConstant_def]
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hsecond :
      0 ≤ 2 + LALM.multiplierErrorConstant h / (params.rho : ℝ) ^ 2 := by
    positivity
  exact hsecond.trans (le_max_right _ _)

/-- Helper for Theorem 3.6: one fixed-index stochastic residual mean square
is controlled by the neighboring step and gradient-error mean squares. -/
private lemma fixedResidualMeanSquare_le
    (run : StochasticRun h oracle ℙ x₀ multiplier₀ params Q B b)
    {K k : ℕ} (h_admissible : run.IsAdmissiblePrefix K)
    (hk_pos : 1 ≤ k) (hk : k < K) :
    KKT.Stochastic.residualMeanSquare ℙ f c
        (run.point (k + 1)) (run.multiplier (k + 1)) ≤
      ENNReal.ofReal
        (LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run.stepMeanSquare k + run.stepMeanSquare (k - 1) +
            run.gradientErrorMeanSquare k + run.gradientErrorMeanSquare (k - 1))) := by
  let C := LALM.stochasticResidualConstant h params.delta params.beta params.rho
    params.multiplierBound
  let moments : Ω → ℝ := fun ω ↦
    ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
      ‖run.gradientError k ω‖ ^ 2 + ‖run.gradientError (k - 1) ω‖ ^ 2
  have hstepK := integrableStepSquare run h_admissible hk
  have hkPrev : k - 1 < K := by omega
  have hstepPrev := integrableStepSquare run h_admissible hkPrev
  have herrorK := integrableGradientErrorSquare run h_admissible hk
  have herrorPrev := integrableGradientErrorSquare run h_admissible hkPrev
  have hmoments : Integrable moments ℙ := by
    exact ((hstepK.add hstepPrev).add herrorK).add herrorPrev
  have hright : Integrable (fun ω ↦ C * moments ω) ℙ := hmoments.const_mul C
  have hC : 0 ≤ C := stochasticResidualConstant_nonneg h params
  have hmomentsNonneg (ω : Ω) : 0 ≤ moments ω := by
    dsimp only [moments]
    positivity
  have hrightNonneg : 0 ≤ᵐ[ℙ] fun ω ↦ C * moments ω :=
    ae_of_all ℙ fun ω ↦ mul_nonneg hC (hmomentsNonneg ω)
  have hmomentsIntegral :
      (∫ ω, moments ω ∂ℙ) =
        run.stepMeanSquare k + run.stepMeanSquare (k - 1) +
          run.gradientErrorMeanSquare k + run.gradientErrorMeanSquare (k - 1) := by
    have hfirst := integral_add hstepK hstepPrev
    have hsecond := integral_add (hstepK.add hstepPrev) herrorK
    have hthird :=
      integral_add ((hstepK.add hstepPrev).add herrorK) herrorPrev
    have hsecond' :
        (∫ ω, ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
            ‖run.gradientError k ω‖ ^ 2 ∂ℙ) =
          (∫ ω, ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂ℙ := by
      simpa only [Pi.add_apply] using hsecond
    calc
      (∫ ω, moments ω ∂ℙ) =
          (∫ ω, ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 +
              ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        simpa only [moments, Pi.add_apply] using hthird
      _ = ((∫ ω, ‖run.step k ω‖ ^ 2 + ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
          ∫ ω, ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        rw [hsecond']
      _ = (((∫ ω, ‖run.step k ω‖ ^ 2 ∂ℙ) +
              ∫ ω, ‖run.step (k - 1) ω‖ ^ 2 ∂ℙ) +
            ∫ ω, ‖run.gradientError k ω‖ ^ 2 ∂ℙ) +
          ∫ ω, ‖run.gradientError (k - 1) ω‖ ^ 2 ∂ℙ := by
        rw [hfirst]
      _ = run.stepMeanSquare k + run.stepMeanSquare (k - 1) +
          run.gradientErrorMeanSquare k +
            run.gradientErrorMeanSquare (k - 1) := rfl
  rw [KKT.Stochastic.residualMeanSquare_def]
  calc
    (∫⁻ ω, ENNReal.ofReal
        (KKT.residual f c (run.point (k + 1) ω)
          (run.multiplier (k + 1) ω) ^ 2) ∂ℙ) ≤
        ∫⁻ ω, ENNReal.ofReal (C * moments ω) ∂ℙ := by
      refine lintegral_mono fun ω ↦ ENNReal.ofReal_le_ofReal ?_
      exact run.residual_sq_le_of_isAdmissiblePrefix h_admissible hk_pos hk ω
    _ = ENNReal.ofReal (∫ ω, C * moments ω ∂ℙ) :=
      (ofReal_integral_eq_lintegral_ofReal hright hrightNonneg).symm
    _ = ENNReal.ofReal (C * ∫ ω, moments ω ∂ℙ) := by
      rw [integral_const_mul]
    _ = ENNReal.ofReal
        (LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run.stepMeanSquare k + run.stepMeanSquare (k - 1) +
            run.gradientErrorMeanSquare k +
              run.gradientErrorMeanSquare (k - 1))) := by
      rw [hmomentsIntegral]

omit [IsProbabilityMeasure ℙ] in
/-- Helper for Theorem 3.6: a countably indexed family of almost-everywhere
measurable functions is almost-everywhere measurable on the corresponding
product space. -/
private lemma aemeasurable_indexedProduct
    {E : Type*} [MeasurableSpace E] (μ : Measure ℕ)
    (g : ℕ → Ω → E) (hg : ∀ k, AEMeasurable (g k) ℙ) :
    AEMeasurable (fun output : ℕ × Ω ↦ g output.1 output.2) (μ.prod ℙ) := by
  let g' : ℕ → Ω → E := fun k ↦ (hg k).mk (g k)
  have hg'Measurable (k : ℕ) : Measurable (g' k) := by
    exact (hg k).measurable_mk
  have hglobalMeasurable :
      Measurable (fun output : ℕ × Ω ↦ g' output.1 output.2) :=
    measurable_from_prod_countable_right hg'Measurable
  have hsections : ∀ᵐ ω ∂ℙ, ∀ k, g' k ω = g k ω := by
    apply ae_all_iff.mpr
    intro k
    exact (hg k).ae_eq_mk.symm
  have hlifted :
      ∀ᵐ output ∂μ.prod ℙ, ∀ k, g' k output.2 = g k output.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ℙ)).ae hsections
  have hglobalAE :
      (fun output : ℕ × Ω ↦ g' output.1 output.2) =ᵐ[μ.prod ℙ]
        fun output ↦ g output.1 output.2 := by
    filter_upwards [hlifted] with output houtput
    exact houtput output.1
  exact hglobalMeasurable.aemeasurable.congr hglobalAE

namespace UniformOutput

/-- Theorem 3.6 (1): with the prescribed SPIDER schedule and an almost-surely
admissible length-`K` stochastic NR-LALM prefix, the independent uniform output has
expected squared KKT residual at most `C_st / (K - 1)`. -/
theorem residualMeanSquare_le
    (K : ℕ) (hK : 2 ≤ K)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_admissible : run.IsAEAdmissiblePrefix K) :
    residualMeanSquare run K hK ≤
      ENNReal.ofReal (complexityConstant h oracle params / ((K : ℝ) - 1)) := by
  obtain ⟨run', hrun'Admissible, hpointAE, hmultiplierAE, _, _⟩ :=
    h_admissible.exists_pathwiseVersion run K
  have hrunSupport :=
    hasRegularOutputPoints_of_isAEAdmissiblePrefix run K h_admissible
  have hrun'Support :=
    hasRegularOutputPoints_of_isAEAdmissiblePrefix run' K hrun'Admissible.isAE
  have hbatch := SPIDER.innerBatchSize_isSufficient h oracle params K
  have herrorAverage :=
    run'.averageGradientErrorMeanSquare_le_of_isAdmissiblePrefix K hK
      hrun'Admissible hbatch
  have hstepAverage :=
    run'.averageStepMeanSquare_le_of_isAdmissiblePrefix K hK
      hrun'Admissible hbatch
  rw [SPIDER.refreshBatchSize_coe K hK] at herrorAverage hstepAverage
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have herrorTotalRaw := (div_le_iff₀ hKreal).mp herrorAverage
  have hstepTotalRaw := (div_le_iff₀ hKreal).mp hstepAverage
  have herrorTotal :
      (∑ k ∈ Finset.range K, run'.gradientErrorMeanSquare k) ≤
        errorAverageConstant h oracle params := by
    calc
      (∑ k ∈ Finset.range K, run'.gradientErrorMeanSquare k) ≤
          (2 * (oracle.noiseLevel : ℝ) ^ 2 / K +
            initialStepBound h params / (errorStepConstant h params * K)) * K :=
        herrorTotalRaw
      _ = errorAverageConstant h oracle params := by
        rw [errorAverageConstant_def]
        field_simp [hKzero]
  have hstepTotal :
      (∑ k ∈ Finset.range K, run'.stepMeanSquare k) ≤
        stepAverageConstant h oracle params := by
    calc
      (∑ k ∈ Finset.range K, run'.stepMeanSquare k) ≤
          (2 * errorStepConstant h params * (oracle.noiseLevel : ℝ) ^ 2 / K +
            2 * initialStepBound h params / K) * K := hstepTotalRaw
      _ = stepAverageConstant h oracle params := by
        rw [stepAverageConstant_def]
        field_simp [hKzero]
  let a : ℕ → ℝ := fun k ↦
    run'.stepMeanSquare k + run'.gradientErrorMeanSquare k
  have ha (k : ℕ) : 0 ≤ a k := by
    exact add_nonneg (stepMeanSquare_nonneg run' k)
      (gradientErrorMeanSquare_nonneg run' k)
  have htotalRange :
      (∑ k ∈ Finset.range K, a k) ≤
        stepAverageConstant h oracle params + errorAverageConstant h oracle params := by
    rw [Finset.sum_add_distrib]
    exact add_le_add hstepTotal herrorTotal
  have hadjacent := sumAdjacent_le_two_range a K hK ha
  have hC := stochasticResidualConstant_nonneg h params
  have hrealSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run'.stepMeanSquare k + run'.stepMeanSquare (k - 1) +
            run'.gradientErrorMeanSquare k +
              run'.gradientErrorMeanSquare (k - 1))) ≤
        complexityConstant h oracle params := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
        LALM.stochasticResidualConstant h params.delta params.beta params.rho
          params.multiplierBound *
          (run'.stepMeanSquare k + run'.stepMeanSquare (k - 1) +
            run'.gradientErrorMeanSquare k +
              run'.gradientErrorMeanSquare (k - 1))) =
          LALM.stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
            ∑ k ∈ Finset.Icc 1 (K - 1), (a k + a (k - 1)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        dsimp only [a]
        ring
      _ ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
            (2 * ∑ k ∈ Finset.range K, a k) :=
        mul_le_mul_of_nonneg_left hadjacent hC
      _ ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
            params.multiplierBound *
            (2 * (stepAverageConstant h oracle params +
              errorAverageConstant h oracle params)) := by
        gcongr
      _ = complexityConstant h oracle params := by
        rw [complexityConstant_def]
        ring
  have htermNonneg (k : ℕ) (_hk : k ∈ Finset.Icc 1 (K - 1)) :
      0 ≤ LALM.stochasticResidualConstant h params.delta params.beta params.rho
        params.multiplierBound *
        (run'.stepMeanSquare k + run'.stepMeanSquare (k - 1) +
          run'.gradientErrorMeanSquare k +
            run'.gradientErrorMeanSquare (k - 1)) := by
    apply mul_nonneg hC
    exact add_nonneg
      (add_nonneg
        (add_nonneg (stepMeanSquare_nonneg run' k)
          (stepMeanSquare_nonneg run' (k - 1)))
        (gradientErrorMeanSquare_nonneg run' k))
      (gradientErrorMeanSquare_nonneg run' (k - 1))
  have hfixedSum :
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run'.point (k + 1)) (run'.multiplier (k + 1))) ≤
        ENNReal.ofReal (complexityConstant h oracle params) := by
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
        KKT.Stochastic.residualMeanSquare ℙ f c
          (run'.point (k + 1)) (run'.multiplier (k + 1))) ≤
          ∑ k ∈ Finset.Icc 1 (K - 1), ENNReal.ofReal
            (LALM.stochasticResidualConstant h params.delta params.beta params.rho
              params.multiplierBound *
              (run'.stepMeanSquare k + run'.stepMeanSquare (k - 1) +
                run'.gradientErrorMeanSquare k +
                  run'.gradientErrorMeanSquare (k - 1))) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkbounds := Finset.mem_Icc.mp hk
        have hklt : k < K := by omega
        exact fixedResidualMeanSquare_le run' hrun'Admissible hkbounds.1 hklt
      _ = ENNReal.ofReal
          (∑ k ∈ Finset.Icc 1 (K - 1),
            LALM.stochasticResidualConstant h params.delta params.beta params.rho
              params.multiplierBound *
              (run'.stepMeanSquare k + run'.stepMeanSquare (k - 1) +
                run'.gradientErrorMeanSquare k +
                  run'.gradientErrorMeanSquare (k - 1))) :=
        (ENNReal.ofReal_sum_of_nonneg htermNonneg).symm
      _ ≤ ENNReal.ofReal (complexityConstant h oracle params) :=
        ENNReal.ofReal_le_ofReal hrealSum
  have hcard : (Finset.Icc 1 (K - 1)).card = K - 1 := by
    simp only [Nat.card_Icc]
    omega
  have hKnatOne : 1 < K := by omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnatOne
  have hdenominator : 0 < (K : ℝ) - 1 := by
    linarith
  have hOneNonneg : (0 : ℝ) ≤ 1 := by norm_num
  have hrun'Rate :
      residualMeanSquare run' K hK ≤
        ENNReal.ofReal (complexityConstant h oracle params / ((K : ℝ) - 1)) := by
    rw [residualMeanSquare_eq_expect run' K hK hrun'Support, hcard,
      ENNReal.natCast_sub, Nat.cast_one]
    calc
      (∑ k ∈ Finset.Icc 1 (K - 1),
          KKT.Stochastic.residualMeanSquare ℙ f c
            (run'.point (k + 1)) (run'.multiplier (k + 1))) /
            ((K : ℝ≥0∞) - 1) ≤
          ENNReal.ofReal (complexityConstant h oracle params) /
            ((K : ℝ≥0∞) - 1) :=
        ENNReal.div_le_div_right hfixedSum _
      _ = ENNReal.ofReal
          (complexityConstant h oracle params / ((K : ℝ) - 1)) := by
        rw [ENNReal.ofReal_div_of_pos hdenominator,
          ENNReal.ofReal_sub (K : ℝ) hOneNonneg,
          ENNReal.ofReal_natCast, ENNReal.ofReal_one]
  have houtputEq : residualMeanSquare run K hK = residualMeanSquare run' K hK := by
    rw [residualMeanSquare_eq_expect run K hK hrunSupport,
      residualMeanSquare_eq_expect run' K hK hrun'Support]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    exact residualMeanSquare_congr (hpointAE (k + 1)).symm
      (hmultiplierAE (k + 1)).symm
  exact houtputEq.trans_le hrun'Rate

/-- Theorem 3.6 (2): under the exact `C_st * ε⁻² ≤ K - 1` threshold, the
independent uniform output is a stochastic `ε`-KKT pair. -/
theorem isApproximatePair_of_iterationBound
    (K : ℕ) (hK : 2 ≤ K)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K)
    (h_admissible : run.IsAEAdmissiblePrefix K)
    (ε : ℝ≥0) (ε_pos : 0 < ε)
    (h_iterations :
      complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2 ≤ (K : ℝ) - 1) :
    KKT.Stochastic.IsApproximatePair (measure K hK ℙ) f c ε
      (point run) (multiplier run) := by
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast ε_pos
  have hεzero : (ε : ℝ) ≠ 0 := hεreal.ne'
  have hKnatOne : 1 < K := by omega
  have hKrealOne : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnatOne
  have hdenominator : 0 < (K : ℝ) - 1 := by
    linarith
  have hrealRate :
      complexityConstant h oracle params / ((K : ℝ) - 1) ≤ (ε : ℝ) ^ 2 := by
    apply (div_le_iff₀ hdenominator).2
    calc
      complexityConstant h oracle params =
          (complexityConstant h oracle params * (ε : ℝ)⁻¹ ^ 2) *
            (ε : ℝ) ^ 2 := by
        field_simp [hεzero]
      _ ≤ ((K : ℝ) - 1) * (ε : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right h_iterations (sq_nonneg (ε : ℝ))
      _ = (ε : ℝ) ^ 2 * ((K : ℝ) - 1) := by ring
  have hrate := residualMeanSquare_le K hK run h_admissible
  have hresidual :
      KKT.Stochastic.residualMeanSquare (measure K hK ℙ) f c
          (point run) (multiplier run) ≤ (ε : ℝ≥0∞) ^ 2 := by
    calc
      KKT.Stochastic.residualMeanSquare (measure K hK ℙ) f c
          (point run) (multiplier run) = residualMeanSquare run K hK := rfl
      _ ≤ ENNReal.ofReal
          (complexityConstant h oracle params / ((K : ℝ) - 1)) := hrate
      _ ≤ ENNReal.ofReal ((ε : ℝ) ^ 2) :=
        ENNReal.ofReal_le_ofReal hrealRate
      _ = (ε : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_pow (NNReal.coe_nonneg ε),
          ENNReal.ofReal_coe_nnreal]
  have hpointMeasurable :
      AEMeasurable (point run) (measure K hK ℙ) := by
    change AEMeasurable
      (fun output : ℕ × Ω ↦ run.point (output.1 + 1) output.2)
      ((indexLaw K hK).toMeasure.prod ℙ)
    exact aemeasurable_indexedProduct (indexLaw K hK).toMeasure
      (fun k ↦ run.point (k + 1))
      (fun k ↦ run.aemeasurable_point (k + 1))
  have hmultiplierMeasurable :
      AEMeasurable (multiplier run) (measure K hK ℙ) := by
    change AEMeasurable
      (fun output : ℕ × Ω ↦ run.multiplier (output.1 + 1) output.2)
      ((indexLaw K hK).toMeasure.prod ℙ)
    exact aemeasurable_indexedProduct (indexLaw K hK).toMeasure
      (fun k ↦ run.multiplier (k + 1))
      (fun k ↦ run.aemeasurable_multiplier (k + 1))
  exact KKT.Stochastic.IsApproximatePair.of_residualMeanSquare_le
    hpointMeasurable hmultiplierMeasurable hresidual

end UniformOutput

/-- Helper for Theorem 3.6: among the first `K` indices, at most `q` are
divisible by `q` whenever `K ≤ q ^ 2`. -/
private lemma refreshIndexCard_le
    (K q : ℕ) (hq : 0 < q) (hKq : K ≤ q * q) :
    ((Finset.range K).filter (fun k ↦ k % q = 0)).card ≤ q := by
  have hcard :
      ((Finset.range K).filter (fun k ↦ k % q = 0)).card ≤
        (Finset.range q).card := by
    apply Finset.card_le_card_of_injOn (fun k ↦ k / q)
    · intro k hk
      have hk' := Finset.mem_filter.mp hk
      apply Finset.mem_range.mpr
      rw [Nat.div_lt_iff_lt_mul hq]
      exact lt_of_lt_of_le (Finset.mem_range.mp hk'.1) hKq
    · intro x hx y hy hxy
      change x / q = y / q at hxy
      have hx' := Finset.mem_filter.mp hx
      have hy' := Finset.mem_filter.mp hy
      have hxmod : x % q = 0 := hx'.2
      have hymod : y % q = 0 := hy'.2
      have hxrepr := Nat.div_add_mod x q
      have hyrepr := Nat.div_add_mod y q
      calc
        x = q * (x / q) + x % q := hxrepr.symm
        _ = q * (x / q) := by rw [hxmod, Nat.add_zero]
        _ = q * (y / q) := by rw [hxy]
        _ = q * (y / q) + y % q := by rw [hymod, Nat.add_zero]
        _ = y := hyrepr
  simpa only [Finset.card_range] using hcard

/-- Helper for Theorem 3.6: the scheduled refresh period squared covers the
full iteration horizon. -/
private lemma iteration_le_refreshPeriod_sq (K : ℕ) (hK : 2 ≤ K) :
    K ≤ (SPIDER.refreshPeriod K : ℕ) * (SPIDER.refreshPeriod K : ℕ) := by
  have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
  have hsqrtSquare := Real.sq_sqrt (Nat.cast_nonneg K)
  have hsqrtCeil := Nat.le_ceil (Real.sqrt K)
  have hceilNonneg :
      (0 : ℝ) ≤ (Nat.ceil (Real.sqrt K) : ℝ) := Nat.cast_nonneg _
  have hreal :
      (K : ℝ) ≤ (Nat.ceil (Real.sqrt K) : ℝ) * Nat.ceil (Real.sqrt K) := by
    nlinarith
  rw [SPIDER.refreshPeriod_coe K hK]
  exact_mod_cast hreal

/-- Helper for Theorem 3.6: the scheduled refresh period is at most one plus
the square root of the iteration horizon. -/
private lemma refreshPeriod_le_sqrt_add_one (K : ℕ) (hK : 2 ≤ K) :
    ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := by
  rw [SPIDER.refreshPeriod_coe K hK]
  exact (Nat.ceil_lt_add_one (Real.sqrt_nonneg (K : ℝ))).le

/-- Helper for Theorem 3.6: the stochastic error-step coefficient is strictly
positive. -/
private lemma errorStepConstant_pos
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    0 < errorStepConstant h params := by
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hfirst : 0 < (2 : ℝ) / params.beta := by positivity
  have hsecond :
      0 ≤ ((4 : ℝ) / h.licqModulus ^ 2) / params.rho := by positivity
  have hsum :
      0 < (2 : ℝ) / params.beta +
        ((4 : ℝ) / h.licqModulus ^ 2) / params.rho :=
    add_pos_of_pos_of_nonneg hfirst hsecond
  rw [errorStepConstant_def, lyapunovErrorConstant_def,
    LALM.multiplierErrorConstant_def]
  positivity

/-- Helper for Theorem 3.6: the scheduled inner batch is bounded by its
real-valued linear expression in the refresh period. -/
private lemma innerBatchSize_le_linear
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) :
    ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
      2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2 *
        (SPIDER.refreshPeriod K : ℕ) + 1 := by
  let A : ℝ :=
    2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [errorStepConstant_pos h params]
  have hargument :
      0 ≤ A * (SPIDER.refreshPeriod K : ℕ) :=
    mul_nonneg hA (Nat.cast_nonneg _)
  have hceiling := Nat.ceil_lt_add_one hargument
  have honeLe :
      (1 : ℝ) ≤ A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
    linarith
  rw [SPIDER.innerBatchSize_coe, Nat.cast_max]
  apply max_le
  · simpa only [A, Nat.cast_one] using honeLe
  · dsimp only [A] at hceiling ⊢
    exact hceiling.le

/-- Helper for Theorem 3.6: the scheduled gradient counter is bounded by one
refresh-period copy of the horizon plus all inner updates. -/
private lemma gradientEvaluationCount_le_schedule
    (K : ℕ) (hK : 2 ≤ K)
    (run : SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params K) :
    run.gradientEvaluationCount K ≤
      (SPIDER.refreshPeriod K : ℕ) * K +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
  have hq : 0 < (SPIDER.refreshPeriod K : ℕ) :=
    (SPIDER.refreshPeriod K).pos
  have hrefreshCard := refreshIndexCard_le K (SPIDER.refreshPeriod K)
    hq (iteration_le_refreshPeriod_sq K hK)
  calc
    run.gradientEvaluationCount K =
        ∑ k ∈ Finset.range K,
          if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
            (SPIDER.refreshBatchSize K : ℕ)
          else 2 * (SPIDER.innerBatchSize h oracle params K : ℕ) :=
      run.gradientEvaluationCount_spec K
    _ ≤ ∑ k ∈ Finset.range K,
        ((if k % (SPIDER.refreshPeriod K : ℕ) = 0 then
            (SPIDER.refreshBatchSize K : ℕ) else 0) +
          2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      apply Finset.sum_le_sum
      intro k hk
      split
      · omega
      · omega
    _ = ((Finset.range K).filter
          (fun k ↦ k % (SPIDER.refreshPeriod K : ℕ) = 0)).card *
          (SPIDER.refreshBatchSize K : ℕ) +
        K * (2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_range, Nat.cast_id]
    _ ≤ (SPIDER.refreshPeriod K : ℕ) * K +
        K * (2 * (SPIDER.innerBatchSize h oracle params K : ℕ)) := by
      rw [SPIDER.refreshBatchSize_coe K hK]
      exact add_le_add (Nat.mul_le_mul_right K hrefreshCard) le_rfl
    _ = (SPIDER.refreshPeriod K : ℕ) * K +
        2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by ring

/-- Helper for Theorem 3.6: a natural ceiling of a fixed multiple of `ε⁻²`,
with fixed additive overhead, is `O(ε⁻²)` as `ε → 0⁺`. -/
private lemma natCeilQuadraticBudget_isBigO (C : ℝ) :
    (fun ε : ℝ≥0 ↦ ((Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) + 2 : ℕ) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- Restrict to `0 < ε < 1`, where the comparison function dominates constants.
  refine Asymptotics.IsBigO.of_bound (|C| + 3) ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds
      (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hinverse : 1 ≤ (ε : ℝ)⁻¹ := (one_le_inv₀ hεreal).2 hεrealOne
  have hinverseSq : 1 ≤ (ε : ℝ)⁻¹ ^ 2 := by
    nlinarith
  have hinverseSqNonneg : 0 ≤ (ε : ℝ)⁻¹ ^ 2 := sq_nonneg _
  -- Split on the sign of the fixed coefficient because `Nat.ceil` truncates negatives.
  by_cases hC : 0 ≤ C
  · have hargument : 0 ≤ C * (ε : ℝ)⁻¹ ^ 2 :=
      mul_nonneg hC hinverseSqNonneg
    have hceiling := Nat.ceil_lt_add_one hargument
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), Nat.cast_add, Nat.cast_ofNat,
      Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg, abs_of_nonneg hC]
    have hcoefficient : 0 ≤ C + 3 := by positivity
    nlinarith [mul_nonneg hcoefficient (sub_nonneg.mpr hinverseSq)]
  · have hargument : C * (ε : ℝ)⁻¹ ^ 2 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hinverseSqNonneg
    have hceiling : Nat.ceil (C * (ε : ℝ)⁻¹ ^ 2) = 0 :=
      Nat.ceil_eq_zero.mpr hargument
    have htwo : (0 : ℝ) ≤ 2 := by norm_num
    rw [hceiling, Nat.zero_add, Nat.cast_ofNat, Real.norm_eq_abs,
      abs_of_nonneg htwo, Real.norm_eq_abs, abs_of_nonneg hinverseSqNonneg]
    have hcoefficient : 0 ≤ |C| + 3 := by positivity
    calc
      (2 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      _ = (|C| + 3) * 1 := (mul_one _).symm
      _ ≤ (|C| + 3) * (ε : ℝ)⁻¹ ^ 2 :=
        mul_le_mul_of_nonneg_left hinverseSq hcoefficient

/-- Theorem 3.6 (3): with the prescribed SPIDER schedule and canonical
`O(ε⁻²)` iteration budget, the stochastic-gradient evaluation count is
`O(ε⁻³)` as `ε → 0⁺`. -/
theorem gradientEvaluationCount_isBigO
    (run : ∀ ε : ℝ≥0, SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params
      (iterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦
      ((run ε).gradientEvaluationCount (iterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 3 := by
  let C : ℝ := complexityConstant h oracle params
  let D : ℝ := |C| + 3
  let A : ℝ :=
    2 * errorStepConstant h params * oracle.meanSquareLipschitz ^ 2
  let M : ℝ := D * ((D + 1) + 2 * (A * (D + 1) + 1))
  refine Asymptotics.IsBigO.of_bound M ?_
  have hzeroLtOne : (0 : ℝ≥0) < 1 := by norm_num
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hzeroLtOne)] with ε hεpos hεone
  let x : ℝ := (ε : ℝ)⁻¹
  let K : ℕ := iterationBudget h oracle params ε
  have hεreal : 0 < (ε : ℝ) := by
    exact_mod_cast hεpos
  have hεrealOne : (ε : ℝ) ≤ 1 := by
    exact_mod_cast hεone.le
  have hx : 1 ≤ x := by
    dsimp only [x]
    exact (one_le_inv₀ hεreal).2 hεrealOne
  have hxNonneg : 0 ≤ x := le_trans zero_le_one hx
  have hxSq : 1 ≤ x ^ 2 := by nlinarith
  have hxSqNonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hD : 1 ≤ D := by
    dsimp only [D]
    linarith [abs_nonneg C]
  have hDNonneg : 0 ≤ D := le_trans zero_le_one hD
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity [errorStepConstant_pos h params]
  have hK : 2 ≤ K := by
    dsimp only [K]
    exact (iterationBudget_spec h oracle params ε).1
  have hKNonneg : 0 ≤ (K : ℝ) := Nat.cast_nonneg K
  have hzeroOne : (0 : ℝ) ≤ 1 := by norm_num
  have hKBound : (K : ℝ) ≤ D * x ^ 2 := by
    dsimp only [K]
    rw [iterationBudget_def]
    by_cases hC : 0 ≤ C
    · have hargument : 0 ≤ C * x ^ 2 := mul_nonneg hC hxSqNonneg
      have hceiling := Nat.ceil_lt_add_one hargument
      have hCplus : 0 ≤ C + 3 := by positivity
      rw [Nat.cast_add, Nat.cast_ofNat]
      dsimp only [D]
      rw [abs_of_nonneg hC]
      nlinarith [mul_nonneg hCplus (sub_nonneg.mpr hxSq)]
    · have hargument : C * x ^ 2 ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hC) hxSqNonneg
      have hceiling : Nat.ceil (C * x ^ 2) = 0 :=
        Nat.ceil_eq_zero.mpr hargument
      rw [hceiling, Nat.zero_add, Nat.cast_ofNat]
      dsimp only [D]
      have hcoefficient : 0 ≤ |C| + 3 := by positivity
      have hthree : (3 : ℝ) ≤ |C| + 3 := by linarith [abs_nonneg C]
      have hproduct : (3 : ℝ) * 1 ≤ (|C| + 3) * x ^ 2 :=
        mul_le_mul hthree hxSq hzeroOne hcoefficient
      nlinarith
  have hrefreshRaw := refreshPeriod_le_sqrt_add_one K hK
  have hDsq : D ≤ D ^ 2 := by nlinarith
  have hKSquare : (K : ℝ) ≤ (D * x) ^ 2 := by
    calc
      (K : ℝ) ≤ D * x ^ 2 := hKBound
      _ ≤ D ^ 2 * x ^ 2 :=
        mul_le_mul_of_nonneg_right hDsq hxSqNonneg
      _ = (D * x) ^ 2 := by ring
  have hsqrtK : Real.sqrt K ≤ D * x := by
    have hsqrtNonneg := Real.sqrt_nonneg (K : ℝ)
    have hsqrtSquare := Real.sq_sqrt hKNonneg
    have hDxNonneg : 0 ≤ D * x := mul_nonneg hDNonneg hxNonneg
    nlinarith
  have hrefreshBound :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ (D + 1) * x := by
    calc
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) ≤ Real.sqrt K + 1 := hrefreshRaw
      _ ≤ D * x + 1 := by
        simpa only [add_comm] using add_le_add_right hsqrtK 1
      _ ≤ (D + 1) * x := by nlinarith
  have hinnerRaw := innerBatchSize_le_linear h oracle params K
  have hinnerBound :
      ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
        (A * (D + 1) + 1) * x := by
    calc
      ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) ≤
          A * (SPIDER.refreshPeriod K : ℕ) + 1 := by
        simpa only [A] using hinnerRaw
      _ ≤ A * ((D + 1) * x) + 1 := by
        gcongr
      _ ≤ (A * (D + 1) + 1) * x := by
        nlinarith [mul_nonneg hA (add_nonneg hDNonneg zero_le_one)]
  have hcountNat := gradientEvaluationCount_le_schedule K hK (run ε)
  have hcountReal :
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤
        ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := by
    exact_mod_cast hcountNat
  have hrefreshNonneg :
      0 ≤ ((SPIDER.refreshPeriod K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hinnerNonneg :
      0 ≤ ((SPIDER.innerBatchSize h oracle params K : ℕ) : ℝ) := Nat.cast_nonneg _
  have hrefreshWork :
      ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K ≤
        ((D + 1) * x) * (D * x ^ 2) := by
    exact mul_le_mul hrefreshBound hKBound hKNonneg
      (mul_nonneg (add_nonneg hDNonneg zero_le_one) hxNonneg)
  have hinnerCoefficientNonneg : 0 ≤ A * (D + 1) + 1 := by
    positivity
  have hinnerWork :
      (2 : ℝ) * K * (SPIDER.innerBatchSize h oracle params K : ℕ) ≤
        2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) := by
    gcongr
  have hcountBound :
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤ M * x ^ 3 := by
    calc
      (((run ε).gradientEvaluationCount K : ℕ) : ℝ) ≤
          ((SPIDER.refreshPeriod K : ℕ) : ℝ) * K +
            2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) := hcountReal
      _ ≤ ((D + 1) * x) * (D * x ^ 2) +
          2 * (D * x ^ 2) * ((A * (D + 1) + 1) * x) :=
        add_le_add hrefreshWork hinnerWork
      _ = M * x ^ 3 := by
        dsimp only [M]
        ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _),
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hxNonneg 3)]
  simpa only [K, x] using hcountBound

/-- Theorem 3.6 (4): with the canonical stochastic iteration budget, the
constraint-evaluation count is `O(ε⁻²)` as `ε → 0⁺`. -/
theorem constraintEvaluationCount_isBigO
    (run : ∀ ε : ℝ≥0, SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params
      (iterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦
      ((run ε).constraintEvaluationCount (iterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- The counter specification reduces the claim to the shared ceiling budget.
  simpa only [constraintEvaluationCount_spec, iterationBudget_def] using
    natCeilQuadraticBudget_isBigO (complexityConstant h oracle params)

/-- Theorem 3.6 (5): with the canonical stochastic iteration budget, the
constraint-Jacobian evaluation count is `O(ε⁻²)` as `ε → 0⁺`. -/
theorem jacobianEvaluationCount_isBigO
    (run : ∀ ε : ℝ≥0, SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params
      (iterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦
      ((run ε).jacobianEvaluationCount (iterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- One Jacobian evaluation is recorded for each transition in the budget.
  simpa only [jacobianEvaluationCount_spec, iterationBudget_def] using
    natCeilQuadraticBudget_isBigO (complexityConstant h oracle params)

/-- Theorem 3.6 (6): with the canonical stochastic iteration budget, the
Jacobian-induced linear-system solve count is `O(ε⁻²)` as `ε → 0⁺`. -/
theorem linearSystemSolveCount_isBigO
    (run : ∀ ε : ℝ≥0, SPIDER.ScheduledRun h oracle ℙ x₀ multiplier₀ params
      (iterationBudget h oracle params ε)) :
    (fun ε : ℝ≥0 ↦
      ((run ε).linearSystemSolveCount (iterationBudget h oracle params ε) : ℝ))
      =O[nhdsWithin 0 (Set.Ioi 0)] fun ε : ℝ≥0 ↦ (ε : ℝ)⁻¹ ^ 2 := by
  -- One exact Jacobian-induced solve is recorded for each transition.
  simpa only [linearSystemSolveCount_spec, iterationBudget_def] using
    natCeilQuadraticBudget_isBigO (complexityConstant h oracle params)

end LALM.StochasticRun

end
