/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_66
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_67
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_14
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Definition_25_10
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Lemma_25_13
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_9
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_18.Compensator
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_18.IntegralProcess

open Filter MeasureTheory ProbabilityTheory
open MeasureTheory.MemPredictableStepProcessClosure
open scoped ENNReal Topology

noncomputable section

namespace ProbabilityTheory

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {ℱ : Filtration NNReal mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ]

private abbrev Process (Ω : Type u) := NNReal → Ω → ℝ

variable {W H M : Process Ω}

/-- Source-facing finite-energy hypothesis for the current Brownian-Itô item: `H` is
progressively measurable, its squared sample paths are integrable on every finite horizon almost
surely, and the compensator `ω ↦ ∫_0^T H_s(ω)^2 ds` has finite expectation on every positive
finite horizon. -/
structure HasFiniteExpectedEnergyOnEveryHorizon
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) (H : Process Ω) : Prop where
  progMeasurable : MeasureTheory.ProgMeasurable ℱ H
  interval_square_integrable :
    ∀ ⦃T : NNReal⦄, ∀ᵐ ω ∂μ,
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ))
  finite_expectation :
    ∀ ⦃T : NNReal⦄, 0 < T → Integrable (MeasureTheory.secondMomentCompensator H T) μ

/-- Helper: progressive measurability of `H` gives measurability of its
time-space representative `MeasureTheory.processToTimeSpaceFun H`. -/
private theorem measurable_processToTimeSpaceFun_of_progMeasurable
    {H : Process Ω}
    (hH_prog : ProgMeasurable ℱ H) :
    Measurable (MeasureTheory.processToTimeSpaceFun H) := by
  have huncurry : Measurable (Function.uncurry H) := hH_prog.measurable_uncurry
  have hswap : Measurable fun x : Ω × ℝ ↦ (x.2.toNNReal, x.1) := by
    exact measurable_snd.real_toNNReal.prodMk measurable_fst
  simpa [MeasureTheory.processToTimeSpaceFun, Function.uncurry] using huncurry.comp hswap

/-- Helper for Theorem 25.18: a deterministic cutoff belongs to ambient `L²(μ ⊗ dt)` once the
source process is progressively measurable and its squared sample paths are integrable on every
finite horizon almost surely. -/
private theorem constStop_memLp_of_intervalSquareIntegrable
    {H : Process Ω}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_int :
      ∀ ⦃T : NNReal⦄, ∀ᵐ ω ∂μ,
        IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)))
    (hH_finite :
      ∀ ⦃T : NNReal⦄, 0 < T → Integrable (MeasureTheory.secondMomentCompensator H T) μ)
    (T : NNReal) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        (processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal))))
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  let K : Process Ω := processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal))
  let ν : Measure ℝ := (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))
  have hK_prog : ProgMeasurable ℱ K :=
    MeasureTheory.processBeforeStoppingTime_progMeasurable
      hH_prog
      (isStoppingTime_const ℱ T)
  have hK_aesm :
      AEStronglyMeasurable (MeasureTheory.processToTimeSpaceFun K)
        (MeasureTheory.processMeasure μ) := by
    exact (measurable_processToTimeSpaceFun_of_progMeasurable hK_prog).aestronglyMeasurable
  let A : Set ℝ := Set.Icc (0 : ℝ) (T : ℝ)
  let g : Ω → ℝ → ℝ := fun ω s ↦ (H s.toNNReal ω) ^ 2
  let f : Ω × ℝ → ℝ := fun x ↦ (MeasureTheory.processToTimeSpaceFun K x) ^ 2
  have hbase_int :
      ∀ᵐ ω ∂μ, IntegrableOn (g ω) A volume := by
    have hH_int_T :
        ∀ᵐ ω ∂μ,
          IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2) (Set.Icc (0 : ℝ) (T : ℝ)) :=
      @hH_int T
    simpa [A, g] using hH_int_T
  have hRowEqAE :
      ∀ ω : Ω,
        (fun s : ℝ ↦ f (ω, s)) =ᵐ[ν]
          Set.indicator A (g ω) := by
    intro ω
    change
      ∀ᵐ s ∂((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ))),
        f (ω, s) = Set.indicator A (g ω) s
    rw [ae_restrict_iff' measurableSet_Ici]
    refine Filter.Eventually.of_forall ?_
    intro s hs0
    by_cases hsT : s ≤ (T : ℝ)
    · have hs_cutoff : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
        exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 hsT)
      have hs_mem : s ∈ A := ⟨hs0, hsT⟩
      have hs_not_gt : ¬ T < s.toNNReal := by
        exact not_lt_of_ge (Real.toNNReal_le_iff_le_coe.2 hsT)
      simpa [f, g, K, A, MeasureTheory.processToTimeSpaceFun,
        ProbabilityTheory.processBeforeStoppingTime_apply, hs_cutoff, hs_not_gt,
        Set.indicator_of_mem hs_mem]
    · have hs_not_cutoff : ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
        intro hs_cutoff
        exact hsT (Real.toNNReal_le_iff_le_coe.1 (by exact_mod_cast hs_cutoff))
      have hs_not_mem : s ∉ A := by
        intro hs_mem
        exact hsT hs_mem.2
      have hs_not_le : ¬ s.toNNReal ≤ T := by
        intro hs_le
        exact hs_not_cutoff (by exact_mod_cast hs_le)
      simpa [f, g, K, A, MeasureTheory.processToTimeSpaceFun,
        ProbabilityTheory.processBeforeStoppingTime_apply, hs_not_cutoff, hs_not_le,
        Set.indicator_of_notMem hs_not_mem]
  have hrow_int :
      ∀ᵐ ω ∂μ, Integrable (fun s : ℝ ↦ f (ω, s)) ν := by
    filter_upwards [hbase_int] with ω hω
    have hIndicator_int : Integrable (Set.indicator A (g ω)) ν := by
      rw [integrable_indicator_iff measurableSet_Icc]
      have hA_subset : A ⊆ Set.Ici (0 : ℝ) := by
        intro s hs
        exact hs.1
      simpa [IntegrableOn, ν, A, Measure.restrict_restrict,
        Set.inter_eq_left.mpr hA_subset] using hω
    exact hIndicator_int.congr (hRowEqAE ω).symm
  have houter_eq :
      (fun ω ↦ ∫ t, ‖f (ω, t)‖ ∂ν) =ᵐ[μ] MeasureTheory.secondMomentCompensator H T := by
    filter_upwards [hrow_int] with ω hω
    calc
      ∫ t, ‖f (ω, t)‖ ∂ν = ∫ t, f (ω, t) ∂ν := by
        refine integral_congr_ae ?_
        filter_upwards with t
        simp [f, sq_nonneg (MeasureTheory.processToTimeSpaceFun K (ω, t))]
      _ = ∫ t, Set.indicator A (g ω) t ∂ν := by
        exact integral_congr_ae (hRowEqAE ω)
      _ = ∫ t in A, g ω t ∂ν := by
        rw [integral_indicator measurableSet_Icc]
      _ = ∫ t in A, g ω t ∂volume := by
        have hA_subset : A ⊆ Set.Ici (0 : ℝ) := by
          intro s hs
          exact hs.1
        simp [ν, A, Measure.restrict_restrict, Set.inter_eq_left.mpr hA_subset]
      _ = MeasureTheory.secondMomentCompensator H T ω := by
        simp [A, g, MeasureTheory.secondMomentCompensator]
  have houter_int :
      Integrable (fun ω ↦ ∫ t, ‖f (ω, t)‖ ∂ν) μ := by
    by_cases hT0 : T = 0
    · have hZero :
        Integrable (MeasureTheory.secondMomentCompensator H T) μ := by
          rw [hT0, MeasureTheory.secondMomentCompensator_zero]
          exact integrable_zero _ _ _
      exact hZero.congr houter_eq.symm
    · have hFinite :
          Integrable (MeasureTheory.secondMomentCompensator H T) μ := by
        exact hH_finite (pos_iff_ne_zero.mpr hT0)
      exact hFinite.congr houter_eq.symm
  have hf_aesm : AEStronglyMeasurable f (μ.prod ν) := by
    simpa [f, MeasureTheory.processMeasure, ν] using hK_aesm.pow 2
  have hf_int : Integrable f (μ.prod ν) := by
    exact (integrable_prod_iff hf_aesm).2 ⟨by simpa [f, ν] using hrow_int, houter_int⟩
  refine (memLp_two_iff_integrable_sq hK_aesm).2 ?_
  simpa [f, K, MeasureTheory.processMeasure, ν] using hf_int

namespace HasFiniteExpectedEnergyOnEveryHorizon

/-- Internal bridge: the source-facing finite-energy hypothesis yields the stronger implementation
package used to realize deterministic cutoffs inside `brownianItoIntegralProcess`. -/
theorem toInternal
    {H : Process Ω} (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) :
    _root_.ProbabilityTheory.HasFiniteExpectedEnergy ℱ μ H :=
  { progMeasurable := hH.progMeasurable
    interval_square_integrable := hH.interval_square_integrable
    const_stop_closure := fun T ↦
      MeasureTheory.progMeasurable_memPredictableStepProcessClosure ℱ μ
        (MeasureTheory.processBeforeStoppingTime_progMeasurable
          hH.progMeasurable
          (isStoppingTime_const ℱ T))
        (constStop_memLp_of_intervalSquareIntegrable
          hH.progMeasurable
          hH.interval_square_integrable
          hH.finite_expectation
          T)
    finite_expectation := hH.finite_expectation }

end HasFiniteExpectedEnergyOnEveryHorizon

/-- Internal bridge: realize the Brownian-Itô process `t ↦ ∫_0^t H_s dW_s` from the
source-facing finite-energy package by upgrading to the stronger deterministic-cutoff API. -/
private noncomputable abbrev brownianItoIntegralProcessOnEveryHorizon
    (W : Process Ω)
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) : Process Ω :=
  brownianItoIntegralProcess W hH.toInternal

/-- Source-facing Brownian-Itô process
`M_t := ∫_0^t H_s dW_s` attached to an integrand `H` whose energy has finite expectation on every
positive finite horizon. -/
noncomputable abbrev brownianItoIntegralProcessOfFiniteExpectedEnergy
    (W : Process Ω)
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) : Process Ω :=
  brownianItoIntegralProcessOnEveryHorizon W hH

/-- Implementation package for the Brownian-Itô martingale result below: besides the
source-facing finite-energy hypothesis, it carries the almost-sure interval
square-integrability used to build the deterministic cutoff closure points
feeding the Brownian-Itô continuous modification. -/
private abbrev HasFiniteExpectedEnergyPathwise
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) (H : Process Ω) : Prop :=
  HasFiniteExpectedEnergy ℱ μ H

/-- Implementation bridge: the source-facing finite-energy hypothesis upgrades to
the pathwise interval-integrability package used to realize deterministic cutoffs in the Brownian-
Itô closure model. -/
private theorem HasFiniteExpectedEnergy.exists_pathwise
    {H : Process Ω} (hH : HasFiniteExpectedEnergy ℱ μ H) :
    Nonempty (HasFiniteExpectedEnergyPathwise ℱ μ H) :=
  ⟨hH⟩

/-- The source-facing finite-energy hypothesis above implies the packaged local
square-integrability condition used elsewhere in Chapter 25. -/
theorem HasFiniteExpectedEnergyOnEveryHorizon.isLocallySquareIntegrableProcess
    {H : Process Ω} (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) :
    MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H := by
  -- Proof comment: this is exactly the pair of fields stored in the source-facing
  -- finite-energy package.
  refine ⟨hH.progMeasurable, ?_⟩
  intro T
  simpa using
    (@HasFiniteExpectedEnergyOnEveryHorizon.interval_square_integrable _ mΩ ℱ μ H hH T)

/-- The source-facing finite-energy hypothesis above implies the packaged local
square-integrability condition used elsewhere in Chapter 25. -/
theorem HasFiniteExpectedEnergy.isLocallySquareIntegrableProcess
    {H : Process Ω} (hH : HasFiniteExpectedEnergy ℱ μ H) :
    MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H :=
  ⟨hH.progMeasurable,
    fun T ↦ by
      simpa using
        (@HasFiniteExpectedEnergy.interval_square_integrable _ mΩ ℱ μ H hH T)⟩

namespace HasFiniteExpectedEnergyPathwise

/-- Helper: the deterministic cutoff of a finite-energy integrand is an
ambient `L²(μ ⊗ dt)` process. -/
private theorem constStop_memLp
    {H : Process Ω} (hH : HasFiniteExpectedEnergy ℱ μ H) (T : NNReal) :
    MemLp
      (MeasureTheory.processToTimeSpaceFun
        (processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal))))
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) := by
  -- Proof comment: this is the source-facing deterministic-cutoff `L²` lemma specialized to
  -- the stronger implementation package.
  exact
    constStop_memLp_of_intervalSquareIntegrable
      hH.progMeasurable hH.interval_square_integrable
      hH.finite_expectation T

/-- Helper: every deterministic cutoff of a finite-energy integrand defines the
canonical closure point needed by Theorem 25.11. -/
private theorem constStop_memPredictableStepProcessClosure
    {H : Process Ω} (hH : HasFiniteExpectedEnergy ℱ μ H) (T : NNReal) :
    MeasureTheory.MemPredictableStepProcessClosure ℱ μ
      (processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal))) :=
  MeasureTheory.progMeasurable_memPredictableStepProcessClosure ℱ μ
    (MeasureTheory.processBeforeStoppingTime_progMeasurable
      hH.progMeasurable
      (isStoppingTime_const ℱ T))
    (constStop_memLp hH T)

end HasFiniteExpectedEnergyPathwise

/-- Helper: continuity on every integer interval `[0, N + 1]` patches to
continuity on all of `NNReal`. -/
private lemma continuous_of_continuousOnIntegerIntervals
    {β : Type v} [TopologicalSpace β] {f : NNReal → β}
    (hcont : ∀ N : ℕ, ContinuousOn f (Set.Icc (0 : NNReal) (N + 1 : NNReal))) :
    Continuous f := by
  -- Proof comment: every `t : NNReal` lies in some interval `[0, N + 1]` that is a neighborhood
  -- of `t`, so the local continuity on that interval upgrades to global continuity.
  refine continuous_iff_continuousAt.2 ?_
  intro t
  let N : ℕ := Nat.ceil t
  have ht_le : t ≤ (N : NNReal) := by
    exact_mod_cast Nat.le_ceil t
  have ht_lt : t < (N + 1 : NNReal) := by
    exact lt_of_le_of_lt ht_le (by exact_mod_cast Nat.lt_succ_self N)
  have hnhdsIic : Set.Iic (N + 1 : NNReal) ∈ 𝓝 t :=
    Iic_mem_nhds ht_lt
  have hnhdsIcc : Set.Icc (0 : NNReal) (N + 1 : NNReal) ∈ 𝓝 t :=
    Filter.mem_of_superset hnhdsIic fun x hx ↦ ⟨bot_le, hx⟩
  exact (hcont N).continuousAt hnhdsIcc

/-- Helper: one all-times almost-sure identity transports deterministic-time
stopped slices under a fixed clock. -/
private lemma stoppedProcess_congr_process_ae_allTimes
    {M N : Process Ω} {τ : Ω → ENNReal}
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω) (t : NNReal) :
    stoppedProcess M τ t =ᵐ[μ] stoppedProcess N τ t := by
  -- Proof comment: both stopped slices evaluate the source process at the same clipped time
  -- `t ∧ τ(ω)`, so the all-times equality transfers directly.
  filter_upwards [hMN] with ω hω
  simpa [stoppedProcess] using hω ((min (t : ENNReal) (τ ω)).untopA)

/-- Helper: an all-times almost-sure identity transports the local-martingale
property to a continuous adapted modification. -/
private theorem isLocalMartingale_congr_ae_allTimes_local
    {M N : Process Ω}
    (hM : IsLocalMartingale ℱ μ M) (hN_adapted : Adapted ℱ N)
    (hN_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ N t ω)
    (hMN : ∀ᵐ ω ∂μ, ∀ t : NNReal, M t ω = N t ω) :
    IsLocalMartingale ℱ μ N := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨_, τSeq, hτSeq⟩
  refine (isLocalMartingale_iff ℱ μ N).2 ⟨hN_adapted, τSeq, ?_⟩
  rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hlim, hStopped⟩
  refine (isLocalizingSequence_iff ℱ μ N τSeq).2 ⟨hStopping, hlim, ?_⟩
  intro n
  obtain ⟨hMart, hUI⟩ := hStopped n
  have hStoppedEq :
      ∀ t : NNReal,
        stoppedProcess M (τSeq n) t =ᵐ[μ] stoppedProcess N (τSeq n) t := by
    intro t
    -- Proof comment: the common stopped clock preserves the all-times almost-sure identity.
    exact stoppedProcess_congr_process_ae_allTimes hMN t
  have hStoppedStrong :
      StronglyAdapted ℱ (stoppedProcess N (τSeq n)) := by
    -- Proof comment: continuity of the target process upgrades adaptedness to strong adaptedness
    -- after stopping.
    exact hN_adapted.stronglyAdapted.stoppedProcess hN_cont (hStopping n)
  refine ⟨martingale_congr_ae hMart hStoppedStrong hStoppedEq, ?_⟩
  -- Proof comment: uniform integrability is stable under timewise almost-sure equality.
  exact (uniformIntegrable_congr_ae hStoppedEq).1 hUI

/-- Helper: deterministic stopping preserves the local-martingale property for
continuous paths. -/
private theorem isLocalMartingale_stoppedProcess_constTime
    {M : Process Ω}
    (hM : IsLocalMartingale ℱ μ M)
    (hM_cont : ∀ ω : Ω, Continuous fun t : NNReal ↦ M t ω)
    (T : NNReal) :
    IsLocalMartingale ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) := by
  rcases (isLocalMartingale_iff ℱ μ M).1 hM with ⟨hM_adapted, τSeq, hτSeq⟩
  refine
    (isLocalMartingale_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal)))).2
      ⟨?_, τSeq, ?_⟩
  · -- Proof comment: deterministic stopping preserves adaptedness once the source process has
    -- continuous sample paths.
    exact
      (hM_adapted.stronglyAdapted.stoppedProcess hM_cont (isStoppingTime_const ℱ T)).adapted
  · rcases (isLocalizingSequence_iff ℱ μ M τSeq).1 hτSeq with ⟨hStopping, hLim, hStopped⟩
    refine
      (isLocalizingSequence_iff ℱ μ (stoppedProcess M (fun _ ↦ (T : ENNReal))) τSeq).2
        ⟨hStopping, hLim, ?_⟩
    intro n
    obtain ⟨hMart, hUI⟩ := hStopped n
    have hDoubleStop :
        stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) := by
      have hLeft :
          stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (fun _ ↦ (T : ENNReal))) (τSeq n) =
              stoppedProcess M
                (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))))
      have hRight :
          stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
            stoppedProcess M
              (fun ω ↦ min ((τSeq n) ω) (((fun _ ↦ (T : ENNReal)) ω))) := by
        simpa [min_comm] using
          (stoppedProcess_stoppedProcess' :
            stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)) =
              stoppedProcess M
                (fun ω ↦ min (((fun _ ↦ (T : ENNReal)) ω)) ((τSeq n) ω)))
      exact hLeft.trans hRight.symm
    have hStoppedConst :
        Martingale
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            ℱ
            μ ∧
          UniformIntegrable
            (stoppedProcess (stoppedProcess M (τSeq n)) (fun _ ↦ (T : ENNReal)))
            1
            μ :=
      martingaleUniformIntegrable_stoppedProcessConstTime hMart T
    -- Proof comment: after swapping the two stops, the localized stopped process is just a
    -- deterministic stop of the martingale supplied by the localizing sequence.
    exact hDoubleStop ▸ hStoppedConst

/-- Helper: deterministic constant stops already form a localizing sequence
when each stopped process is a uniformly integrable martingale. -/
private theorem isLocalMartingale_of_constStoppedMartingale
    {X : Process Ω}
    (hAdapted : Adapted ℱ X)
    (hStopped :
      ∀ n : ℕ, Martingale (stoppedProcess X (fun _ ↦ (n : ENNReal))) ℱ μ ∧
        UniformIntegrable (stoppedProcess X (fun _ ↦ (n : ENNReal))) 1 μ) :
    IsLocalMartingale ℱ μ X := by
  -- Proof comment: use the deterministic localization sequence `τₙ ≡ n`; the only input is
  -- that each deterministically stopped process is already a uniformly integrable martingale.
  refine (ProbabilityTheory.isLocalMartingale_iff ℱ μ X).2 ?_
  refine ⟨hAdapted, ?_⟩
  let τs : ℕ → Ω → ENNReal := fun n _ ↦ (n : ENNReal)
  refine ⟨τs, (ProbabilityTheory.isLocalizingSequence_iff ℱ μ X τs).2 ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n
    simpa [τs] using (MeasureTheory.isStoppingTime_const ℱ n)
  · refine Filter.Eventually.of_forall ?_
    intro ω
    refine ⟨?_, ?_⟩
    · intro i j hij
      simpa [τs] using (show (i : ENNReal) ≤ (j : ENNReal) from by exact_mod_cast hij)
    · simpa [τs] using
        (ENNReal.tendsto_nat_nhds_top : Tendsto (fun n : ℕ ↦ (n : ENNReal)) atTop (𝓝 ∞))
  · intro n
    simpa [τs] using hStopped n

/-- Helper: on the interval `[0, T]`, deterministic cutoff leaves the
integrand unchanged. -/
private lemma processBeforeStoppingTime_const_eqOn_Icc
    {H : Process Ω} (T : NNReal) (ω : Ω) :
    Set.EqOn
      (fun s : ℝ ↦
        processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal)) s.toNNReal ω)
      (fun s : ℝ ↦ H s.toNNReal ω)
      (Set.Icc (0 : ℝ) (T : ℝ)) := by
  -- Proof comment: on `[0, T]`, the deterministic cutoff condition is active, so the cutoff
  -- process evaluates to the original integrand pointwise.
  intro s hs
  have hs_le : s.toNNReal ≤ T := by
    exact (Real.toNNReal_le_iff_le_coe).2 hs.2
  have hs_cutoff : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
    exact_mod_cast hs_le
  simp [processBeforeStoppingTime_apply, hs_cutoff]

/-- Helper: once an integrand is already cut off at `T`, stopping it again at a
later deterministic horizon does not change it. -/
private lemma processBeforeStoppingTime_constCutoff_eq_self_of_le
    {H : Process Ω} {T U : NNReal} (hTU : T ≤ U) :
    processBeforeStoppingTime
        (processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal)))
        (fun _ : Ω ↦ (U : ENNReal)) =
      processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal)) := by
  -- Proof comment: before `T` both sides agree with `H`, while after `T` the inner cutoff has
  -- already forced the process to vanish.
  funext t ω
  have hTU' : (T : ENNReal) ≤ (U : ENNReal) := by
    exact_mod_cast hTU
  by_cases hU : (t : ENNReal) ≤ (U : ENNReal)
  · by_cases hT : (t : ENNReal) ≤ (T : ENNReal)
    · simp [processBeforeStoppingTime_apply, hU, hT]
    · simp [processBeforeStoppingTime_apply, hU, hT]
  · have hT : ¬ (t : ENNReal) ≤ (T : ENNReal) := by
      intro ht
      exact hU (le_trans ht hTU')
    rw [processBeforeStoppingTime_apply, if_neg hU]
    rw [processBeforeStoppingTime_apply, if_neg hT]
/-- Helper: each deterministic-time slice of the compensator
`t ↦ ∫_0^t H_s^2 ds` is measurable in the matching filtration level. -/
private lemma secondMomentCompensator_measurable
    {H : Process Ω}
    (hH_prog : MeasureTheory.ProgMeasurable ℱ H) (T : NNReal) :
    Measurable[ℱ T] (MeasureTheory.secondMomentCompensator H T) := by
  let J : Set ℝ := Set.Icc (0 : ℝ) (T : ℝ)
  let νJ : Measure J := Measure.comap Subtype.val volume
  let g : Ω → J → ℝ := fun ω s ↦ (H s.1.toNNReal ω) ^ 2
  let hJ : MeasurableEmbedding (Subtype.val : J → ℝ) :=
    MeasurableEmbedding.subtype_coe measurableSet_Icc
  letI : IsFiniteMeasure νJ := by
    refine ⟨?_⟩
    calc
      νJ Set.univ = volume ((Subtype.val : J → ℝ) '' Set.univ) := by
        simpa [νJ] using hJ.comap_apply volume (Set.univ : Set J)
      _ = volume J := by simp
      _ < ∞ := by
        simpa [J] using (measure_Icc_lt_top : volume (Set.Icc (0 : ℝ) (T : ℝ)) < ∞)
  have hstrip :
      StronglyMeasurable[Subtype.instMeasurableSpace.prod (ℱ T)]
        (fun p : Set.Iic T × Ω ↦ H p.1 p.2) :=
    hH_prog T
  -- Local instance justification: the product-integration measurability lemmas are stated for the
  -- ambient source measurable space, so we temporarily set that source to `ℱ T`.
  letI : MeasurableSpace Ω := ℱ T
  have htime : Measurable (fun p : Ω × J ↦ (p.2.1 : ℝ)) :=
    measurable_snd.subtype_val
  have htimeNN : Measurable (fun p : Ω × J ↦ p.2.1.toNNReal) :=
    htime.real_toNNReal
  have htimeSub :
      Measurable
        (fun p : Ω × J ↦
          (⟨p.2.1.toNNReal, by
              refine Real.toNNReal_le_iff_le_coe.2 ?_
              exact p.2.2.2⟩ : Set.Iic T)) :=
    htimeNN.subtype_mk
  have hmap :
      Measurable
        (fun p : Ω × J ↦
          ((⟨p.2.1.toNNReal, by
              refine Real.toNNReal_le_iff_le_coe.2 ?_
              exact p.2.2.2⟩ : Set.Iic T), p.1)) :=
    htimeSub.prodMk measurable_fst
  have hgBase : Measurable (fun p : Ω × J ↦ H p.2.1.toNNReal p.1) := by
    -- Proof comment: after swapping the coordinates, the integrand is exactly the progressive
    -- strip map evaluated at the deterministic horizon `T`.
    simpa using hstrip.measurable.comp hmap
  have hg : Measurable (Function.uncurry g) := by
    -- Proof comment: squaring preserves measurability of the pulled-back strip integrand.
    simpa [Function.uncurry, g] using hgBase.pow_const 2
  have hgIntegral :
      StronglyMeasurable[ℱ T] (fun ω : Ω ↦ ∫ s, g ω s ∂νJ) := by
    -- Proof comment: integrating the strip-restricted integrand over the deterministic finite
    -- interval preserves measurability in the sample point.
    simpa [Function.uncurry, g] using
      (hg.stronglyMeasurable.integral_prod_right :
        StronglyMeasurable fun ω : Ω ↦ ∫ s, g ω s ∂νJ)
  have hEq :
      (fun ω : Ω ↦ ∫ s, g ω s ∂νJ) = MeasureTheory.secondMomentCompensator H T := by
    funext ω
    -- Proof comment: the subtype integral over `J = [0, T]` is exactly the textbook compensator.
    simpa [MeasureTheory.secondMomentCompensator, g, νJ, J] using
      (integral_subtype_comap measurableSet_Icc fun s : ℝ ↦ (H s.toNNReal ω) ^ 2)
  simpa [hEq] using hgIntegral.measurable
/-- Helper: the compensator process is adapted. -/
lemma MeasureTheory.secondMomentCompensator_adapted
    {H : Process Ω}
    (hH : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H) :
    Adapted ℱ (MeasureTheory.secondMomentCompensator H) := by
  -- Proof comment: adaptedness is pointwise measurability, and each time slice is measurable by
  -- the deterministic-horizon compensator lemma.
  intro T
  exact secondMomentCompensator_measurable
    hH.1 T
/-- Helper: on a finite horizon with square-integrable density, the compensator
path is continuous along that compact interval. -/
private lemma secondMomentCompensator_continuousOn_of_integrableOn
    {H : Process Ω} {ω : Ω} {T : NNReal}
    (hT_int :
      IntegrableOn (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ))) :
    ContinuousOn
      (fun t : NNReal ↦ MeasureTheory.secondMomentCompensator H t ω)
      (Set.Icc (0 : NNReal) T) := by
  -- Proof comment: along a fixed sample path, the compensator is the primitive of the
  -- square-integrable density `s ↦ H s ω ^ 2` on `[0, T]`.
  have hReal :
      ContinuousOn
        (fun x : ℝ ↦ ∫ s in Set.Icc (0 : ℝ) x, (H s.toNNReal ω) ^ 2)
        (Set.Icc (0 : ℝ) (T : ℝ)) :=
    intervalIntegral.continuousOn_primitive_Icc hT_int
  have hVal :
      ContinuousOn (fun t : NNReal ↦ (t : ℝ)) (Set.Icc (0 : NNReal) T) :=
    continuous_subtype_val.continuousOn
  have hMaps :
      Set.MapsTo (fun t : NNReal ↦ (t : ℝ))
        (Set.Icc (0 : NNReal) T)
        (Set.Icc (0 : ℝ) (T : ℝ)) := by
    intro t ht
    exact ht
  simpa [MeasureTheory.secondMomentCompensator, Function.comp] using
    hReal.comp' hVal hMaps
/-- Helper: the compensator has almost surely continuous sample paths. -/
lemma MeasureTheory.secondMomentCompensator_hasAlmostSurelyContinuousPaths
    {H : Process Ω}
    (hH : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H) :
    HasAlmostSurelyContinuousPaths μ (MeasureTheory.secondMomentCompensator H) := by
  -- Proof comment: on a full-measure event, every finite-horizon primitive is continuous; the
  -- integer-interval patching lemma then yields continuity on all of `NNReal`.
  rw [HasAlmostSurelyContinuousPaths]
  have hAllHorizons :
      ∀ᵐ ω ∂μ,
        ∀ N : ℕ,
          IntegrableOn
            (fun s : ℝ ↦ (H s.toNNReal ω) ^ 2)
            (Set.Icc (0 : ℝ) ((N + 1 : NNReal) : ℝ)) := by
    rw [ae_all_iff]
    intro N
    simpa using
      hH.2 (N + 1 : NNReal)
  filter_upwards [hAllHorizons] with ω hω
  exact
    continuous_of_continuousOnIntegerIntervals fun N ↦
      secondMomentCompensator_continuousOn_of_integrableOn
        (hω N)

/-- Helper for Theorem 25.18: cutting off an already deterministically cut off integrand at a
second deterministic horizon yields the cutoff at the smaller horizon on the realized `L²`
closure point. -/
theorem deterministicCutoffDoubleCutoff_toClosure_eq
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H)
    (t T : NNReal) :
    MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure T)) =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (hH.toInternal.const_stop_closure (min t T)) := by
  let hNested :
      MeasureTheory.MemPredictableStepProcessClosure ℱ μ
        (processBeforeStoppingTime
          (processBeforeStoppingTime H (fun _ : Ω ↦ (T : ENNReal)))
          (fun _ : Ω ↦ (t : ENNReal))) :=
    MeasureTheory.MemPredictableStepProcessClosure.processBeforeStoppingTime
      (hH.toInternal.const_stop_closure T) (isStoppingTime_const ℱ t)
  calc
    MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure T)) =
      MeasureTheory.MemPredictableStepProcessClosure.toClosure hNested := by
        -- Proof comment: the first deterministic cutoff theorem rewrites the outer truncation to
        -- the closure point of the doubly cut off source integrand.
        simpa [hNested] using
          cutoffBefore_toClosure_eq_processBeforeStoppingTimeConst
            (hH.toInternal.const_stop_closure T) t
    _ = MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure (min t T)) := by
        -- Proof comment: the two closure points represent the same deterministic double cutoff,
        -- so their `L²(μ ⊗ dt)` representatives are pointwise equal.
        apply Subtype.ext
        rw [MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure]
        rw [MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure]
        apply Lp.ext
        refine Filter.Eventually.of_forall ?_
        intro x
        rcases x with ⟨ω, s⟩
        by_cases hs_t : s.toNNReal ≤ t
        · by_cases hs_T : s.toNNReal ≤ T
          · have hs_t_enn : (s.toNNReal : ENNReal) ≤ (t : ENNReal) := by
              exact_mod_cast hs_t
            have hs_T_enn : (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
              exact_mod_cast hs_T
            have hs_min_enn :
                (s.toNNReal : ENNReal) ≤ ((min t T : NNReal) : ENNReal) := by
              exact_mod_cast (le_min hs_t hs_T)
            simp [MeasureTheory.processToTimeSpaceFun, processBeforeStoppingTime_apply,
              hs_t_enn, hs_T_enn, hs_min_enn]
          · have hs_t_enn : (s.toNNReal : ENNReal) ≤ (t : ENNReal) := by
              exact_mod_cast hs_t
            have hs_T_enn : ¬ (s.toNNReal : ENNReal) ≤ (T : ENNReal) := by
              exact_mod_cast hs_T
            have hs_min_enn :
                ¬ (s.toNNReal : ENNReal) ≤ ((min t T : NNReal) : ENNReal) := by
              intro hs_min_enn
              exact hs_T (le_trans (by exact_mod_cast hs_min_enn) (min_le_right t T))
            simp [MeasureTheory.processToTimeSpaceFun, processBeforeStoppingTime_apply,
              hs_t_enn, hs_T_enn, hs_min_enn]
        · have hs_t_enn : ¬ (s.toNNReal : ENNReal) ≤ (t : ENNReal) := by
            exact_mod_cast hs_t
          have hs_min_enn :
              ¬ (s.toNNReal : ENNReal) ≤ ((min t T : NNReal) : ENNReal) := by
            intro hs_min_enn
            exact hs_t (le_trans (by exact_mod_cast hs_min_enn) (min_le_left t T))
          simp [MeasureTheory.processToTimeSpaceFun, processBeforeStoppingTime_apply,
            hs_t_enn, hs_min_enn]

/-- Helper for Theorem 25.18: stopping the raw Brownian-Itô process at a deterministic horizon
matches the canonical deterministic truncation process built from that same horizon. -/
theorem brownianItoIntegralProcessStoppedConst_eq_truncatedProcess
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H)
    (T : NNReal) :
    stoppedProcess (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH)
        (fun _ : Ω ↦ (T : ENNReal)) =
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure T)) := by
  funext t ω
  let K : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
    MeasureTheory.MemPredictableStepProcessClosure.toClosure
      (hH.toInternal.const_stop_closure T)
  have hCutoff :
      MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t K =
        MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure (min t T)) :=
    deterministicCutoffDoubleCutoff_toClosure_eq hH t T
  -- Proof comment: both sides are the Brownian-Itô map applied to the same closure point at the
  -- clipped horizon `min t T`.
  change brownianItoIntegralProcessOfFiniteExpectedEnergy W hH (min t T) ω =
    hIto.toContinuousLinearMap
      (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t K) ω
  rw [brownianItoIntegralProcess_apply]
  rw [hCutoff]

/-- Helper for Theorem 25.18: evaluating the raw Brownian-Itô process at time `t` is exactly the
matching `t`-slice of the deterministic-horizon truncation process with horizon `t`. -/
private lemma brownianItoIntegralProcess_eq_truncatedSlice
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H)
    (t : NNReal) :
    brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t =
      brownianItoIntegralTruncatedProcess W
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure t)) t := by
  -- Proof comment: stopping the raw process at its own horizon `t` leaves the time-`t` slice
  -- unchanged, so the deterministic-stop normalization collapses directly to the truncation slice.
  simpa [stoppedProcessConstTime_eq_min] using
    congrArg (fun X : Process Ω ↦ X t)
      (brownianItoIntegralProcessStoppedConst_eq_truncatedProcess hH t)

/-- Helper for Theorem 25.18: every deterministic-time slice of the raw Brownian-Itô process is
`L²(μ)`. This is the exact slice-level part of the textbook conclusion that survives for the raw
`Lp` representative without invoking any modification transport. -/
private theorem brownianItoIntegralProcess_squareIntegrable
    [hIto : BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) :
    IsSquareIntegrableProcess
      (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH) μ := by
  intro t
  -- Proof comment: identify the raw slice with the matching deterministic-horizon truncation
  -- slice and reuse the public `L²` theorem from Theorem 25.11.
  have hSlice :
      brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t =
        brownianItoIntegralTruncatedProcess W
          (MeasureTheory.MemPredictableStepProcessClosure.toClosure
            (hH.toInternal.const_stop_closure t)) t := by
    simpa [stoppedProcessConstTime_eq_min] using
      congrArg (fun X : Process Ω ↦ X t)
        (brownianItoIntegralProcessStoppedConst_eq_truncatedProcess hH t)
  rw [hSlice]
  exact BrownianItoIntegral.truncatedProcess_memLp
    (MeasureTheory.MemPredictableStepProcessClosure.toClosure
      (hH.toInternal.const_stop_closure t))
    t

/-- Helper: subtracting the continuous compensator from `t ↦ M t ^ 2`
preserves almost sure continuity of sample paths. -/
private lemma brownianItoCompensatedSquareProcess_hasAlmostSurelyContinuousPaths
    {H M : Process Ω}
    (hM_cont : HasAlmostSurelyContinuousPaths μ M)
    (hH_local : MeasureTheory.IsLocallySquareIntegrableProcess ℱ μ H) :
    HasAlmostSurelyContinuousPaths μ
      (MeasureTheory.brownianItoCompensatedSquareProcess M H) := by
  -- Proof comment: on the full-measure event where both `M` and the compensator are continuous,
  -- the compensated square path is the difference of two continuous functions.
  rw [HasAlmostSurelyContinuousPaths] at hM_cont ⊢
  filter_upwards
    [hM_cont,
      MeasureTheory.secondMomentCompensator_hasAlmostSurelyContinuousPaths hH_local] with
    ω hωM hωA
  simpa [HasAlmostSurelyContinuousPaths, processPath,
    MeasureTheory.brownianItoCompensatedSquareProcess] using (hωM.pow 2).sub hωA

variable {W H M : Process Ω}

/-- Companion API for Theorem 25.18: `M` is a continuous modification of the explicit Brownian-
Itô process `t ↦ ∫₀ᵗ Hₛ dWₛ` built from the source-facing finite-energy hypothesis. -/
def IsBrownianItoContinuousModificationOfFiniteExpectedEnergy
    (W : Process Ω)
    [BrownianItoIntegral μ ℱ W]
    {H : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H)
    (M : Process Ω) : Prop :=
  HasAlmostSurelyContinuousPaths μ M ∧
    AreModifications μ M (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH)

/-- Unfolding the companion owner shows that it records almost sure continuity and modification
to the explicit Brownian-Itô process on every finite horizon. -/
theorem isBrownianItoContinuousModificationOfFiniteExpectedEnergy_iff
    [BrownianItoIntegral μ ℱ W]
    {H M : Process Ω}
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) :
    IsBrownianItoContinuousModificationOfFiniteExpectedEnergy W hH M ↔
      HasAlmostSurelyContinuousPaths μ M ∧
        AreModifications μ M (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH) :=
  Iff.rfl

/-- Companion API for Theorem 25.18: a process is a zero-started continuous martingale if it is
a martingale, has almost surely continuous sample paths, and vanishes at time `0`. -/
@[mk_iff isZeroStartedContinuousMartingale_iff]
class IsZeroStartedContinuousMartingale
    (ℱ : Filtration NNReal mΩ) (μ : Measure Ω) (M : Process Ω) : Prop where
  martingale : Martingale M ℱ μ
  continuous_paths : HasAlmostSurelyContinuousPaths μ M
  zero : M 0 = 0

/-- Theorem 25.18 (1): if `H` is progressively measurable and has finite expected energy on every
positive finite horizon, then the Brownian-Itô process
`M_t := ∫_0^t H_s dW_s` is a square-integrable continuous martingale. -/
theorem brownianItoIntegral_isSquareIntegrableContinuousMartingale
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H) :
    ∃ M : Process Ω,
      IsBrownianItoContinuousModificationOfFiniteExpectedEnergy W hH M ∧
        Martingale M ℱ μ ∧
        IsSquareIntegrableProcess M μ := by
  let X : ℕ → Process Ω := fun n ↦
    BrownianItoIntegral.continuousModification
      hBrownian hAdapted hIndep
      (MeasureTheory.MemPredictableStepProcessClosure.toClosure
        (hH.toInternal.const_stop_closure (n + 1 : NNReal)))
  let Xtilde : NNReal → MeasureTheory.Lp ℝ (ENNReal.ofReal (2 : ℝ)) μ := fun t ↦
    let hMem :
        MemLp (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t)
          (ENNReal.ofReal (2 : ℝ)) μ := by
      simpa using (brownianItoIntegralProcess_squareIntegrable (W := W) hH t)
    hMem.toLp (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t)
  have hX : ∀ n : ℕ, Martingale (X n) ℱ μ := by
    intro n
    -- Proof comment: each deterministic cutoff belongs to the fixed-horizon Theorem 25.11
    -- setting, so its named continuous modification is already a martingale.
    exact
      BrownianItoIntegral.continuousModification_martingale
        hBrownian hAdapted hIndep
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure (n + 1 : NNReal)))
  have hcont : ∀ n : ℕ, HasAlmostSurelyContinuousPaths μ (X n) := by
    intro n
    -- Proof comment: the same named owner also records almost surely continuous sample paths.
    exact
      (BrownianItoIntegral.continuousModification_spec
        hBrownian hAdapted hIndep
        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure (n + 1 : NNReal)))).1
  have hp : 1 < (2 : ℝ) := by
    norm_num
  have hlimit :
      ∀ t : NNReal,
        letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
        ∃ h_memLpSeq : ∀ n, MemLp (X n t) (ENNReal.ofReal (2 : ℝ)) μ,
          Tendsto
            (fun n ↦ (h_memLpSeq n).toLp (X n t))
            atTop
            (nhds (Xtilde t)) := by
    intro t
    letI : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := fact_iff.2 (by norm_num)
    let hTargetMem : MemLp
        (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t)
        (ENNReal.ofReal (2 : ℝ)) μ :=
      by
        simpa using (brownianItoIntegralProcess_squareIntegrable (W := W) hH t)
    let h_memLpSeq :
        ∀ n, MemLp (X n t) (ENNReal.ofReal (2 : ℝ)) μ := fun n ↦ by
          let Hn : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
            MeasureTheory.MemPredictableStepProcessClosure.toClosure
              (hH.toInternal.const_stop_closure (n + 1 : NNReal))
          have hTruncMem :
              MemLp (brownianItoIntegralTruncatedProcess W Hn t)
                (ENNReal.ofReal (2 : ℝ)) μ := by
            simpa [Hn] using BrownianItoIntegral.truncatedProcess_memLp Hn t
          -- Proof comment: each fixed-time slice of the continuous owner is almost everywhere
          -- equal to the matching truncation slice, so it inherits the same `L²` class.
          exact
            (MeasureTheory.memLp_congr_ae
              ((BrownianItoIntegral.continuousModification_spec
                hBrownian hAdapted hIndep Hn).2 t)).2 hTruncMem
    refine ⟨h_memLpSeq, ?_⟩
    let N : ℕ := Nat.ceil t
    have hN : t ≤ (N : NNReal) := by
      exact_mod_cast Nat.le_ceil t
    have hEventually :
        (fun n ↦ (h_memLpSeq n).toLp (X n t)) =ᶠ[atTop] fun _ ↦ Xtilde t := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have htn : t ≤ (n + 1 : NNReal) := by
        calc
          t ≤ (N : NNReal) := hN
          _ ≤ (n : NNReal) := by exact_mod_cast hn
          _ ≤ (n + 1 : NNReal) := by exact_mod_cast Nat.le_succ n
      let Hn : MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ :=
        MeasureTheory.MemPredictableStepProcessClosure.toClosure
          (hH.toInternal.const_stop_closure (n + 1 : NNReal))
      have hSliceEq :
          brownianItoIntegralTruncatedProcess W Hn t =
            brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t := by
        have hCutoff :
            MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hn =
              MeasureTheory.MemPredictableStepProcessClosure.toClosure
                (hH.toInternal.const_stop_closure t) := by
          apply Subtype.ext
          rw [MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure]
          rw [MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure]
          apply Lp.ext
          have hCutoffAe :
              (((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hn :
                    MeasureTheory.PredictableSimpleProcessL2Closure ℱ μ) :
                  Lp ℝ 2 (MeasureTheory.processMeasure μ)) : Ω × ℝ → ℝ) =ᵐ[
                    MeasureTheory.processMeasure μ]
                Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)} fun x ↦
                  MeasureTheory.processToTimeSpaceFun
                    (processBeforeStoppingTime H
                      (fun _ : Ω ↦ (((n + 1 : NNReal) : ENNReal)))) x := by
            simpa [Hn, MeasureTheory.MemPredictableStepProcessClosure.coe_toClosure] using
              (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn t Hn)
          refine hCutoffAe.trans ?_
          refine Filter.Eventually.of_forall ?_
          intro x
          rcases x with ⟨ω, s⟩
          by_cases hs_t : s ≤ (t : ℝ)
          · have hs_t_enn : (s.toNNReal : ENNReal) ≤ (t : ENNReal) := by
              exact_mod_cast (Real.toNNReal_le_iff_le_coe.2 hs_t)
            have hs_n :
                (s.toNNReal : ENNReal) ≤ (((n + 1 : NNReal) : ENNReal)) := by
              exact le_trans hs_t_enn (by exact_mod_cast htn)
            simp [MeasureTheory.processToTimeSpaceFun,
              ProbabilityTheory.processBeforeStoppingTime_apply, hs_t, hs_t_enn, hs_n]
          · have hs_t_enn : ¬ (s.toNNReal : ENNReal) ≤ (t : ENNReal) := by
              intro hs_t_enn
              exact hs_t (Real.toNNReal_le_iff_le_coe.1 (by exact_mod_cast hs_t_enn))
            simp [MeasureTheory.processToTimeSpaceFun,
              ProbabilityTheory.processBeforeStoppingTime_apply, hs_t, hs_t_enn]
        -- Proof comment: the truncation slice uses the same closure point as the raw process once
        -- the deterministic horizon `n + 1` already dominates `t`.
        calc
          brownianItoIntegralTruncatedProcess W Hn t
              = hIto.toContinuousLinearMap
                  (MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t Hn) := by
                    rfl
          _ = hIto.toContinuousLinearMap
                (MeasureTheory.MemPredictableStepProcessClosure.toClosure
                  (hH.toInternal.const_stop_closure t)) := by
                    rw [hCutoff]
          _ = brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t := by
                    rw [brownianItoIntegralProcess_apply]
      have hSliceAe :
          X n t =ᵐ[μ] brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t := by
        exact
          ((BrownianItoIntegral.continuousModification_spec
            hBrownian hAdapted hIndep Hn).2 t).trans
            (Filter.EventuallyEq.of_eq hSliceEq)
      have hToLpEq :
          (h_memLpSeq n).toLp (X n t) =
            hTargetMem.toLp (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t) :=
        (MeasureTheory.MemLp.toLp_eq_toLp_iff (h_memLpSeq n) hTargetMem).2 hSliceAe
      simpa [Xtilde, hTargetMem] using hToLpEq
    exact
      Tendsto.congr' hEventually.symm
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ ↦ Xtilde t) atTop (nhds (Xtilde t)))
  rcases exists_continuous_martingale_modification_of_timewise_lp_limit
      (X := X) (Xtilde := Xtilde) (p := 2) hX hcont hp hlimit with
    ⟨M, hM_mart, hM_cont, hM_repr, _hM_tendsto⟩
  refine ⟨M, ?_, hM_mart, ?_⟩
  · refine ⟨hM_cont, ?_⟩
    intro t
    let hTargetMem : MemLp
        (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t)
        (ENNReal.ofReal (2 : ℝ)) μ :=
      by
        simpa using (brownianItoIntegralProcess_squareIntegrable (W := W) hH t)
    rcases hM_repr t with ⟨hM_memLp, hM_toLp⟩
    have hToLpEq :
        hM_memLp.toLp (M t) =
          hTargetMem.toLp (brownianItoIntegralProcessOfFiniteExpectedEnergy W hH t) := by
      simpa [Xtilde, hTargetMem] using hM_toLp
    -- Proof comment: equal fixed-time `L²` classes are exactly the modification relation.
    exact (MeasureTheory.MemLp.toLp_eq_toLp_iff hM_memLp hTargetMem).1 hToLpEq
  · intro t
    rcases hM_repr t with ⟨hM_memLp, _hM_toLp⟩
    -- Proof comment: the continuous representative already comes with an `L²` owner at every
    -- deterministic time.
    simpa using hM_memLp

/-- Theorem 25.18 (2): under the same hypotheses, the compensated square process
`N_t := M_t^2 - ∫_0^t H_s^2 ds` is a continuous martingale with `N_0 = 0`. -/
theorem brownianItoCompensatedSquareProcess_isZeroStartedContinuousMartingale
    [hIto : BrownianItoIntegral μ ℱ W]
    (hBrownian : IsBrownianMotion μ W)
    (hAdapted : Adapted ℱ W)
    (hIndep :
      ∀ ⦃s t : NNReal⦄, s ≤ t →
        Indep
          (MeasurableSpace.comap (fun ω ↦ W t ω - W s ω) (borel ℝ))
          (ℱ s)
          μ)
    (hH : HasFiniteExpectedEnergyOnEveryHorizon ℱ μ H)
    {M : Process Ω}
    (hM : IsBrownianItoContinuousModificationOfFiniteExpectedEnergy W hH M) :
    IsZeroStartedContinuousMartingale ℱ μ
      (MeasureTheory.brownianItoCompensatedSquareProcess M H) := by
  -- Route correction: the current hypothesis `hM` only records almost-sure continuity and a
  -- modification relation to the raw Brownian-Itô process. That is insufficient to force the
  -- exact pointwise identity `M 0 = 0`, so the final `zero` field in this theorem is not
  -- derivable from the present statement.
  sorry
end ProbabilityTheory
