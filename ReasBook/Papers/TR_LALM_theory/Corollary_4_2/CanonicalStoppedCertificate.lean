/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedRestart
public import TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis
public import TR_LALM_theory.Corollary_4_2.StoppedUniformResidualBridge
public import TR_LALM_theory.Corollary_4_2.CertifiedStoppedRestart
public import TR_LALM_theory.Corollary_4_2
import all TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

universe u v w

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {Ω' : Type w} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

namespace CanonicalStoppedCertificate

open StoppedAttemptAnalysis
open StoppedUniformResidualBridge

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {hK : 2 ≤ K}

/-! The lemmas in this namespace provide the interface needed to transport a
    finite stopped certificate through a measure-preserving noise map. -/

/-- Helper for Corollary 4.2: the state of a pulled stopped attempt is the
source state evaluated after the measure-preserving map. -/
theorem pullback_state_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : Fin (K + 1)) (ω : Ω') :
    (StoppedAttempt.pullback attempt φ hφ).state k ω = attempt.state k (φ ω) := by
  exact StoppedAttempt.pullback_state_apply attempt φ hφ k ω

/-- Helper for Corollary 4.2: the batch of a pulled stopped attempt is the
source batch evaluated after the measure-preserving map. -/
theorem pullback_batch_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    (StoppedAttempt.pullback attempt φ hφ).batch k ω = attempt.batch k (φ ω) := by
  exact StoppedAttempt.batch_pullback_aux attempt φ hφ k ω

/-- Helper for Corollary 4.2: the padded primal path of a pulled stopped
attempt is the source padded path after the map. -/
theorem pullback_point_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    StoppedAttempt.point (StoppedAttempt.pullback attempt φ hφ) k ω =
      StoppedAttempt.point attempt k (φ ω) := by
  exact StoppedAttempt.point_pullback_aux attempt φ hφ k ω

/-- Helper for Corollary 4.2: the padded multiplier path of a pulled stopped
attempt is the source padded multiplier after the map. -/
theorem pullback_multiplier_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    StoppedAttempt.multiplier (StoppedAttempt.pullback attempt φ hφ) k ω =
      StoppedAttempt.multiplier attempt k (φ ω) := by
  exact StoppedAttempt.multiplier_pullback_aux attempt φ hφ k ω

/-- Helper for Corollary 4.2: the padded base step of a pulled stopped attempt
is the source base step after the map. -/
theorem pullback_baseStep_apply
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P)
    (k : ℕ) (ω : Ω') :
    StoppedAttempt.baseStep (StoppedAttempt.pullback attempt φ hφ) k ω =
      StoppedAttempt.baseStep attempt k (φ ω) := by
  exact StoppedAttempt.baseStep_pullback_aux attempt φ hφ k ω

/-- Helper for Corollary 4.2: the clipped-gradient integrand commutes with a
measure-preserving stopped-attempt pullback. -/
theorem activeGradientErrorIntegrand_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k : ℕ) (ω : Ω') :
    activeGradientErrorIntegrand (StoppedAttempt.pullback attempt φ hφ) k ω =
      activeGradientErrorIntegrand attempt k (φ ω) := by
  unfold StoppedAttemptAnalysis.activeGradientErrorIntegrand
  by_cases hk : k < K
  · simp only [dif_pos hk, pullback_state_apply, pullback_batch_apply]
  · simp only [dif_neg hk]

/-- Helper for Corollary 4.2: the base-step integrand commutes with a
measure-preserving stopped-attempt pullback. -/
theorem activeBaseStepIntegrand_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k : ℕ) (ω : Ω') :
    activeBaseStepIntegrand (StoppedAttempt.pullback attempt φ hφ) k ω =
      activeBaseStepIntegrand attempt k (φ ω) := by
  unfold StoppedAttemptAnalysis.activeBaseStepIntegrand
  by_cases hk : k < K
  · simp only [dif_pos hk, pullback_baseStep_apply]
  · simp only [dif_neg hk]

/-- Helper for Corollary 4.2: the displacement integrand commutes with a
measure-preserving stopped-attempt pullback. -/
theorem activeDisplacementIntegrand_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) (k : ℕ) (ω : Ω') :
    activeDisplacementIntegrand (StoppedAttempt.pullback attempt φ hφ) k ω =
      activeDisplacementIntegrand attempt k (φ ω) := by
  unfold StoppedAttemptAnalysis.activeDisplacementIntegrand
  by_cases hk : k < K
  · simp only [dif_pos hk, pullback_point_apply]
  · simp only [dif_neg hk]

/-- Helper for Corollary 4.2: the finite success event pulls back exactly under
a measure-preserving stopped-attempt map. -/
theorem successEvent_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    StoppedAttempt.successEvent (StoppedAttempt.pullback attempt φ hφ) =
      φ ⁻¹' StoppedAttempt.successEvent attempt := by
  exact StoppedAttempt.successEvent_pullback attempt φ hφ

/-- Helper for Corollary 4.2: the analysis success event also pulls back under
    a measure-preserving stopped-attempt map. -/
theorem analysisSuccessEvent_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    StoppedAttemptAnalysis.successEvent (StoppedAttempt.pullback attempt φ hφ) =
      φ ⁻¹' StoppedAttemptAnalysis.successEvent attempt := by
  rw [StoppedAttemptAnalysis.successEvent_eq_stoppedAttempt,
    StoppedAttemptAnalysis.successEvent_eq_stoppedAttempt]
  exact successEvent_pullback attempt φ hφ

/-- Helper for Corollary 4.2: the three stopped energies are invariant under a
measure-preserving pullback. -/
theorem stoppedEnergies_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    stoppedGradientErrorEnergy (StoppedAttempt.pullback attempt φ hφ) =
        stoppedGradientErrorEnergy attempt ∧
      stoppedBaseStepEnergy (StoppedAttempt.pullback attempt φ hφ) =
        stoppedBaseStepEnergy attempt ∧
      stoppedDisplacementEnergy (StoppedAttempt.pullback attempt φ hφ) =
        stoppedDisplacementEnergy attempt := by
  have hIntegral (g : Ω → ℝ) (hg : Integrable g P) :
      (∫ ω', g (φ ω') ∂P') = ∫ ω, g ω ∂P := by
    have hgm : AEStronglyMeasurable g (Measure.map φ P') := by
      simpa only [hφ.map_eq] using hg.aestronglyMeasurable
    rw [← hφ.map_eq]
    exact (integral_map hφ.measurable.aemeasurable hgm).symm
  have hgradEq : stoppedGradientErrorEnergy (StoppedAttempt.pullback attempt φ hφ) =
      stoppedGradientErrorEnergy attempt := by
    unfold StoppedAttemptAnalysis.stoppedGradientErrorEnergy
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hIntegral (activeGradientErrorIntegrand attempt k)
      (integrable_activeGradientErrorIntegrand attempt k)]
    congr 1
    funext ω'
    exact activeGradientErrorIntegrand_pullback attempt φ hφ k ω'
  have hbaseEq : stoppedBaseStepEnergy (StoppedAttempt.pullback attempt φ hφ) =
      stoppedBaseStepEnergy attempt := by
    unfold StoppedAttemptAnalysis.stoppedBaseStepEnergy
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hIntegral (activeBaseStepIntegrand attempt k)
      (integrable_activeBaseStepIntegrand attempt k)]
    congr 1
    funext ω'
    exact activeBaseStepIntegrand_pullback attempt φ hφ k ω'
  have hdispEq : stoppedDisplacementEnergy (StoppedAttempt.pullback attempt φ hφ) =
      stoppedDisplacementEnergy attempt := by
    unfold StoppedAttemptAnalysis.stoppedDisplacementEnergy
    apply Finset.sum_congr rfl
    intro k hk
    rw [← hIntegral (activeDisplacementIntegrand attempt k)
      (integrable_activeDisplacementIntegrand attempt k)]
    congr 1
    funext ω'
    exact activeDisplacementIntegrand_pullback attempt φ hφ k ω'
  exact ⟨hgradEq, hbaseEq, hdispEq⟩

/-- Helper for Corollary 4.2: the finite observable law is unchanged by a
measure-preserving pullback of the stopped attempt. -/
theorem finiteObservable_measure_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    P'.map (stoppedAttemptFiniteObservable (StoppedAttempt.pullback attempt φ hφ)) =
      P.map (stoppedAttemptFiniteObservable attempt) := by
  have hobs : stoppedAttemptFiniteObservable (StoppedAttempt.pullback attempt φ hφ) =
      stoppedAttemptFiniteObservable attempt ∘ φ := by
    funext ω'
    exact StoppedAttempt.finiteObservable_pullback attempt φ hφ ω'
  rw [hobs, ← Measure.map_map (measurable_stoppedAttemptFiniteObservable attempt)
    hφ.measurable, hφ.map_eq]

/-- Helper for Corollary 4.2: the reference product law used by the residual
numerator is invariant under a measure-preserving stopped-attempt pullback. -/
theorem outputMeasure_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    stoppedAttemptOutputMeasure (StoppedAttempt.pullback attempt φ hφ) hK =
      stoppedAttemptOutputMeasure attempt hK := by
  unfold StoppedAttemptAnalysis.stoppedAttemptOutputMeasure
  rw [finiteObservable_measure_pullback attempt φ hφ]

/-- Helper for Corollary 4.2: the success-restricted residual numerator is
invariant under a measure-preserving stopped-attempt pullback. -/
theorem successRestrictedResidualNumerator_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    successRestrictedResidualNumerator (StoppedAttempt.pullback attempt φ hφ) hK =
      successRestrictedResidualNumerator attempt hK := by
  rw [successRestrictedResidualNumerator_def,
    successRestrictedResidualNumerator_def, outputMeasure_pullback attempt φ hφ]

/-- Helper for Corollary 4.2: a stopped certificate admits a transported
certificate with the same declared aggregate residual scale along every
measure-preserving pullback of its noise space. -/
theorem certificate_pullback_exists_with_residualBound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (certificate : StoppedAttemptCertificate attempt hK)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    ∃ transported :
        StoppedAttemptCertificate (StoppedAttempt.pullback attempt φ hφ) hK,
      transported.residualPerSuccessBound = certificate.residualPerSuccessBound := by
  have hsuccess :
      P' (StoppedAttemptAnalysis.successEvent (StoppedAttempt.pullback attempt φ hφ)) =
        P (StoppedAttemptAnalysis.successEvent attempt) := by
    rw [analysisSuccessEvent_pullback attempt φ hφ]
    have hmap := Measure.map_apply (μ := P') hφ.measurable
      (StoppedAttemptAnalysis.measurableSet_successEvent attempt)
    calc
      P' (φ ⁻¹' StoppedAttemptAnalysis.successEvent attempt) =
          (Measure.map φ P') (StoppedAttemptAnalysis.successEvent attempt) := hmap.symm
      _ = P (StoppedAttemptAnalysis.successEvent attempt) := by rw [hφ.map_eq]
  refine ⟨{
    successProbability_lower := by simpa only [hsuccess] using certificate.successProbability_lower
    residualPerSuccessBound := certificate.residualPerSuccessBound
    successRestrictedResidual_le := by
      simpa only [successRestrictedResidualNumerator_pullback attempt φ hφ, hsuccess]
        using certificate.successRestrictedResidual_le }, ?_⟩
  rfl

/-- Helper for Corollary 4.2: a stopped certificate admits a transported
certificate along every measure-preserving pullback of its noise space. -/
theorem certificate_pullback_nonempty
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (certificate : StoppedAttemptCertificate attempt hK)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    Nonempty (StoppedAttemptCertificate (StoppedAttempt.pullback attempt φ hφ) hK) := by
  obtain ⟨transported, _hspec⟩ :=
    certificate_pullback_exists_with_residualBound attempt certificate φ hφ
  exact ⟨transported⟩

/-- Corollary 4.2: a stopped certificate transports along every
measure-preserving pullback of its noise space. -/
noncomputable def certificate_pullback
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (certificate : StoppedAttemptCertificate attempt hK)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    StoppedAttemptCertificate (StoppedAttempt.pullback attempt φ hφ) hK :=
  Classical.choose
    (certificate_pullback_exists_with_residualBound attempt certificate φ hφ)

/-- Helper for Corollary 4.2: transporting a stopped certificate preserves
its declared aggregate residual scale. -/
theorem certificate_pullback_residualPerSuccessBound
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (certificate : StoppedAttemptCertificate attempt hK)
    (φ : Ω' → Ω) (hφ : MeasurePreserving φ P' P) :
    (certificate_pullback attempt certificate φ hφ).residualPerSuccessBound =
      certificate.residualPerSuccessBound := by
  exact Classical.choose_spec
    (certificate_pullback_exists_with_residualBound attempt certificate φ hφ)

/-- Helper for Corollary 4.2: transporting a stopped certificate across an
equality of attempts preserves its declared aggregate residual scale. -/
theorem residualPerSuccessBound_transport
    {attempt₁ attempt₂ :
      StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}
    (hAttempt : attempt₁ = attempt₂)
    (certificate : StoppedAttemptCertificate attempt₁ hK) :
    (hAttempt ▸ certificate).residualPerSuccessBound =
      certificate.residualPerSuccessBound := by
  cases hAttempt
  rfl

/-! The next bridge identifies the finite canonical recursion with the
    localized state of an arbitrary corrected stochastic run when the two
    runs use the same sample array.  The hypothesis is deliberately explicit:
    constructing a globally measurable corrected tail is a separate concern
    from the finite stopped analysis. -/

/-- Helper for Corollary 4.2: a canonical finite stopped state agrees with the
localized state of any corrected stochastic run driven by the same samples. -/
theorem canonicalAttempt_state_eq_localized_of_run
    (run : LALM.Correction.StochasticRun h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params Q B b)
    (h_sample : ∀ t i (ω : CanonicalSampleSpace Ξ),
      run.sample t i ω = CanonicalRun.sample t i ω)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : LALM.Correction.StochasticRun.Localization.RegionCondition
      h oracle params confidence X) (K : ℕ)
    (k : Fin (K + 1)) (ω : CanonicalSampleSpace Ξ) :
    (CanonicalStoppedAttempt.attempt (Q := Q) (B := B) (b := b)
      X hX initial_mem h_region K).state k ω =
      StochasticRun.Localization.localizedPreBatchState run X initial_mem
        h_region k.1 ω := by
  rw [CanonicalStoppedAttempt.attempt_state]
  rw [CanonicalStoppedAttempt.state_eq_canonicalLocalizedPreBatchState]
  have hlocalized :=
    StochasticRun.Localization.canonicalLocalizedPreBatchState_apply_samples
      run X initial_mem h_region k.1 ω
  simpa only [h_sample] using hlocalized

/-! The following construction packages the finite canonical recursion for an
    arbitrary corrected scheduled run.  Its sample measurability hypothesis
    is explicit because `StochasticRun` stores only a.e. measurability. -/

/-- Helper for Corollary 4.2: a scheduled corrected run admits a finite stopped
attempt whose state is the canonical localized sample-history recursion. -/
theorem stoppedAttemptOfRun_exists
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    ∃ attempt : SPIDER.Correction.StoppedScheduledAttempt h oracle P
        x₀ multiplier₀ params confidence K X,
      attempt.sample = run.sample ∧
      ∀ (k : Fin (K + 1)) (omega : Ω),
        attempt.state k omega =
          StochasticRun.Localization.canonicalLocalizedPreBatchState h oracle
            params (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
            (SPIDER.Correction.innerBatchSize h oracle params K) X initial_mem
            h_region k.1 (fun t i ↦ run.sample t.1 i omega) := by
  let stateFn : Fin (K + 1) → Ω →
      StochasticRun.Localization.LocalizedPreBatchState h params X :=
    fun k omega ↦
      StochasticRun.Localization.canonicalLocalizedPreBatchState h oracle params
        (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
        (SPIDER.Correction.innerBatchSize h oracle params K) X initial_mem
        h_region k.1 (fun t i ↦ run.sample t.1 i omega)
  have hhistory (k : Fin (K + 1)) : Measurable
      (fun omega : Ω ↦ fun t : Fin k.1 ↦ fun i : ℕ ↦ run.sample t.1 i omega) := by
    apply measurable_pi_lambda
    intro t
    apply measurable_pi_lambda
    intro i
    exact h_sample_meas t.1 i
  have hstate_meas (k : Fin (K + 1)) : Measurable (stateFn k) := by
    dsimp [stateFn]
    exact (StochasticRun.Localization.measurable_canonicalLocalizedPreBatchState
      X hX initial_mem h_region k.1).comp (hhistory k)
  have hstate_eq_localized (k : Fin (K + 1)) (omega : Ω) :
      stateFn k omega =
        StochasticRun.Localization.localizedPreBatchState run X initial_mem
          h_region k.1 omega := by
    dsimp [stateFn]
    exact StochasticRun.Localization.canonicalLocalizedPreBatchState_apply_samples
      run X initial_mem h_region k.1 omega
  have hindependent_state (k : Fin K) :
      ProbabilityTheory.IndepFun (stateFn k.castSucc)
        (fun omega i ↦ run.sample k i omega) P := by
    have hindependent :=
      StochasticRun.Localization.indepFun_localizedPreBatchState_freshBatch
        run X hX initial_mem h_region k.1
    have hstate_ae : stateFn k.castSucc =ᵐ[P]
        StochasticRun.Localization.localizedPreBatchState run X initial_mem
          h_region k.1 :=
      Filter.Eventually.of_forall fun omega ↦ hstate_eq_localized k.castSucc omega
    exact hindependent.congr hstate_ae.symm
      (Filter.Eventually.of_forall fun _ ↦ rfl)
  have hstate_zero (omega : Ω) :
      stateFn ⟨0, Nat.zero_lt_succ K⟩ omega =
        Sum.inr (StochasticRun.Localization.initialActivePreBatchState
          initial_mem h_region) := by
    dsimp [stateFn]
    rw [StochasticRun.Localization.canonicalLocalizedPreBatchState_zero]
  have hstate_succ (k : Fin K) (omega : Ω) :
      stateFn k.succ omega =
        StochasticRun.Localization.canonicalLocalizedTransition h oracle params
          (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
          (SPIDER.Correction.innerBatchSize h oracle params K) X h_region k.1
          (stateFn k.castSucc omega, fun i ↦ run.sample k i omega) := by
    dsimp [stateFn]
    rw [StochasticRun.Localization.canonicalLocalizedPreBatchState_succ]
    rfl
  refine ⟨{
    measurableSet_localization := hX
    initial_mem := initial_mem
    region_condition := h_region
    sample := run.sample
    measurable_sample := h_sample_meas
    hasLaw_sample := run.hasLaw_sample
    independent_sample := run.independent_sample
    state := stateFn
    measurable_state := hstate_meas
    independent_state_sample := hindependent_state
    state_zero := hstate_zero
    state_succ := hstate_succ }, rfl, ?_⟩
  intro k omega
  rfl

/-- Helper for Corollary 4.2: the finite stopped attempt canonically induced by
a scheduled run. -/
noncomputable def stoppedAttemptOfRun
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    SPIDER.Correction.StoppedScheduledAttempt h oracle P x₀ multiplier₀ params
      confidence K X :=
  Classical.choose
    (stoppedAttemptOfRun_exists run confidence X hX initial_mem h_region
      h_sample_meas)

/-- Helper for Corollary 4.2: the induced stopped attempt has the canonical
finite state at every index and sample point. -/
theorem stoppedAttemptOfRun_state_eq_canonical
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : Fin (K + 1)) (omega : Ω) :
    (stoppedAttemptOfRun run confidence X hX initial_mem h_region
      h_sample_meas).state k omega =
      StochasticRun.Localization.canonicalLocalizedPreBatchState h oracle
        params (SPIDER.refreshPeriod K) (SPIDER.refreshBatchSize K)
        (SPIDER.Correction.innerBatchSize h oracle params K) X initial_mem
        h_region k.1 (fun t i ↦ run.sample t.1 i omega) := by
  exact (Classical.choose_spec
    (stoppedAttemptOfRun_exists run confidence X hX initial_mem h_region
      h_sample_meas)).2 k omega

/-- Helper for Corollary 4.2: the induced finite stopped attempt uses exactly
the sample field of the scheduled run. -/
theorem stoppedAttemptOfRun_sample
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    (stoppedAttemptOfRun run confidence X hX initial_mem h_region
      h_sample_meas).sample = run.sample := by
  exact (Classical.choose_spec
    (stoppedAttemptOfRun_exists run confidence X hX initial_mem h_region
      h_sample_meas)).1

/-- Helper for Corollary 4.2: the induced stopped state agrees pointwise with
the run's survival-adapted localized state. -/
theorem stoppedAttemptOfRun_state_eq_localized
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : Fin (K + 1)) (omega : Ω) :
    (stoppedAttemptOfRun run confidence X hX initial_mem h_region
      h_sample_meas).state k omega =
      StochasticRun.Localization.localizedPreBatchState run X initial_mem
        h_region k.1 omega := by
  rw [stoppedAttemptOfRun_state_eq_canonical]
  exact StochasticRun.Localization.canonicalLocalizedPreBatchState_apply_samples
    run X initial_mem h_region k.1 omega

/-- Helper for Corollary 4.2: activity of the induced stopped attempt at an
in-horizon index is equivalent to survival of the corrected run to that index. -/
theorem stoppedAttemptOfRun_activeAt_iff_survival
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k ≤ K) (omega : Ω) :
    StoppedAttempt.activeAt
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega ↔
      omega ∈ StochasticRun.Localization.survivalEvent run X k := by
  classical
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  constructor
  · intro hactive
    by_contra hsurvival
    obtain ⟨a, ha⟩ :=
      (StoppedAttempt.activeAt_iff_state attempt k omega hk).mp hactive
    have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
      initial_mem h_region h_sample_meas ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
    have hlocal := StochasticRun.Localization.localizedPreBatchState_of_not_mem
      run X initial_mem h_region k omega hsurvival
    rw [hstate, hlocal] at ha
    cases ha
  · intro hsurvival
    apply (StoppedAttempt.activeAt_iff_state attempt k omega hk).mpr
    refine ⟨StochasticRun.Localization.actualActivePreBatchState run X initial_mem
      h_region k omega hsurvival, ?_⟩
    calc
      attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega =
          StochasticRun.Localization.localizedPreBatchState run X initial_mem
            h_region k omega :=
        stoppedAttemptOfRun_state_eq_localized run confidence X hX initial_mem
          h_region h_sample_meas ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
      _ = Sum.inr (StochasticRun.Localization.actualActivePreBatchState run X
          initial_mem h_region k omega hsurvival) :=
        StochasticRun.Localization.localizedPreBatchState_of_mem run X
          initial_mem h_region k omega hsurvival

/-- Helper for Corollary 4.2: the finite success event of the induced stopped
attempt is exactly the corrected run's survival event at the horizon. -/
theorem stoppedAttemptOfRun_successEvent_eq_survivalEvent
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    StoppedAttemptAnalysis.successEvent
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) =
      StochasticRun.Localization.survivalEvent run X K := by
  classical
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  ext omega
  rw [StoppedAttemptAnalysis.successEvent_eq_stoppedAttempt]
  constructor
  · intro hsuccess
    have hactive :=
      (StoppedAttempt.mem_successEvent_iff_all_active attempt omega).mp hsuccess
        K (le_refl K)
    exact (stoppedAttemptOfRun_activeAt_iff_survival run confidence X hX
      initial_mem h_region h_sample_meas K (le_refl K) omega).mp hactive
  · intro hsurvival
    apply (StoppedAttempt.mem_successEvent_iff_all_active attempt omega).mpr
    intro j hj
    have hsurvival_j : omega ∈ StochasticRun.Localization.survivalEvent run X j :=
      (StochasticRun.Localization.survivalEvent_antitone run X hj) hsurvival
    exact (stoppedAttemptOfRun_activeAt_iff_survival run confidence X hX
      initial_mem h_region h_sample_meas j hj omega).mpr hsurvival_j

/-! The next pointwise adapters expose the finite stopped observables in the
    normal form used by the full corrected-run estimates. -/

/-- Helper for Corollary 4.2: on terminal survival, every in-horizon primal
coordinate of the induced stopped attempt equals the corrected run coordinate. -/
theorem stoppedAttemptOfRun_point_eq_run_of_terminalSurvival
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k ≤ K) (omega : Ω)
    (hterminal : omega ∈
      StochasticRun.Localization.survivalEvent run X K) :
    StoppedAttempt.point
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega = run.point k omega := by
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  have hsurvival : omega ∈
      StochasticRun.Localization.survivalEvent run X k :=
    (StochasticRun.Localization.survivalEvent_antitone run X hk) hterminal
  let actual := StochasticRun.Localization.actualActivePreBatchState run X
    initial_mem h_region k omega hsurvival
  have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
    initial_mem h_region h_sample_meas
      ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
  have hlocal := StochasticRun.Localization.localizedPreBatchState_of_mem
    run X initial_mem h_region k omega hsurvival
  have hactive : attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega =
      Sum.inr actual := by
    exact hstate.trans hlocal
  have hcoordinate := StoppedAttempt.activeState_current_eq_point attempt k
    omega hk actual hactive
  calc
    StoppedAttempt.point attempt k omega = actual.1.1 := hcoordinate.symm
    _ = (StochasticRun.Localization.actualPreBatchData run k omega).1 := by
      rw [StochasticRun.Localization.actualActivePreBatchState_coe]
    _ = run.point k omega :=
      StochasticRun.Localization.actualPreBatchData_current run k omega

/-- Helper for Corollary 4.2: on terminal survival, every in-horizon multiplier
coordinate of the induced stopped attempt equals the corrected run coordinate. -/
theorem stoppedAttemptOfRun_multiplier_eq_run_of_terminalSurvival
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k ≤ K) (omega : Ω)
    (hterminal : omega ∈
      StochasticRun.Localization.survivalEvent run X K) :
    StoppedAttempt.multiplier
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega = run.multiplier k omega := by
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  have hsurvival : omega ∈
      StochasticRun.Localization.survivalEvent run X k :=
    (StochasticRun.Localization.survivalEvent_antitone run X hk) hterminal
  let actual := StochasticRun.Localization.actualActivePreBatchState run X
    initial_mem h_region k omega hsurvival
  have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
    initial_mem h_region h_sample_meas
      ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega
  have hlocal := StochasticRun.Localization.localizedPreBatchState_of_mem
    run X initial_mem h_region k omega hsurvival
  have hactive : attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ omega =
      Sum.inr actual := by
    exact hstate.trans hlocal
  have hcoordinate := StoppedAttempt.activeState_multiplier_eq_multiplier
    attempt k omega hk actual hactive
  calc
    StoppedAttempt.multiplier attempt k omega = actual.1.2.2.1 :=
      hcoordinate.symm
    _ = (StochasticRun.Localization.actualPreBatchData run k omega).2.2.1 := by
      rw [StochasticRun.Localization.actualActivePreBatchState_coe]
    _ = run.multiplier k omega :=
      StochasticRun.Localization.actualPreBatchData_multiplier run k omega

/-- Helper for Corollary 4.2: on a surviving prefix, the induced stopped base
step is the corrected run's base step. -/
theorem stoppedAttemptOfRun_baseStep_eq_run_of_survival
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k < K) (omega : Ω)
    (hsurvival : omega ∈ StochasticRun.Localization.survivalEvent run X k) :
    StoppedAttempt.baseStep
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega = run.baseStep k omega := by
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
    initial_mem h_region h_sample_meas
    ⟨k, Nat.lt_succ_of_lt hk⟩ omega
  have hlocal := StochasticRun.Localization.localizedPreBatchState_of_mem
    run X initial_mem h_region k omega hsurvival
  have hactive : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega =
      Sum.inr (StochasticRun.Localization.actualActivePreBatchState run X
        initial_mem h_region k omega hsurvival) :=
    hstate.trans hlocal
  rw [StoppedAttempt.activeState_baseStep_eq_baseStep attempt k omega hk
    (StochasticRun.Localization.actualActivePreBatchState run X initial_mem
      h_region k omega hsurvival) hactive]
  have hsample : attempt.sample = run.sample := by
    simpa only [attempt] using
      stoppedAttemptOfRun_sample run confidence X hX initial_mem h_region
        h_sample_meas
  have hbatch : attempt.batch k omega = fun i ↦ run.sample k i omega := by
    funext i
    exact congrFun (congrFun (congrFun hsample k) i) omega
  rw [hbatch]
  exact StochasticRun.Localization.canonicalActiveBaseStepAt_actual run X
    initial_mem h_region k omega hsurvival

/-- Helper for Corollary 4.2: after a stopped prefix exits, its padded base
step is zero. -/
theorem stoppedAttemptOfRun_baseStep_eq_zero_of_not_survival
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k < K) (omega : Ω)
    (hsurvival : omega ∉ StochasticRun.Localization.survivalEvent run X k) :
    StoppedAttempt.baseStep
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega = 0 := by
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  change StoppedAttempt.baseStep attempt k omega = 0
  have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
    initial_mem h_region h_sample_meas
    ⟨k, Nat.lt_succ_of_lt hk⟩ omega
  have hlocal := StochasticRun.Localization.localizedPreBatchState_of_not_mem
    run X initial_mem h_region k omega hsurvival
  have hstate' : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega =
      StochasticRun.Localization.localizedPreBatchState run X initial_mem
        h_region k omega := by
    simpa only [attempt] using hstate
  rw [StoppedAttempt.baseStep, dif_pos hk, hstate', hlocal]
  rfl

/-- Helper for Corollary 4.2: the finite stopped base-step integrand is the
survival indicator of the corresponding full-run square. -/
theorem stoppedAttemptOfRun_activeBaseStepIntegrand_eq_indicator
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k < K) (omega : Ω) :
    StoppedAttemptAnalysis.activeBaseStepIntegrand
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega =
      (StochasticRun.Localization.survivalEvent run X k).indicator
        (fun ω ↦ ‖run.baseStep k ω‖ ^ 2) omega := by
  by_cases hsurvival : omega ∈
      StochasticRun.Localization.survivalEvent run X k
  · rw [StoppedAttemptAnalysis.activeBaseStepIntegrand, dif_pos hk,
      stoppedAttemptOfRun_baseStep_eq_run_of_survival run confidence X hX
        initial_mem h_region h_sample_meas k hk omega hsurvival,
      Set.indicator_of_mem hsurvival]
  · rw [StoppedAttemptAnalysis.activeBaseStepIntegrand, dif_pos hk,
      stoppedAttemptOfRun_baseStep_eq_zero_of_not_survival run confidence X
        hX initial_mem h_region h_sample_meas k hk omega hsurvival,
      Set.indicator_of_notMem hsurvival]
    simp

/-- Helper for Corollary 4.2: the finite stopped gradient-error integrand is
the survival indicator of the corrected run's clipped estimator error. -/
theorem stoppedAttemptOfRun_activeGradientErrorIntegrand_eq_indicator
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i))
    (k : ℕ) (hk : k < K) (omega : Ω) :
    StoppedAttemptAnalysis.activeGradientErrorIntegrand
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) k omega =
      (StochasticRun.Localization.survivalEvent run X k).indicator
        (fun ω ↦ ‖run.gradientError k ω‖ ^ 2) omega := by
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  by_cases hsurvival : omega ∈
      StochasticRun.Localization.survivalEvent run X k
  · have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
      initial_mem h_region h_sample_meas
      ⟨k, Nat.lt_succ_of_lt hk⟩ omega
    have hlocal := StochasticRun.Localization.localizedPreBatchState_of_mem
      run X initial_mem h_region k omega hsurvival
    have hactive : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega =
        Sum.inr (StochasticRun.Localization.actualActivePreBatchState run X
          initial_mem h_region k omega hsurvival) :=
      hstate.trans hlocal
    have hsample : attempt.sample = run.sample := by
      simpa only [attempt] using
        stoppedAttemptOfRun_sample run confidence X hX initial_mem h_region
          h_sample_meas
    have hbatch : attempt.batch k omega = fun i ↦ run.sample k i omega := by
      funext i
      exact congrFun (congrFun (congrFun hsample k) i) omega
    rw [StoppedAttemptAnalysis.activeGradientErrorIntegrand_eq_canonical
      attempt k omega hk
      (StochasticRun.Localization.actualActivePreBatchState run X initial_mem
        h_region k omega hsurvival) hactive,
      hbatch, StochasticRun.Localization.actualActivePreBatchState_coe,
      StochasticRun.Localization.canonicalRawEstimateAt_apply_samples,
      StochasticRun.Localization.actualPreBatchData_current,
      Set.indicator_of_mem hsurvival, run.gradientError_apply,
      run.gradientEstimate_apply, SPIDER.estimate_apply]
  · have hstate := stoppedAttemptOfRun_state_eq_localized run confidence X hX
      initial_mem h_region h_sample_meas
      ⟨k, Nat.lt_succ_of_lt hk⟩ omega
    have hlocal := StochasticRun.Localization.localizedPreBatchState_of_not_mem
      run X initial_mem h_region k omega hsurvival
    have hstate' : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega =
        Sum.inl () := by
      exact hstate.trans hlocal
    rw [StoppedAttemptAnalysis.activeGradientErrorIntegrand, dif_pos hk,
      hstate', Set.indicator_of_notMem hsurvival]
    rfl

/-- Helper for Corollary 4.2: the two analytic energies of the induced finite
stopped attempt equal the corresponding survival-restricted run energies. -/
theorem stoppedAttemptOfRun_stoppedEnergies_eq
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (confidence : ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (hX : MeasurableSet X) (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    StoppedAttemptAnalysis.stoppedGradientErrorEnergy
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) =
        StochasticRun.Localization.stoppedGradientErrorEnergy run X K ∧
      StoppedAttemptAnalysis.stoppedBaseStepEnergy
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) =
        StochasticRun.Localization.stoppedBaseStepEnergy run X K := by
  constructor
  · rw [StoppedAttemptAnalysis.stoppedGradientErrorEnergy,
      StochasticRun.Localization.stoppedGradientErrorEnergy_def]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    rw [← integral_indicator₀
      (StochasticRun.Localization.nullMeasurableSet_survivalEvent run X hX k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega ↦
      stoppedAttemptOfRun_activeGradientErrorIntegrand_eq_indicator run
        confidence X hX initial_mem h_region h_sample_meas k hklt omega)
  · rw [StoppedAttemptAnalysis.stoppedBaseStepEnergy,
      StochasticRun.Localization.stoppedBaseStepEnergy_def]
    apply Finset.sum_congr rfl
    intro k hk
    have hklt : k < K := Finset.mem_range.mp hk
    rw [← integral_indicator₀
      (StochasticRun.Localization.nullMeasurableSet_survivalEvent run X hX k)]
    exact integral_congr_ae (Filter.Eventually.of_forall fun omega ↦
      stoppedAttemptOfRun_activeBaseStepIntegrand_eq_indicator run confidence
        X hX initial_mem h_region h_sample_meas k hklt omega)

/-- Helper for Corollary 4.2: the finite stopped attempt induced by a scheduled
run has the source estimator-error and base-step energy allowances. -/
theorem stoppedAttemptOfRun_energyBounds
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (hK : 2 ≤ K) (confidence : ℝ)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    StoppedAttemptAnalysis.stoppedGradientErrorEnergy
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) ≤ errorAverageConstant h oracle params ∧
      StoppedAttemptAnalysis.stoppedBaseStepEnergy
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) ≤ stepAverageConstant h oracle params := by
  have hequalities := stoppedAttemptOfRun_stoppedEnergies_eq run confidence X
    hX initial_mem h_region h_sample_meas
  have hbounds := StochasticRun.Localization.scheduledStoppedEnergyBounds
    K hK confidence X hX
    initial_mem run h_region
  rw [hequalities.1, hequalities.2]
  exact hbounds

/-- Helper for Corollary 4.2: the nonnegative residual scale for one successful
stopped attempt is the source inverse-horizon bound normalized by success probability. -/
noncomputable def stoppedResidualPerSuccessBound
    (confidence : ℝ) (K : ℕ) : ℝ≥0 :=
  Real.toNNReal (stochasticComplexityConstant h oracle params /
    ((1 - confidence) * ((K : ℝ) - 1)))

/-- Helper for Corollary 4.2: embedding the stopped residual scale into
`ℝ≥0∞` recovers the source `ENNReal.ofReal` expression. -/
theorem coe_stoppedResidualPerSuccessBound
    (confidence : ℝ) (K : ℕ) :
    (stoppedResidualPerSuccessBound (h := h) (oracle := oracle)
        (params := params) confidence K : ℝ≥0∞) =
      ENNReal.ofReal (stochasticComplexityConstant h oracle params /
        ((1 - confidence) * ((K : ℝ) - 1))) := by
  rfl

/-- Corollary 4.2: a corrected scheduled run induces a finite stopped attempt
with the source success-probability and success-restricted residual certificate. -/
theorem stoppedAttemptOfRun_certificate_exists
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    ∃ certificate : StoppedAttemptAnalysis.StoppedAttemptCertificate
        (stoppedAttemptOfRun run confidence X hX initial_mem h_region
          h_sample_meas) hK,
      certificate.residualPerSuccessBound =
        stoppedResidualPerSuccessBound (h := h) (oracle := oracle)
          (params := params) confidence K := by
  let attempt := stoppedAttemptOfRun run confidence X hX initial_mem h_region
    h_sample_meas
  let residualBound := stoppedResidualPerSuccessBound
    (h := h) (oracle := oracle) (params := params) confidence K
  have hsuccess : StoppedAttemptAnalysis.successEvent attempt =
      StochasticRun.Localization.survivalEvent run X K := by
    exact stoppedAttemptOfRun_successEvent_eq_survivalEvent run confidence X
      hX initial_mem h_region h_sample_meas
  have hsuccessLower : ENNReal.ofReal (1 - confidence) ≤
      P (StoppedAttemptAnalysis.successEvent attempt) := by
    rw [hsuccess]
    exact StochasticRun.Localization.survivalProbability_ge K hK confidence
      confidence_pos X hX initial_mem run h_region
  have hXregion : X ⊆ h.region := by
    intro x hx
    exact h_region.thickening_subset (Metric.self_subset_cthickening X hx)
  have hpoint : ∀ k ≤ K, ∀ omega,
      omega ∈ StochasticRun.Localization.survivalEvent run X K →
        StoppedAttempt.point attempt k omega = run.point k omega := by
    intro k hk omega hterminal
    exact stoppedAttemptOfRun_point_eq_run_of_terminalSurvival run confidence
      X hX initial_mem h_region h_sample_meas k hk omega hterminal
  have hmultiplier : ∀ k ≤ K, ∀ omega,
      omega ∈ StochasticRun.Localization.survivalEvent run X K →
        StoppedAttempt.multiplier attempt k omega = run.multiplier k omega := by
    intro k hk omega hterminal
    exact stoppedAttemptOfRun_multiplier_eq_run_of_terminalSurvival run
      confidence X hX initial_mem h_region h_sample_meas k hk omega hterminal
  have htransport :
      StoppedAttemptAnalysis.successRestrictedResidualNumerator attempt hK =
        ∫⁻ output in Set.univ ×ˢ
            StochasticRun.Localization.survivalEvent run X K,
          ENNReal.ofReal
            (KKT.residual f c
              (StochasticRun.UniformOutput.point run output)
              (StochasticRun.UniformOutput.multiplier run output) ^ 2)
          ∂LALM.StochasticRun.UniformOutput.measure K hK P := by
    exact successRestrictedResidualNumerator_eq_uniformSurvivalIntegral
      attempt run hsuccess hpoint hmultiplier hX hXregion
  have hnumerator :
      (∫⁻ output in Set.univ ×ˢ
          StochasticRun.Localization.survivalEvent run X K,
        ENNReal.ofReal
          (KKT.residual f c
            (StochasticRun.UniformOutput.point run output)
            (StochasticRun.UniformOutput.multiplier run output) ^ 2)
        ∂LALM.StochasticRun.UniformOutput.measure K hK P) ≤
      ENNReal.ofReal
        (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) := by
    exact StochasticRun.UniformOutput.survivalRestrictedResidualLIntegral_le
      K hK confidence X hX initial_mem run h_region
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by
    exact_mod_cast hKnat
  have hdenominator : 0 < (K : ℝ) - 1 := sub_pos.mpr hKreal
  have honeMinus : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hresidualBoundCoe : (residualBound : ℝ≥0∞) =
      ENNReal.ofReal (stochasticComplexityConstant h oracle params /
        ((1 - confidence) * ((K : ℝ) - 1))) := by
    exact coe_stoppedResidualPerSuccessBound confidence K
  have hnormalize :
      ENNReal.ofReal
          (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) =
        ENNReal.ofReal (1 - confidence) * (residualBound : ℝ≥0∞) := by
    rw [hresidualBoundCoe]
    rw [← ENNReal.ofReal_mul honeMinus.le]
    congr 1
    field_simp [honeMinus.ne', hdenominator.ne']
  have hresidual :
      StoppedAttemptAnalysis.successRestrictedResidualNumerator attempt hK ≤
        P (StoppedAttemptAnalysis.successEvent attempt) *
          (residualBound : ℝ≥0∞) := by
    calc
      StoppedAttemptAnalysis.successRestrictedResidualNumerator attempt hK =
          ∫⁻ output in Set.univ ×ˢ
              StochasticRun.Localization.survivalEvent run X K,
            ENNReal.ofReal
              (KKT.residual f c
                (StochasticRun.UniformOutput.point run output)
                (StochasticRun.UniformOutput.multiplier run output) ^ 2)
            ∂LALM.StochasticRun.UniformOutput.measure K hK P := htransport
      _ ≤ ENNReal.ofReal
          (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1)) :=
        hnumerator
      _ = ENNReal.ofReal (1 - confidence) * (residualBound : ℝ≥0∞) :=
        hnormalize
      _ ≤ P (StoppedAttemptAnalysis.successEvent attempt) *
          (residualBound : ℝ≥0∞) := by
        simpa only [mul_comm] using
          mul_le_mul_left hsuccessLower (residualBound : ℝ≥0∞)
  refine ⟨{
    successProbability_lower := hsuccessLower
    residualPerSuccessBound := residualBound
    successRestrictedResidual_le := hresidual }, rfl⟩

/-- Helper for Corollary 4.2: choose the finite stopped certificate induced by a
corrected scheduled run. -/
noncomputable def stoppedAttemptOfRun_certificate
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    StoppedAttemptAnalysis.StoppedAttemptCertificate
      (stoppedAttemptOfRun run confidence X hX initial_mem h_region
        h_sample_meas) hK :=
  Classical.choose
    (stoppedAttemptOfRun_certificate_exists run hK confidence confidence_pos
      confidence_lt_one X hX initial_mem h_region h_sample_meas)

/-- Helper for Corollary 4.2: the chosen stopped certificate carries the
source normalized residual scale. -/
theorem stoppedAttemptOfRun_certificate_residualPerSuccessBound
    (run : SPIDER.Correction.ScheduledRun h oracle P x₀ multiplier₀ params K)
    (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    (stoppedAttemptOfRun_certificate run hK confidence confidence_pos
      confidence_lt_one X hX initial_mem h_region h_sample_meas).residualPerSuccessBound =
      stoppedResidualPerSuccessBound (h := h) (oracle := oracle)
        (params := params) confidence K :=
  Classical.choose_spec
    (stoppedAttemptOfRun_certificate_exists run hK confidence confidence_pos
      confidence_lt_one X hX initial_mem h_region h_sample_meas)

end CanonicalStoppedCertificate

namespace CanonicalStoppedRestart

variable {confidence : ℝ} {K : ℕ} {hK : 2 ≤ K}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Corollary 4.2: a certificate for one canonical stopped scheduled attempt
induces a uniform certificate family on the countable canonical restart. -/
noncomputable def certificateFamily_of_base
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
  (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK) :
    ∀ i, StoppedAttemptAnalysis.StoppedAttemptCertificate
      (attempt (hK := hK) base i) hK :=
  fun i =>
    (attempt_eq_pullback (hK := hK) base i).symm ▸
      CanonicalStoppedCertificate.certificate_pullback base baseCertificate
        (noise (Ξ := Ξ) i)
        (measurePreserving_noise (Ξ := Ξ) (ν := ν) (K := K) (hK := hK) i)

/-- Helper for Corollary 4.2: every certificate in the canonical family has
the same declared aggregate residual scale as the base certificate. -/
theorem certificateFamily_of_base_residualPerSuccessBound
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK)
    (i : ℕ) :
    (certificateFamily_of_base (hK := hK) base baseCertificate i).residualPerSuccessBound =
      baseCertificate.residualPerSuccessBound := by
  unfold certificateFamily_of_base
  calc
    ((attempt_eq_pullback (hK := hK) base i).symm ▸
      CanonicalStoppedCertificate.certificate_pullback base baseCertificate
        (noise (Ξ := Ξ) i)
        (measurePreserving_noise (Ξ := Ξ) (ν := ν) (K := K)
          (hK := hK) i)).residualPerSuccessBound =
        (CanonicalStoppedCertificate.certificate_pullback base baseCertificate
          (noise (Ξ := Ξ) i)
          (measurePreserving_noise (Ξ := Ξ) (ν := ν) (K := K)
            (hK := hK) i)).residualPerSuccessBound :=
      CanonicalStoppedCertificate.residualPerSuccessBound_transport
        (attempt_eq_pullback (hK := hK) base i).symm
        (CanonicalStoppedCertificate.certificate_pullback base baseCertificate
          (noise (Ξ := Ξ) i)
          (measurePreserving_noise (Ξ := Ξ) (ν := ν) (K := K) (hK := hK) i))
    _ = baseCertificate.residualPerSuccessBound :=
      CanonicalStoppedCertificate.certificate_pullback_residualPerSuccessBound
        base baseCertificate (noise (Ξ := Ξ) i)
          (measurePreserving_noise (Ξ := Ξ) (ν := ν) (K := K) (hK := hK) i)

/-- Corollary 4.2: a canonical stopped restart with one certified base attempt
has a nonempty certified stopped-restart package. -/
theorem certifiedStoppedSafeguardedRestart_nonempty_of_base
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
  (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK) :
    Nonempty (CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) := by
  refine ⟨CertifiedStoppedSafeguardedRestart.ofRestart
    { attempt := attempt (hK := hK) base
      outputIndex := outputIndex (Ξ := Ξ)
      outputIndex_hasLaw := outputIndex_hasLaw (Ξ := Ξ) (ν := ν)
      outputIndex_indep_attempt := outputIndex_indep_attempt (hK := hK) base
      independent_attempt := independent_attempt (hK := hK) base }
    ?_⟩
  exact certificateFamily_of_base (hK := hK) base baseCertificate

/-- Corollary 4.2: choose the certified canonical stopped restart induced by a
certified base stopped attempt. -/
@[expose] noncomputable def certifiedStoppedSafeguardedRestart_of_base
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK) :
    CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  { restart :=
      { attempt := attempt (hK := hK) base
        outputIndex := outputIndex (Ξ := Ξ)
        outputIndex_hasLaw := outputIndex_hasLaw (Ξ := Ξ) (ν := ν)
        outputIndex_indep_attempt := outputIndex_indep_attempt (hK := hK) base
        independent_attempt := independent_attempt (hK := hK) base }
    certificate := certificateFamily_of_base (hK := hK) base baseCertificate }

/-- Helper for Corollary 4.2: a corrected run on the canonical product space
directly supplies a certified finite stopped restart, without an external
finite-certificate hypothesis. -/
noncomputable def certifiedStoppedSafeguardedRestart_of_run
    (run : SPIDER.Correction.ScheduledRun h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params K)
    (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) :
    CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
      (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  certifiedStoppedSafeguardedRestart_of_base (hK := hK)
    (CanonicalStoppedCertificate.stoppedAttemptOfRun run confidence X hX
      initial_mem h_region h_sample_meas)
    (CanonicalStoppedCertificate.stoppedAttemptOfRun_certificate run hK
      confidence confidence_pos confidence_lt_one X hX initial_mem h_region
      h_sample_meas)

/-- Helper for Corollary 4.2: the `i`th attempt of the explicitly certified
canonical restart is the measure-preserving pullback of the base attempt at
restart coordinate `i`. -/
@[simp] theorem certifiedStoppedSafeguardedRestart_of_base_attempt
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK)
    (i : ℕ) :
    (certifiedStoppedSafeguardedRestart_of_base (hK := hK) base
        baseCertificate).restart.attempt i =
      attempt (hK := hK) base i := by
  rfl

/-- Helper for Corollary 4.2: the `i`th certificate of the explicitly
certified canonical restart is the transported base certificate. -/
@[simp] theorem certifiedStoppedSafeguardedRestart_of_base_certificate
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK)
    (i : ℕ) :
    (certifiedStoppedSafeguardedRestart_of_base (hK := hK) base
        baseCertificate).certificate i =
      certificateFamily_of_base (hK := hK) base baseCertificate i := by
  rfl

/-- Helper for Corollary 4.2: every attempt certificate in the explicit
canonical restart retains the base certificate's aggregate residual scale. -/
@[simp] theorem certifiedStoppedSafeguardedRestart_of_base_residualPerSuccessBound
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (baseCertificate : StoppedAttemptAnalysis.StoppedAttemptCertificate base hK)
    (i : ℕ) :
    ((certifiedStoppedSafeguardedRestart_of_base (hK := hK) base
        baseCertificate).certificate i).residualPerSuccessBound =
      baseCertificate.residualPerSuccessBound := by
  rw [certifiedStoppedSafeguardedRestart_of_base_certificate,
    certificateFamily_of_base_residualPerSuccessBound]

/-- Helper for Corollary 4.2: every attempt in the run-induced canonical
restart carries the source normalized residual scale. -/
theorem certifiedStoppedSafeguardedRestart_of_run_residualPerSuccessBound
    (run : SPIDER.Correction.ScheduledRun h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params K)
    (hK : 2 ≤ K) (confidence : ℝ)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : StochasticRun.Localization.RegionCondition
      h oracle params confidence X)
    (h_sample_meas : ∀ k i, Measurable (run.sample k i)) (i : ℕ) :
    ((certifiedStoppedSafeguardedRestart_of_run run hK confidence
        confidence_pos confidence_lt_one X hX initial_mem h_region
        h_sample_meas).certificate i).residualPerSuccessBound =
      CanonicalStoppedCertificate.stoppedResidualPerSuccessBound
        (h := h) (oracle := oracle) (params := params) confidence K := by
  rw [certifiedStoppedSafeguardedRestart_of_run,
    certifiedStoppedSafeguardedRestart_of_base_residualPerSuccessBound,
    CanonicalStoppedCertificate.stoppedAttemptOfRun_certificate_residualPerSuccessBound]

end CanonicalStoppedRestart

end LALM.Correction

end
