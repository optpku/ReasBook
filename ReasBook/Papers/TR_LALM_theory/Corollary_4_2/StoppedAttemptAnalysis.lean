/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt
import all TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt
import all TR_LALM_theory.Corollary_4_2.LocalizedEstimatorActiveState
public import TR_LALM_theory.Corollary_4_2.StoppedRestart
public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorObservables
public import TR_LALM_theory.Corollary_4_2.StochasticEstimatorProbability
public import TR_LALM_theory.Corollary_4_2.StochasticEstimator
public import TR_LALM_theory.Corollary_4_2.EnergyGeometry
public import TR_LALM_theory.Corollary_4_2.StochasticEnergy
public import TR_LALM_theory.Corollary_4_2.StochasticMultiplier
public import TR_LALM_theory.Corollary_4_2.FixedPathEnergy

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}

namespace StoppedAttemptAnalysis

open StochasticRun.Localization

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}
variable {hK : 2 ≤ K}

/-- Corollary 4.2: a stopped attempt is active through the horizon exactly when
its finite localized state stays in the active summand at every pre-batch time.
This is the finite replacement for the old infinite `exitTime` predicate. -/
def successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : Set Ω :=
  {ω | ∀ k ≤ K, StoppedAttempt.activeAt attempt k ω}

/-- Helper for Corollary 4.2: the analysis success event agrees with the
terminal-activity success event owned by `StoppedAttempt`. -/
lemma successEvent_eq_stoppedAttempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    successEvent attempt = StoppedAttempt.successEvent attempt := by
  ext omega
  change (∀ k : ℕ, k ≤ K → StoppedAttempt.activeAt attempt k omega) ↔
    omega ∈ StoppedAttempt.successEvent attempt
  exact (StoppedAttempt.mem_successEvent_iff_all_active attempt omega).symm

/-- Helper for Corollary 4.2: the finite success event is an intersection of
the measurable active-state coordinate events. -/
lemma measurableSet_successEvent
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    MeasurableSet (successEvent attempt) := by
  have hcoord (k : ℕ) : MeasurableSet
      {ω | StoppedAttempt.activeAt attempt k ω} := by
    by_cases hk : k ≤ K
    · have hstate : Measurable (fun ω =>
          attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ ω) :=
        attempt.measurable_state ⟨k, Nat.lt_succ_iff.mpr hk⟩
      have hflag := StoppedAttempt.measurable_localizedActiveFlag
        (h := h) (params := params) (X := X)
      have heq : {ω | StoppedAttempt.activeAt attempt k ω} =
          (fun ω => StoppedAttempt.localizedActiveFlag
            (attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ ω)) ⁻¹'
            ({true} : Set Bool) := by
        ext ω
        change StoppedAttempt.activeAt attempt k ω ↔
          StoppedAttempt.localizedActiveFlag
            (attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ ω) = true
        exact (StoppedAttempt.activeAt_iff_state attempt k ω hk).trans
          (StoppedAttempt.localizedActiveFlag_eq_true_iff
            (attempt.state ⟨k, Nat.lt_succ_iff.mpr hk⟩ ω)).symm
      rw [heq]
      exact (measurableSet_singleton true).preimage (hflag.comp hstate)
    · have hempty : {ω | StoppedAttempt.activeAt attempt k ω} = ∅ := by
        ext ω
        constructor
        · intro hactive
          exact (StoppedAttempt.not_activeAt_of_horizon_lt attempt k
            (Nat.lt_of_not_ge hk) ω hactive).elim
        · intro hmem
          simp at hmem
      rw [hempty]
      exact MeasurableSet.empty
  have hfinite : MeasurableSet {ω | ∀ k ∈ Finset.range (K + 1),
      StoppedAttempt.activeAt attempt k ω} := by
    induction Finset.range (K + 1) using Finset.induction with
    | empty =>
        simp only [Finset.notMem_empty, IsEmpty.forall_iff, implies_true,
          Set.setOf_true, MeasurableSet.univ]
    | insert a s ha hs =>
        simpa only [Finset.forall_mem_insert, Set.setOf_and] using
          (hcoord a).inter hs
  simpa only [successEvent, Finset.mem_range, Nat.lt_succ_iff] using hfinite

/-- Helper for Corollary 4.2: a stopped attempt's active clipped-gradient error
square, with inactive and out-of-horizon indices assigned zero. -/
noncomputable def activeGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (ω : Ω) : ℝ :=
  if hk : k < K then
    Sum.elim (fun _ : Unit ↦ 0)
      (fun s : ActivePreBatchState h params X ↦
        ‖SPIDER.clip h.gradientBound
            (canonicalRawEstimateAt oracle Q B b k s.1
              (StoppedAttempt.batch attempt k ω)) -
          gradient f s.1.1‖ ^ 2)
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ ω)
  else 0

/-- Helper for Corollary 4.2: a stopped attempt's active raw-gradient error
square, expressed directly through its finite pre-batch state and fresh row. -/
noncomputable def activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) : ℝ :=
  if hk : k < K then
    localizedRawGradientErrorObservable h oracle params Q B b X k
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
        attempt.batch k omega)
  else 0

/-- Helper for Corollary 4.2: the finite active raw-gradient mean square is
the integral of the stopped raw-error observable. -/
noncomputable def activeRawGradientErrorMeanSquare
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) : ℝ :=
  ∫ omega, activeRawGradientErrorIntegrand attempt k omega ∂P

/-- Helper for Corollary 4.2: the active base-step square of a stopped attempt. -/
noncomputable def activeBaseStepIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (ω : Ω) : ℝ :=
  if _hk : k < K then
    ‖StoppedAttempt.baseStep attempt k ω‖ ^ 2
  else 0

/-- Helper for Corollary 4.2: the active corrected displacement square of a
stopped attempt. -/
noncomputable def activeDisplacementIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (ω : Ω) : ℝ :=
  if _hk : k < K then
    ‖StoppedAttempt.point attempt (k + 1) ω - StoppedAttempt.point attempt k ω‖ ^ 2
  else 0

/-- Helper for Corollary 4.2: every active clipped-gradient error integrand is
pointwise nonnegative. -/
theorem activeGradientErrorIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeGradientErrorIntegrand attempt k omega := by
  unfold activeGradientErrorIntegrand
  split
  · cases attempt.state _ omega with
    | inl u => simp
    | inr s => exact sq_nonneg _
  · exact le_rfl

/-- Helper for Corollary 4.2: every finite active raw-gradient error
integrand is pointwise nonnegative. -/
theorem activeRawGradientErrorIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeRawGradientErrorIntegrand attempt k omega := by
  unfold activeRawGradientErrorIntegrand
  split
  · rw [localizedRawGradientErrorObservable_apply]
    cases attempt.state _ omega with
    | inl inactive => exact le_rfl
    | inr active => exact sq_nonneg _
  · exact le_rfl

/-- Helper for Corollary 4.2: every active base-step integrand is pointwise
nonnegative. -/
theorem activeBaseStepIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeBaseStepIntegrand attempt k omega := by
  unfold activeBaseStepIntegrand
  split
  · exact sq_nonneg _
  · exact le_rfl

/-- Helper for Corollary 4.2: every active corrected-displacement integrand is
pointwise nonnegative. -/
theorem activeDisplacementIntegrand_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    0 ≤ activeDisplacementIntegrand attempt k omega := by
  unfold activeDisplacementIntegrand
  split
  · exact sq_nonneg _
  · exact le_rfl

/-- Helper for Corollary 4.2: every stopped clipped-gradient error integrand
is measurable, including the inactive and out-of-horizon zero branches. -/
theorem measurable_activeGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Measurable (activeGradientErrorIntegrand attempt k) := by
  by_cases hk : k < K
  · let observable :
        LocalizedPreBatchState h params X × (ℕ → Ξ) → ℝ :=
      Sum.elim
          (fun _ : Unit × (ℕ → Ξ) ↦ 0)
          (fun z : ActivePreBatchState h params X × (ℕ → Ξ) ↦
            ‖canonicalClippedEstimateAt h oracle Q B b k
                (activeNumericalInput z) - gradient f z.1.1.1‖ ^ 2) ∘
        MeasurableEquiv.sumProdDistrib Unit (ActivePreBatchState h params X)
          (ℕ → Ξ)
    have hcurrent : Measurable (fun z :
        ActivePreBatchState h params X × (ℕ → Ξ) ↦ z.1.1.1) := by
      fun_prop
    have hgradient : Measurable (fun z :
        ActivePreBatchState h params X × (ℕ → Ξ) ↦
          gradient f z.1.1.1) := by
      have hgradientExtension : Measurable (fun z :
          ActivePreBatchState h params X × (ℕ → Ξ) ↦
            h.objectiveGradientExtension z.1.1.1) :=
        h.measurable_objectiveGradientExtension.comp hcurrent
      have hgradientEq :
          (fun z : ActivePreBatchState h params X × (ℕ → Ξ) ↦
              gradient f z.1.1.1) =
            fun z ↦ h.objectiveGradientExtension z.1.1.1 := by
        funext z
        exact (h.objectiveGradientExtension_eq
          (canonicalActivePoint_mem_region attempt.region_condition z)).symm
      rw [hgradientEq]
      exact hgradientExtension
    have hclipped : Measurable (fun z :
        ActivePreBatchState h params X × (ℕ → Ξ) ↦
          canonicalClippedEstimateAt h oracle Q B b k
            (activeNumericalInput z)) :=
      (measurable_canonicalClippedEstimateAt h oracle Q B b k).comp
        measurable_activeNumericalInput
    have hobservable : Measurable observable := by
      unfold observable
      exact (measurable_const.sumElim
        ((hclipped.sub hgradient).norm.pow_const 2)).comp
          (MeasurableEquiv.sumProdDistrib Unit
            (ActivePreBatchState h params X) (ℕ → Ξ)).measurable
    have hstateBatch : Measurable (fun omega ↦
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
          attempt.batch k omega)) :=
      (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).prodMk
        (StoppedAttempt.measurable_batch attempt k)
    have heq : activeGradientErrorIntegrand attempt k =
        observable ∘ fun omega ↦
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
            attempt.batch k omega) := by
      funext omega
      simp only [activeGradientErrorIntegrand, dif_pos hk, Function.comp_apply]
      cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega with
      | inl inactive =>
          unfold observable
          rfl
      | inr active =>
          unfold observable canonicalClippedEstimateAt activeNumericalInput
          rfl
    rw [heq]
    exact hobservable.comp hstateBatch
  · have heq : activeGradientErrorIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      unfold activeGradientErrorIntegrand
      rw [dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Corollary 4.2: every finite active raw-gradient error
integrand is measurable. -/
theorem measurable_activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Measurable (activeRawGradientErrorIntegrand attempt k) := by
  by_cases hk : k < K
  · have heq : activeRawGradientErrorIntegrand attempt k =
        localizedRawGradientErrorObservable h oracle params Q B b X k ∘
          fun omega ↦
            (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
              attempt.batch k omega) := by
      funext omega
      rw [activeRawGradientErrorIntegrand, dif_pos hk]
      rfl
    rw [heq]
    exact (measurable_localizedRawGradientErrorObservable
      h oracle params Q B b X k).comp
        ((attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).prodMk
          (StoppedAttempt.measurable_batch attempt k))
  · have heq : activeRawGradientErrorIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      rw [activeRawGradientErrorIntegrand, dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Corollary 4.2: on an active finite state, the raw-error
integrand is the squared padded raw estimate error at the stopped point. -/
theorem activeRawGradientErrorIntegrand_eq_rawEstimate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    activeRawGradientErrorIntegrand attempt k omega =
      ‖attempt.rawEstimate k omega - gradient f (attempt.point k omega)‖ ^ 2 := by
  have hx := canonicalActivePoint_mem_region attempt.region_condition
    (a, attempt.batch k omega)
  have hraw := StoppedAttempt.activeState_rawEstimate_at
    attempt k omega hk a ha
  have hpoint := StoppedAttempt.activeState_current_eq_point
    attempt k omega (Nat.le_of_lt hk) a ha
  rw [activeRawGradientErrorIntegrand, dif_pos hk,
    localizedRawGradientErrorObservable_apply, ha]
  dsimp
  rw [h.objectiveGradientExtension_eq hx, ← hraw, hpoint]

/-- Helper for Corollary 4.2: statewise fresh-batch bounds transfer through
the finite stopped-state independence field to the actual raw-error moment. -/
theorem activeRawGradientErrorMeanSquare_le_of_sectionBounds
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K)
    (C : LocalizedPreBatchState h params X → ℝ)
    (hsection : ∀ s, Integrable (fun batch ↦
      localizedRawGradientErrorObservable h oracle params Q B b X k
        (s, batch)) (P.map (attempt.batch k)))
    (hC : Integrable C
      (P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)))
    (hbound : ∀ s,
      (∫ batch, localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch) ∂P.map (attempt.batch k)) ≤ C s) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        ∫ s, C s ∂P.map
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) := by
  have hstate : AEMeasurable
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) P :=
    (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).aemeasurable
  have hbatch : AEMeasurable (attempt.batch k) P :=
    (StoppedAttempt.measurable_batch attempt k).aemeasurable
  have hindependent : ProbabilityTheory.IndepFun
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)
      (attempt.batch k) P := by
    have hbatch_eq : attempt.batch k =
        (fun omega i ↦ attempt.sample k i omega) := by
      funext omega i
      rfl
    rw [hbatch_eq]
    simpa only [Fin.castSucc_mk] using
      attempt.independent_state_sample ⟨k, hk⟩
  have hnonnegative : ∀ z :
      LocalizedPreBatchState h params X × (ℕ → Ξ),
      0 ≤ localizedRawGradientErrorObservable
        h oracle params Q B b X k z := by
    rintro ⟨s, batch⟩
    rw [localizedRawGradientErrorObservable_apply]
    cases s with
    | inl inactive => exact le_rfl
    | inr active => exact sq_nonneg _
  have hpair :=
    StochasticRun.EstimatorProbability.independentPair_integrable_integral_le
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)
      (attempt.batch k)
      (localizedRawGradientErrorObservable h oracle params Q B b X k) C
      hindependent hstate hbatch
      (measurable_localizedRawGradientErrorObservable
        h oracle params Q B b X k).aemeasurable
      hnonnegative (Filter.Eventually.of_forall hsection) hC
      (Filter.Eventually.of_forall hbound)
  have hidentify : (fun omega ↦
      localizedRawGradientErrorObservable h oracle params Q B b X k
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega,
          attempt.batch k omega)) =ᵐ[P]
      activeRawGradientErrorIntegrand attempt k :=
    Filter.Eventually.of_forall fun omega ↦ by
      rw [activeRawGradientErrorIntegrand, dif_pos hk]
  refine ⟨hpair.1.congr hidentify, ?_⟩
  rw [activeRawGradientErrorMeanSquare, ← integral_congr_ae hidentify]
  exact hpair.2

/-- Helper for Corollary 4.2: a finite stopped refresh has integrable active
raw error and resets its mean square to the large-batch variance scale. -/
theorem activeRawGradientError_refresh
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hrefresh : k % Q = 0) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
  classical
  have hbatch : AEMeasurable (attempt.batch k) P :=
    (StoppedAttempt.measurable_batch attempt k).aemeasurable
  have hbatchIndependent : ProbabilityTheory.iIndepFun (attempt.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using attempt.independent_sample.precomp hinjective
  have hsection : ∀ s : LocalizedPreBatchState h params X,
      Integrable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) (P.map (attempt.batch k)) := by
    intro s
    have hsectionMeasurable : Measurable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) :=
      (measurable_localizedRawGradientErrorObservable
        h oracle params Q B b X k).comp
          (measurable_const.prodMk measurable_id)
    cases s with
    | inl inactive =>
        simpa only [localizedRawGradientErrorObservable_apply] using
          (integrable_const (μ := P.map (attempt.batch k)) (0 : ℝ))
    | inr active =>
        have hcurrent : active.1.1 ∈ h.region :=
          attempt.region_condition.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed :=
          StochasticRun.EstimatorProbability.fixedPointRefreshBatchMeanSquare_le
            (oracle := oracle) active.1.1 hcurrent (attempt.sample k) B
            (attempt.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        refine (integrable_map_measure
          hsectionMeasurable.aestronglyMeasurable hbatch).2 ?_
        simpa only [Function.comp_def,
          localizedRawGradientErrorObservable_of_refresh, hrefresh,
          hgradient, StoppedAttempt.batch] using hfixed.1
  have hbound : ∀ s : LocalizedPreBatchState h params X,
      (∫ batch, localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch) ∂P.map (attempt.batch k)) ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
    intro s
    have hsectionMeasurable : Measurable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) :=
      (measurable_localizedRawGradientErrorObservable
        h oracle params Q B b X k).comp
          (measurable_const.prodMk measurable_id)
    cases s with
    | inl inactive =>
        simp only [localizedRawGradientErrorObservable_apply, integral_zero]
        positivity
    | inr active =>
        have hcurrent : active.1.1 ∈ h.region :=
          attempt.region_condition.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed :=
          StochasticRun.EstimatorProbability.fixedPointRefreshBatchMeanSquare_le
            (oracle := oracle) active.1.1 hcurrent (attempt.sample k) B
            (attempt.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        rw [integral_map hbatch hsectionMeasurable.aestronglyMeasurable]
        simpa only [Function.comp_apply,
          localizedRawGradientErrorObservable_of_refresh, hrefresh,
          hgradient, StoppedAttempt.batch] using hfixed.2
  have hstate : AEMeasurable
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) P :=
    (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).aemeasurable
  have hbridge := activeRawGradientErrorMeanSquare_le_of_sectionBounds
    attempt k hk (fun _ ↦ (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ))
      hsection (integrable_const _) hbound
  refine ⟨hbridge.1, hbridge.2.trans_eq ?_⟩
  rw [integral_const, Measure.real,
    Measure.map_apply_of_aemeasurable hstate MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, ENNReal.toReal_one, one_smul]

/-- Helper for Corollary 4.2: every stopped base-step square integrand is
measurable. -/
theorem measurable_activeBaseStepIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Measurable (activeBaseStepIntegrand attempt k) := by
  by_cases hk : k < K
  · have heq : activeBaseStepIntegrand attempt k =
        fun omega ↦ ‖StoppedAttempt.baseStep attempt k omega‖ ^ 2 := by
      funext omega
      unfold activeBaseStepIntegrand
      rw [dif_pos hk]
    rw [heq]
    exact (StoppedAttempt.measurable_baseStep attempt k).norm.pow_const 2
  · have heq : activeBaseStepIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      unfold activeBaseStepIntegrand
      rw [dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Corollary 4.2: every stopped corrected-displacement square
integrand is measurable. -/
theorem measurable_activeDisplacementIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Measurable (activeDisplacementIntegrand attempt k) := by
  by_cases hk : k < K
  · have heq : activeDisplacementIntegrand attempt k = fun omega ↦
        ‖StoppedAttempt.point attempt (k + 1) omega -
          StoppedAttempt.point attempt k omega‖ ^ 2 := by
      funext omega
      unfold activeDisplacementIntegrand
      rw [dif_pos hk]
    rw [heq]
    exact (((StoppedAttempt.measurable_point attempt (k + 1)).sub
      (StoppedAttempt.measurable_point attempt k)).norm.pow_const 2)
  · have heq : activeDisplacementIntegrand attempt k =
        fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      unfold activeDisplacementIntegrand
      rw [dif_neg hk]
    rw [heq]
    exact measurable_const

/-- Helper for Corollary 4.2: every padded stopped base step is uniformly
bounded by the prescribed localization radius. -/
theorem norm_stoppedBaseStep_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    ‖StoppedAttempt.baseStep attempt k omega‖ ≤ params.delta := by
  unfold StoppedAttempt.baseStep
  split
  · cases attempt.state _ omega with
    | inl inactive => simp
    | inr active =>
        exact norm_canonicalActiveBaseStepAt_le attempt.region_condition k
          (active, attempt.batch k omega)
  · simp

/-- Helper for Corollary 4.2: the squared padded base steps of a stopped
attempt have total pathwise energy at most `K * δ²`. -/
theorem sumActiveBaseStepIntegrand_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    (∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k omega) ≤
      (K : ℝ) * (params.delta : ℝ) ^ 2 := by
  have hterm (k : ℕ) (hk : k ∈ Finset.range K) :
      activeBaseStepIntegrand attempt k omega ≤ (params.delta : ℝ) ^ 2 := by
    have hklt : k < K := Finset.mem_range.mp hk
    unfold activeBaseStepIntegrand
    rw [dif_pos hklt]
    exact (sq_le_sq₀ (norm_nonneg _)
      (NNReal.coe_nonneg params.delta)).2
      (norm_stoppedBaseStep_le attempt k omega)
  calc
    (∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k omega) ≤
        ∑ k ∈ Finset.range K, (params.delta : ℝ) ^ 2 := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k hk
    _ = (K : ℝ) * (params.delta : ℝ) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- Helper for Corollary 4.2: on an active in-horizon state, the finite base
step integrand is the square of the canonical active step. -/
theorem activeBaseStepIntegrand_eq_canonical
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    activeBaseStepIntegrand attempt k omega =
      ‖canonicalActiveBaseStepAt h oracle params Q B b k
          (a, attempt.batch k omega)‖ ^ 2 := by
  rw [activeBaseStepIntegrand, dif_pos hk,
    StoppedAttempt.activeState_baseStep_eq_baseStep attempt k omega hk a ha]

/-- Helper for Corollary 4.2: on an active in-horizon state, the finite
gradient-error integrand exposes the canonical clipped estimator and current
point. -/
theorem activeGradientErrorIntegrand_eq_canonical
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K)
    (a : ActivePreBatchState h params X)
    (ha : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega = Sum.inr a) :
    activeGradientErrorIntegrand attempt k omega =
      ‖SPIDER.clip h.gradientBound
          (canonicalRawEstimateAt oracle Q B b k a.1
            (attempt.batch k omega)) - gradient f a.1.1‖ ^ 2 := by
  rw [activeGradientErrorIntegrand, dif_pos hk, ha]
  rfl

/-- Helper for Corollary 4.2: activity propagates backwards through every
prefix of an in-horizon stopped trajectory. -/
theorem activeAt_of_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) (j k : ℕ) (hjk : j ≤ k) (hk : k ≤ K)
    (hactive : StoppedAttempt.activeAt attempt k omega) :
    StoppedAttempt.activeAt attempt j omega := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := Nat.eq_zero_of_le_zero hjk
      simpa only [hj] using hactive
  | succ k ih =>
      have hklt : k < K := Nat.lt_of_succ_le hk
      have hactive' : StoppedAttempt.activeAt attempt (k + 1) omega := by
        simpa only [Nat.succ_eq_add_one] using hactive
      have hprev : StoppedAttempt.activeAt attempt k omega :=
        ((StoppedAttempt.activeAt_succ_iff attempt ⟨k, hklt⟩ omega).mp
          hactive').1
      by_cases hlast : j = k + 1
      · simpa only [hlast] using hactive'
      · exact ih (j := j) (by omega) (Nat.le_of_lt hklt) hprev

/-- Helper for Corollary 4.2: the state field of every stopped attempt is
uniquely determined by its finite sample history and the canonical localized
transition. -/
theorem state_eq_canonicalLocalizedPreBatchState
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : Fin (K + 1)) (omega : Ω) :
    attempt.state k omega =
      canonicalLocalizedPreBatchState h oracle params Q B b X
        attempt.initial_mem attempt.region_condition k.1
        (fun t i ↦ attempt.sample t.1 i omega) := by
  have hstate (j : ℕ) (hj : j ≤ K) :
      attempt.state ⟨j, Nat.lt_succ_iff.mpr hj⟩ omega =
        canonicalLocalizedPreBatchState h oracle params Q B b X
          attempt.initial_mem attempt.region_condition j
          (fun t i ↦ attempt.sample t.1 i omega) := by
    induction j with
    | zero =>
        rw [attempt.state_zero]
        rw [canonicalLocalizedPreBatchState_zero]
    | succ j ih =>
        have hjlt : j < K := Nat.lt_of_succ_le hj
        have htransition := attempt.state_succ ⟨j, hjlt⟩ omega
        have hsuccessorIndex :
            (⟨j + 1, Nat.lt_succ_iff.mpr hj⟩ : Fin (K + 1)) =
              (⟨j, hjlt⟩ : Fin K).succ := by
          apply Fin.ext
          rfl
        have hpredecessorIndex :
            (⟨j, Nat.lt_succ_of_lt hjlt⟩ : Fin (K + 1)) =
              (⟨j, hjlt⟩ : Fin K).castSucc := by
          apply Fin.ext
          rfl
        rw [hsuccessorIndex, htransition,
          canonicalLocalizedPreBatchState_succ]
        rw [← hpredecessorIndex, ih (Nat.le_of_lt hjlt)]
        rfl
  have hk : k.1 ≤ K := Nat.lt_succ_iff.mp k.isLt
  have hkIndex : (⟨k.1, Nat.lt_succ_iff.mpr hk⟩ : Fin (K + 1)) = k := by
    apply Fin.ext
    rfl
  rw [← hkIndex]
  exact hstate k.1 hk

/-- Helper for Corollary 4.2: every in-horizon stopped corrected displacement
is uniformly bounded by the corrected displacement factor times `params.delta`. -/
theorem norm_stoppedPointDisplacement_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K) :
    ‖StoppedAttempt.point attempt (k + 1) omega -
        StoppedAttempt.point attempt k omega‖ ≤
      displacementFactor h params.delta * params.delta := by
  have hfactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def]
    have hstepConstantNonneg : 0 ≤ stepConstant h := by
      rw [stepConstant_def]
      positivity
    exact add_nonneg (by norm_num)
      (mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta))
  rw [StoppedAttempt.point, dif_pos hk]
  cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega with
  | inl inactive =>
      unfold StoppedAttempt.paddedPointTransition
      change ‖StoppedAttempt.point attempt k omega -
        StoppedAttempt.point attempt k omega‖ ≤
          displacementFactor h params.delta * params.delta
      rw [sub_self, norm_zero]
      exact mul_nonneg hfactorNonneg (NNReal.coe_nonneg params.delta)
  | inr active =>
      unfold StoppedAttempt.paddedPointTransition
      change ‖canonicalActiveNextPointAt h oracle params Q B b k
          (active, attempt.batch k omega) -
            StoppedAttempt.point attempt k omega‖ ≤
        displacementFactor h params.delta * params.delta
      have hcurrent := StoppedAttempt.activeState_current_eq_point attempt k omega
        (Nat.le_of_lt hk) active hstate
      rw [← hcurrent]
      have hadmissible := canonicalActiveBaseStepAt_isAdmissible
        (Q := Q) (B := B) (b := b) attempt.region_condition k
          (active, attempt.batch k omega)
      have hstep := norm_canonicalActiveBaseStepAt_le
        (Q := Q) (B := B) (b := b) attempt.region_condition k
          (active, attempt.batch k omega)
      have hdisplacement := displacement_le h params.delta active.1.1
        (canonicalActiveBaseStepAt h oracle params Q B b k
          (active, attempt.batch k omega)) hadmissible hstep
      exact hdisplacement.trans
        (mul_le_mul_of_nonneg_left hstep hfactorNonneg)

/-- Corollary 4.2: the clipped-gradient error square of an arbitrary finite
stopped attempt is automatically integrable. -/
theorem integrable_activeGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Integrable (activeGradientErrorIntegrand attempt k) P := by
  have hbound (omega : Ω) :
      ‖activeGradientErrorIntegrand attempt k omega‖ ≤
        (2 * (h.gradientBound : ℝ)) ^ 2 := by
    unfold activeGradientErrorIntegrand
    split
    · cases hstate : attempt.state _ omega with
      | inl inactive => simp
      | inr active =>
          have hx := canonicalActivePoint_mem_region attempt.region_condition
            (active, attempt.batch k omega)
          have hclipped :
              ‖SPIDER.clip h.gradientBound
                (canonicalRawEstimateAt oracle Q B b k active.1
                  (attempt.batch k omega))‖ ≤ h.gradientBound :=
            SPIDER.norm_clip_le h.gradientBound _
          have hgradient : ‖gradient f active.1.1‖ ≤ h.gradientBound :=
            h.norm_gradient_le active.1.1 hx
          have herror :
              ‖SPIDER.clip h.gradientBound
                  (canonicalRawEstimateAt oracle Q B b k active.1
                    (attempt.batch k omega)) - gradient f active.1.1‖ ≤
                2 * (h.gradientBound : ℝ) := by
            calc
              _ ≤ ‖SPIDER.clip h.gradientBound
                    (canonicalRawEstimateAt oracle Q B b k active.1
                      (attempt.batch k omega))‖ +
                    ‖gradient f active.1.1‖ := norm_sub_le _ _
              _ ≤ 2 * (h.gradientBound : ℝ) := by linarith
          have hrightNonneg : 0 ≤ 2 * (h.gradientBound : ℝ) := by
            positivity
          have hsquare :=
            (sq_le_sq₀ (norm_nonneg _) hrightNonneg).2 herror
          simpa only [Sum.elim_inr,
            Real.norm_of_nonneg (sq_nonneg _)] using hsquare
    · simpa only [norm_zero] using
        (sq_nonneg (2 * (h.gradientBound : ℝ)))
  exact Integrable.mono' (integrable_const _)
    (measurable_activeGradientErrorIntegrand attempt k).aestronglyMeasurable
    (ae_of_all P hbound)

/-- Corollary 4.2: the base-step square of an arbitrary finite stopped attempt
is automatically integrable. -/
theorem integrable_activeBaseStepIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Integrable (activeBaseStepIntegrand attempt k) P := by
  have hbound (omega : Ω) :
      ‖activeBaseStepIntegrand attempt k omega‖ ≤
        (params.delta : ℝ) ^ 2 := by
    unfold activeBaseStepIntegrand
    split
    · have hsquare := (sq_le_sq₀ (norm_nonneg _)
          (NNReal.coe_nonneg params.delta)).2
        (norm_stoppedBaseStep_le attempt k omega)
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
    · simpa only [norm_zero] using sq_nonneg (params.delta : ℝ)
  exact Integrable.mono' (integrable_const _)
    (measurable_activeBaseStepIntegrand attempt k).aestronglyMeasurable
    (ae_of_all P hbound)

/-- Corollary 4.2: the corrected-displacement square of an arbitrary finite
stopped attempt is automatically integrable. -/
theorem integrable_activeDisplacementIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Integrable (activeDisplacementIntegrand attempt k) P := by
  have hfactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def]
    have hstepConstantNonneg : 0 ≤ stepConstant h := by
      rw [stepConstant_def]
      positivity
    exact add_nonneg (by norm_num)
      (mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta))
  have hrightNonneg :
      0 ≤ displacementFactor h params.delta * (params.delta : ℝ) :=
    mul_nonneg hfactorNonneg (NNReal.coe_nonneg params.delta)
  have hbound (omega : Ω) :
      ‖activeDisplacementIntegrand attempt k omega‖ ≤
        (displacementFactor h params.delta * (params.delta : ℝ)) ^ 2 := by
    unfold activeDisplacementIntegrand
    split
    · have hsquare := (sq_le_sq₀ (norm_nonneg _) hrightNonneg).2
        (norm_stoppedPointDisplacement_le attempt k omega ‹k < K›)
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hsquare
    · simpa only [norm_zero] using sq_nonneg
        (displacementFactor h params.delta * (params.delta : ℝ))
  exact Integrable.mono' (integrable_const _)
    (measurable_activeDisplacementIntegrand attempt k).aestronglyMeasurable
    (ae_of_all P hbound)

/-- Helper for Corollary 4.2: the localized update bound of a finite stopped
state is controlled by the preceding raw error and corrected displacement. -/
theorem localizedUpdateConditionalBound_state_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hkpos : 0 < k) (omega : Ω) :
    localizedUpdateConditionalBound h oracle params b X
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega) ≤
      activeRawGradientErrorIntegrand attempt (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementIntegrand attempt (k - 1) omega := by
  have hkPrev : k - 1 < K := by omega
  by_cases hactive : StoppedAttempt.activeAt attempt k omega
  · obtain ⟨a, ha⟩ :=
      (StoppedAttempt.activeAt_iff_state attempt k omega
        (Nat.le_of_lt hk)).mp hactive
    have hprevActive := activeAt_of_le attempt omega (k - 1) k
      (Nat.sub_le k 1) (Nat.le_of_lt hk) hactive
    obtain ⟨aPrev, hPrevState⟩ :=
      (StoppedAttempt.activeAt_iff_state attempt (k - 1) omega
        (Nat.le_of_lt hkPrev)).mp hprevActive
    have hrawPrev := activeRawGradientErrorIntegrand_eq_rawEstimate
      attempt (k - 1) omega hkPrev aPrev hPrevState
    have hstored := StoppedAttempt.activeState_rawEstimate_eq_rawEstimate
      attempt k omega (Nat.le_of_lt hk) a ha
    have hpointPrev := StoppedAttempt.activeState_previous_eq_point
      attempt k omega (Nat.le_of_lt hk) a ha
    have hpointCurrent := StoppedAttempt.activeState_current_eq_point
      attempt k omega (Nat.le_of_lt hk) a ha
    have hkne : k ≠ 0 := Nat.ne_of_gt hkpos
    have hpredSucc : k - 1 + 1 = k := by omega
    rw [ha, localizedUpdateConditionalBound_apply]
    dsimp
    rw [hstored, if_neg hkne, hpointPrev, hpointCurrent]
    rw [hrawPrev, activeDisplacementIntegrand, dif_pos hkPrev, hpredSucc]
  · have hrightNonneg :
        0 ≤ activeRawGradientErrorIntegrand attempt (k - 1) omega +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activeDisplacementIntegrand attempt (k - 1) omega := by
      exact add_nonneg
        (activeRawGradientErrorIntegrand_nonneg attempt (k - 1) omega)
        (mul_nonneg (by positivity)
          (activeDisplacementIntegrand_nonneg attempt (k - 1) omega))
    rw [StoppedAttempt.activeAt_iff_state attempt k omega
      (Nat.le_of_lt hk)] at hactive
    cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega with
    | inl inactive =>
        rw [localizedUpdateConditionalBound_apply]
        exact hrightNonneg
    | inr active =>
        exact (hactive ⟨active, hstate⟩).elim

/-- Helper for Corollary 4.2: the finite localized conditional update bound is
integrable after composing it with the stopped state. -/
theorem integrable_localizedUpdateConditionalBound_comp
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hkpos : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand attempt (k - 1)) P) :
    Integrable (fun omega ↦
      localizedUpdateConditionalBound h oracle params b X
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)) P := by
  have hstateMeasurable : Measurable
      (fun omega ↦ localizedUpdateConditionalBound h oracle params b X
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)) :=
    (measurable_localizedUpdateConditionalBound h oracle params b X).comp
      (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩)
  have hdisplacement := integrable_activeDisplacementIntegrand
    attempt (k - 1)
  have hscaled : Integrable (fun omega ↦
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        activeDisplacementIntegrand attempt (k - 1) omega) P :=
    hdisplacement.const_mul
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
  have hmajorant : Integrable (fun omega ↦
      activeRawGradientErrorIntegrand attempt (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementIntegrand attempt (k - 1) omega) P :=
    hprevious.add hscaled
  refine Integrable.mono_nonneg hmajorant
    hstateMeasurable.aestronglyMeasurable ?_ ?_
  · exact Filter.Eventually.of_forall fun omega ↦
      localizedUpdateConditionalBound_nonneg
        (oracle := oracle)
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)
  · exact Filter.Eventually.of_forall fun omega ↦
      localizedUpdateConditionalBound_state_le attempt k hk hkpos omega

/-- Helper for Corollary 4.2: integrating the finite localized update bound is
controlled by the preceding raw-error and displacement moments. -/
theorem integral_localizedUpdateConditionalBound_map_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hkpos : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand attempt (k - 1)) P) :
    (∫ s, localizedUpdateConditionalBound h oracle params b X s ∂P.map
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)) ≤
      activeRawGradientErrorMeanSquare attempt (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P := by
  have hstate : AEMeasurable
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) P :=
    (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).aemeasurable
  have hcomp := integrable_localizedUpdateConditionalBound_comp
    attempt k hk hkpos hprevious
  have hdisplacement := integrable_activeDisplacementIntegrand
    attempt (k - 1)
  have hscaled : Integrable (fun omega ↦
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        activeDisplacementIntegrand attempt (k - 1) omega) P :=
    hdisplacement.const_mul
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
  have hmajorant : Integrable (fun omega ↦
      activeRawGradientErrorIntegrand attempt (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementIntegrand attempt (k - 1) omega) P :=
    hprevious.add hscaled
  calc
    (∫ s, localizedUpdateConditionalBound h oracle params b X s ∂P.map
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)) =
        ∫ omega, localizedUpdateConditionalBound h oracle params b X
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega) ∂P :=
      integral_map hstate
        ((measurable_localizedUpdateConditionalBound h oracle params b X).aestronglyMeasurable :
          AEStronglyMeasurable (localizedUpdateConditionalBound h oracle params b X)
            (P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)))
    _ ≤ ∫ omega,
        (activeRawGradientErrorIntegrand attempt (k - 1) omega +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activeDisplacementIntegrand attempt (k - 1) omega) ∂P :=
      integral_mono hcomp hmajorant fun omega ↦
        localizedUpdateConditionalBound_state_le attempt k hk hkpos omega
    _ = activeRawGradientErrorMeanSquare attempt (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P := by
      rw [integral_add hprevious hscaled, integral_const_mul,
        activeRawGradientErrorMeanSquare]

/-- Helper for Corollary 4.2: a finite nonrefresh step adds at most one
mean-square-Lipschitz displacement innovation to the preceding active error. -/
theorem activeRawGradientError_update
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hupdate : k % Q ≠ 0)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand attempt (k - 1)) P) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        activeRawGradientErrorMeanSquare attempt (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P := by
  classical
  have hkpos : 0 < k :=
    Nat.pos_of_ne_zero fun hkZero ↦ hupdate (by simp only [hkZero, Nat.zero_mod])
  have hbatchIndependent : ProbabilityTheory.iIndepFun (attempt.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using attempt.independent_sample.precomp hinjective
  have hsection : ∀ s : LocalizedPreBatchState h params X,
      Integrable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) (P.map (attempt.batch k)) := by
    intro s
    have hsectionMeasurable : Measurable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) :=
      (measurable_localizedRawGradientErrorObservable
        h oracle params Q B b X k).comp
          (measurable_const.prodMk measurable_id)
    cases s with
    | inl inactive =>
        simpa only [localizedRawGradientErrorObservable_apply] using
          (integrable_const (μ := P.map (attempt.batch k)) (0 : ℝ))
    | inr active =>
        have hcurrent : active.1.1 ∈ h.region :=
          attempt.region_condition.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed :=
          StochasticRun.EstimatorProbability.fixedPointUpdateBatchMeanSquare_le
            (oracle := oracle) active.1.1 hcurrent active.1.2.1
            active.previous_mem_region
            (active.1.2.2.2 - gradient f active.1.2.1)
            (attempt.sample k) b (attempt.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        refine (integrable_map_measure
          hsectionMeasurable.aestronglyMeasurable
          (StoppedAttempt.measurable_batch attempt k).aemeasurable).2 ?_
        refine hfixed.1.congr (Filter.Eventually.of_forall fun omega ↦ ?_)
        change _ = localizedRawGradientErrorObservable h oracle params Q B b X k
          (Sum.inr active, fun i ↦ attempt.sample k i omega)
        rw [localizedRawGradientErrorObservable_of_update active _ k hupdate,
          hgradient]
  have hbound : ∀ s : LocalizedPreBatchState h params X,
      (∫ batch, localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch) ∂P.map (attempt.batch k)) ≤
        localizedUpdateConditionalBound h oracle params b X s := by
    intro s
    have hsectionMeasurable : Measurable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) :=
      (measurable_localizedRawGradientErrorObservable
        h oracle params Q B b X k).comp
          (measurable_const.prodMk measurable_id)
    cases s with
    | inl inactive =>
        simp only [localizedRawGradientErrorObservable_apply,
          localizedUpdateConditionalBound_apply, integral_zero]
        exact le_rfl
    | inr active =>
        have hcurrent : active.1.1 ∈ h.region :=
          attempt.region_condition.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed :=
          StochasticRun.EstimatorProbability.fixedPointUpdateBatchMeanSquare_le
            (oracle := oracle) active.1.1 hcurrent active.1.2.1
            active.previous_mem_region
            (active.1.2.2.2 - gradient f active.1.2.1)
            (attempt.sample k) b (attempt.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        rw [integral_map (StoppedAttempt.measurable_batch attempt k).aemeasurable
          hsectionMeasurable.aestronglyMeasurable,
          localizedUpdateConditionalBound_apply]
        rw [integral_congr_ae (Filter.Eventually.of_forall fun omega ↦
          localizedRawGradientErrorObservable_of_update active
            (attempt.batch k omega) k hupdate), hgradient]
        exact hfixed.2
  have hCcomp := integrable_localizedUpdateConditionalBound_comp
    attempt k hk hkpos hprevious
  have hCmap : Integrable (localizedUpdateConditionalBound h oracle params b X)
      (P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)) :=
    (integrable_map_measure (μ := P)
      (measurable_localizedUpdateConditionalBound h oracle params b X).aestronglyMeasurable
      (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).aemeasurable).mpr hCcomp
  have hbridge := activeRawGradientErrorMeanSquare_le_of_sectionBounds
    attempt k hk (localizedUpdateConditionalBound h oracle params b X)
    hsection hCmap hbound
  exact ⟨hbridge.1, hbridge.2.trans
    (integral_localizedUpdateConditionalBound_map_le
      attempt k hk hkpos hprevious)⟩

/-- Helper for Corollary 4.2: the finite active raw SPIDER error accumulates
only displacement innovations since its most recent refresh index. -/
theorem activeRawGradientError_le_lastRefresh
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              ∫ omega, activeDisplacementIntegrand attempt j omega ∂P := by
  classical
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hrefresh : k % Q = 0
      · have hone := activeRawGradientError_refresh attempt k
          hk hrefresh
        refine ⟨hone.1, ?_⟩
        simpa only [hrefresh, Nat.sub_zero, Finset.Ico_self,
          Finset.sum_empty, mul_zero, add_zero] using hone.2
      · have hkPositive : 0 < k :=
          Nat.pos_of_ne_zero fun hkZero ↦
            hrefresh (by simp only [hkZero, Nat.zero_mod])
        have hkPredSucc : k - 1 + 1 = k := by omega
        have hprevious := ih (k - 1) (by omega) (by omega)
        have hone := activeRawGradientError_update attempt k hk hrefresh hprevious.1
        refine ⟨hone.1, ?_⟩
        have hQGtOne : 1 < (Q : ℕ) := by
          have hQPositive : 0 < (Q : ℕ) := Q.pos
          by_contra hnot
          have hQeq : (Q : ℕ) = 1 := by omega
          exact hrefresh (by rw [hQeq, Nat.mod_one])
        have hmodSucc :
            k % Q = ((k - 1) % Q + 1) % Q := by
          conv_lhs => rw [← hkPredSucc]
          rw [Nat.add_mod, Nat.mod_eq_of_lt hQGtOne]
        have hpreviousRemainderSucc : (k - 1) % Q + 1 < Q := by
          have hpreviousModLt : (k - 1) % Q < Q := Nat.mod_lt (k - 1) Q.pos
          by_contra hnot
          have heq : (k - 1) % Q + 1 = Q := by omega
          apply hrefresh
          rw [hmodSucc, heq, Nat.mod_self]
        have hkModSucc : k % Q = (k - 1) % Q + 1 := by
          rw [hmodSucc, Nat.mod_eq_of_lt hpreviousRemainderSucc]
        have hblockStart : k - k % Q = (k - 1) - (k - 1) % Q := by
          omega
        have hstart_le : k - k % Q ≤ k - 1 := by
          have hkModPositive : 0 < k % Q := Nat.pos_of_ne_zero hrefresh
          omega
        have hblockSum :
            (∑ j ∈ Finset.Ico (k - k % Q) k,
                ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) =
              (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) +
                ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P := by
          calc
            (∑ j ∈ Finset.Ico (k - k % Q) k,
                ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) =
                ∑ j ∈ Finset.Ico (k - k % Q) ((k - 1) + 1),
                  ∫ omega, activeDisplacementIntegrand attempt j omega ∂P := by
                    rw [hkPredSucc]
            _ = (∑ j ∈ Finset.Ico (k - k % Q) (k - 1),
                  ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) +
                ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P :=
              Finset.sum_Ico_succ_top hstart_le _
            _ = (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) +
                ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P := by
              rw [hblockStart]
        calc
          activeRawGradientErrorMeanSquare attempt k ≤
              activeRawGradientErrorMeanSquare attempt (k - 1) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P :=
            hone.2
          _ ≤ ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                    ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                ∫ omega, activeDisplacementIntegrand attempt (k - 1) omega ∂P := by
            exact add_le_add hprevious.2 le_rfl
          _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico (k - k % Q) k,
                    ∫ omega, activeDisplacementIntegrand attempt j omega ∂P := by
            rw [hblockSum]
            ring

/-- Helper for Corollary 4.2: stopped estimator-error energy as a finite sum of
active integrals. -/
noncomputable def stoppedGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : ℝ :=
  ∑ k ∈ Finset.range K, ∫ ω, activeGradientErrorIntegrand attempt k ω ∂P

/-- Helper for Corollary 4.2: stopped base-step energy as a finite sum of active
integrals. -/
noncomputable def stoppedBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : ℝ :=
  ∑ k ∈ Finset.range K, ∫ ω, activeBaseStepIntegrand attempt k ω ∂P

/-- Helper for Corollary 4.2: stopped displacement energy as a finite sum of
active integrals. -/
noncomputable def stoppedDisplacementEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) : ℝ :=
  ∑ k ∈ Finset.range K, ∫ ω, activeDisplacementIntegrand attempt k ω ∂P

/-- Helper for Corollary 4.2: stopped clipped-gradient error energy is
nonnegative. -/
theorem stoppedGradientErrorEnergy_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    0 ≤ stoppedGradientErrorEnergy attempt := by
  unfold stoppedGradientErrorEnergy
  exact Finset.sum_nonneg fun k _hk ↦
    integral_nonneg fun omega ↦ activeGradientErrorIntegrand_nonneg attempt k omega

/-- Helper for Corollary 4.2: stopped base-step energy is nonnegative. -/
theorem stoppedBaseStepEnergy_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    0 ≤ stoppedBaseStepEnergy attempt := by
  unfold stoppedBaseStepEnergy
  exact Finset.sum_nonneg fun k _hk ↦
    integral_nonneg fun omega ↦ activeBaseStepIntegrand_nonneg attempt k omega

/-- Helper for Corollary 4.2: stopped corrected-displacement energy is
nonnegative. -/
theorem stoppedDisplacementEnergy_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    0 ≤ stoppedDisplacementEnergy attempt := by
  unfold stoppedDisplacementEnergy
  exact Finset.sum_nonneg fun k _hk ↦
    integral_nonneg fun omega ↦ activeDisplacementIntegrand_nonneg attempt k omega

/-- Helper for Corollary 4.2: the finite output-record type used by one stopped
attempt together with its independent uniform selector. -/
abbrev stoppedAttemptOutputRecordType
    (Ξ : Type u) (n m K : ℕ) :=
  ℕ × stoppedAttemptFiniteObservableType Ξ n m K

/-- Helper for Corollary 4.2: the finite output records whose selector is in the
uniform support and whose stopped attempt succeeds. -/
def successfulOutputRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) :
    Set (stoppedAttemptOutputRecordType Ξ n m K) :=
  {z | z.1 ∈ Finset.Icc 1 (K - 1) ∧
    z.2 ∈ successRecord (Ξ := Ξ) (n := n) (m := m) K X}

omit [MeasurableSpace Ξ] in
/-- Helper for Corollary 4.2: membership in the successful output-record set
means selector support together with finite stopped success. -/
theorem mem_successfulOutputRecord_iff
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (z : stoppedAttemptOutputRecordType Ξ n m K) :
    z ∈ successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X ↔
      z.1 ∈ Finset.Icc 1 (K - 1) ∧
        z.2 ∈ successRecord (Ξ := Ξ) (n := n) (m := m) K X := by
  rfl

/-- Helper for Corollary 4.2: the successful finite output-record set is
measurable. -/
theorem measurableSet_successfulOutputRecord
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    MeasurableSet
      (successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X) := by
  unfold successfulOutputRecord
  exact ((Finset.Icc 1 (K - 1)).measurableSet.preimage measurable_fst).inter
    ((measurableSet_successRecord (Ξ := Ξ) (n := n) (m := m) K X hX).preimage
      measurable_snd)

/-- Helper for Corollary 4.2: the product law of a uniform output selector and
the finite stopped-attempt observable. -/
noncomputable def stoppedAttemptOutputMeasure
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 2 ≤ K) :
    Measure (stoppedAttemptOutputRecordType Ξ n m K) :=
  (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure.prod
    (P.map (stoppedAttemptFiniteObservable attempt))

/-- Helper for Corollary 4.2: the stopped output-record law is the selector law
times the mapped finite-attempt law. -/
theorem stoppedAttemptOutputMeasure_def
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 2 ≤ K) :
    stoppedAttemptOutputMeasure attempt hK =
      (LALM.StochasticRun.UniformOutput.indexLaw K hK).toMeasure.prod
        (P.map (stoppedAttemptFiniteObservable attempt)) := by
  rfl

/-- Helper for Corollary 4.2: the squared KKT residual observed at a finite
uniform-output record.  The residual is written through the regularity-region
extension; on a successful record this equals the raw KKT residual. -/
noncomputable def outputResidualIntegrand
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : stoppedAttemptOutputRecordType Ξ n m K) : ℝ≥0∞ :=
  (successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X).indicator
    (fun output ↦ ENNReal.ofReal
      (KKT.residualExtension h
        (output.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1)),
          output.2.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1))) ^ 2)) output

omit [MeasurableSpace Ξ] in
/-- Helper for Corollary 4.2: expose the successful-record residual integrand
without unfolding its owner definition downstream. -/
theorem outputResidualIntegrand_def
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (output : stoppedAttemptOutputRecordType Ξ n m K) :
    outputResidualIntegrand (h := h) K X output =
      (successfulOutputRecord (Ξ := Ξ) (n := n) (m := m) K X).indicator
        (fun output ↦ ENNReal.ofReal
          (KKT.residualExtension h
            (output.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1)),
              output.2.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1))) ^ 2)) output := by
  rfl

/-- Helper for Corollary 4.2: the successful-record residual integrand is
measurable whenever the finite localization set is measurable. -/
theorem measurable_outputResidualIntegrand
    (K : ℕ) (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X) :
    Measurable (outputResidualIntegrand (Ξ := Ξ) (m := m) (h := h) K X) := by
  let pointProjection :
      stoppedAttemptFiniteObservableType Ξ n m K →
        (Fin (K + 1) → EuclideanSpace ℝ (Fin n)) :=
    fun output ↦ output.2.1
  have hpointProjection : Measurable pointProjection :=
    measurable_fst.comp measurable_snd
  let pointAt : ℕ → stoppedAttemptFiniteObservableType Ξ n m K →
      EuclideanSpace ℝ (Fin n) :=
    fun k output ↦ pointProjection output (Fin.ofNat (K + 1) (k + 1))
  have hpointAt (k : ℕ) : Measurable (pointAt k) :=
    (measurable_pi_apply (Fin.ofNat (K + 1) (k + 1))).comp hpointProjection
  have hpoint : Measurable
      (fun output : stoppedAttemptOutputRecordType Ξ n m K ↦
        output.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1))) := by
    simpa only [pointAt, pointProjection] using
      measurable_from_prod_countable_right hpointAt
  let multiplierProjection :
      stoppedAttemptFiniteObservableType Ξ n m K →
        (Fin (K + 1) → EuclideanSpace ℝ (Fin m)) :=
    fun output ↦ output.2.2.1
  have hmultiplierProjection : Measurable multiplierProjection :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  let multiplierAt : ℕ → stoppedAttemptFiniteObservableType Ξ n m K →
      EuclideanSpace ℝ (Fin m) :=
    fun k output ↦ multiplierProjection output (Fin.ofNat (K + 1) (k + 1))
  have hmultiplierAt (k : ℕ) : Measurable (multiplierAt k) :=
    (measurable_pi_apply (Fin.ofNat (K + 1) (k + 1))).comp
      hmultiplierProjection
  have hmultiplier : Measurable
      (fun output : stoppedAttemptOutputRecordType Ξ n m K ↦
        output.2.2.2.1 (Fin.ofNat (K + 1) (output.1 + 1))) := by
    simpa only [multiplierAt, multiplierProjection] using
      measurable_from_prod_countable_right hmultiplierAt
  have hresidual :=
    (KKT.measurable_residualExtension h).comp (hpoint.prodMk hmultiplier)
  unfold outputResidualIntegrand
  exact (hresidual.pow_const 2).ennreal_ofReal.indicator
    (measurableSet_successfulOutputRecord K X hX)

/-- Helper for Corollary 4.2: the residual numerator restricted to a stopped
attempt's finite success event. -/
noncomputable def successRestrictedResidualNumerator
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
  (hK : 2 ≤ K) : ℝ≥0∞ :=
  ∫⁻ output, outputResidualIntegrand (h := h) K X output
    ∂stoppedAttemptOutputMeasure attempt hK

/-- Helper for Corollary 4.2: expose the product-law definition of the
success-restricted residual numerator. -/
theorem successRestrictedResidualNumerator_def
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 2 ≤ K) :
    successRestrictedResidualNumerator attempt hK =
      ∫⁻ output, outputResidualIntegrand (h := h) K X output
        ∂stoppedAttemptOutputMeasure attempt hK := by
  rfl

/-- Corollary 4.2: a stopped attempt certificate records the substantive
finite-horizon success-probability and success-restricted residual estimates.
Measurability, integrability, and nonnegativity of its bounded energy
observables are derived from the stopped attempt itself. -/
structure StoppedAttemptCertificate
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 2 ≤ K) where
  /-- The finite success event has the certified probability lower bound. -/
  successProbability_lower :
    ENNReal.ofReal (1 - confidence) ≤ P (successEvent attempt)
  /-- The finite nonnegative residual scale used by the aggregate
  success-restricted estimate. This is not a pointwise bound by itself. -/
  residualPerSuccessBound : ℝ≥0
  /-- The finite success-restricted residual numerator is bounded by the
  success probability times the declared residual scale. -/
  successRestrictedResidual_le :
    successRestrictedResidualNumerator attempt hK ≤
      P (successEvent attempt) * (residualPerSuccessBound : ℝ≥0∞)

/-- Helper for Corollary 4.2: a certificate's nonnegative-real residual bound
is finite when embedded into `ℝ≥0∞`. -/
theorem residualPerSuccessBound_ne_top
    (certificate : StoppedAttemptCertificate attempt hK) :
    (certificate.residualPerSuccessBound : ℝ≥0∞) ≠ ⊤ := by
  exact ENNReal.coe_ne_top

/-- Corollary 4.2: the finite certificate supplies the stopped-attempt survival
probability lower bound. -/
lemma survivalProbability_ge
    (certificate : StoppedAttemptCertificate attempt hK) :
    ENNReal.ofReal (1 - confidence) ≤ P (successEvent attempt) :=
  certificate.successProbability_lower

/-- Helper for Corollary 4.2: the finite certificate supplies its
success-restricted residual numerator bound. -/
lemma restrictedResidual_le
    (certificate : StoppedAttemptCertificate attempt hK) :
    successRestrictedResidualNumerator attempt hK ≤
      P (successEvent attempt) *
        (certificate.residualPerSuccessBound : ℝ≥0∞) :=
  certificate.successRestrictedResidual_le

/-- Helper for Corollary 4.2: the finite certificate supplies the residual bound
under its more descriptive success-restricted name. -/
lemma successRestrictedResidualNumerator_le
    (certificate : StoppedAttemptCertificate attempt hK) :
    successRestrictedResidualNumerator attempt hK ≤
      P (successEvent attempt) *
        (certificate.residualPerSuccessBound : ℝ≥0∞) :=
  certificate.successRestrictedResidual_le

end StoppedAttemptAnalysis

end LALM.Correction

end
