/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergyRecursion
public import TR_LALM_theory.Corollary_4_2.StochasticEstimatorProbability
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergyRecursion

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.FiniteStopped.StoppedAttemptAnalysis

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
variable {params : LALM.Parameters h x₀ multiplier₀}
variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Helper for Theorem 3.7: the raw SPIDER error as a measurable function of a
finite pre-batch state and its fresh sample row. The inactive branch is zero. -/
noncomputable def finiteRawGradientErrorObservable
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ)
    (z : PreBatchState n m × (ℕ → Ξ)) : ℝ :=
  if z.1.1 = 1 then
    ‖rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1 z.1.2.2.2.2 z.2 -
      h.objectiveGradientExtension z.1.2.1‖ ^ 2
  else 0

/-- Helper for Theorem 3.7: the finite state/batch raw-error observable is
measurable before it is integrated against the stopped attempt law. -/
theorem measurable_finiteRawGradientErrorObservable
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) :
    Measurable (finiteRawGradientErrorObservable h oracle Q B b k) := by
  have hflag : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦ z.1.1) := by
    fun_prop
  have hpoint : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦ z.1.2.1) := by
    fun_prop
  have hraw : Measurable (fun z : PreBatchState n m × (ℕ → Ξ) ↦
      rawEstimateAt oracle Q B b k z.1.2.1 z.1.2.2.1 z.1.2.2.2.2 z.2) :=
    measurable_rawEstimateAt oracle Q B b k
  unfold finiteRawGradientErrorObservable
  apply Measurable.ite
  · exact measurableSet_eq_fun hflag measurable_const
  · exact ((hraw.sub (h.measurable_objectiveGradientExtension.comp hpoint)).norm.pow_const 2)
  · exact measurable_const

/-- Helper for Theorem 3.7: an independent stopped state and fresh sample row
transfer statewise raw-error bounds to the actual finite observable. -/
theorem activeRawGradientErrorMeanSquare_le_of_statewiseBounds
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K)
    (C : PreBatchState n m → ℝ)
    (hsection : ∀ᵐ s ∂P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩),
      Integrable (fun batch ↦ finiteRawGradientErrorObservable h oracle Q B b k
        (s, batch)) (P.map (attempt.batch k)))
    (hC : Integrable C
      (P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)))
    (hbound : ∀ᵐ s ∂P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩),
      (∫ batch, finiteRawGradientErrorObservable h oracle Q B b k
        (s, batch) ∂P.map (attempt.batch k)) ≤ C s) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        ∫ s, C s ∂P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) := by
  have hstate : AEMeasurable
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) P :=
    (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).aemeasurable
  have hbatch : AEMeasurable (attempt.batch k) P :=
    (attempt.measurable_batch k).aemeasurable
  have hindependent : ProbabilityTheory.IndepFun
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) (attempt.batch k) P := by
    have hbatch_eq : attempt.batch k = (fun omega i ↦ attempt.sample k i omega) := by
      funext omega i
      rfl
    rw [hbatch_eq]
    simpa only [Fin.castSucc_mk] using
      attempt.independent_state_sample ⟨k, hk⟩
  have hnonnegative : ∀ z : PreBatchState n m × (ℕ → Ξ),
      0 ≤ finiteRawGradientErrorObservable h oracle Q B b k z := by
    intro z
    unfold finiteRawGradientErrorObservable
    split
    · exact sq_nonneg _
    · exact le_rfl
  have hpair :=
    LALM.Correction.StochasticRun.EstimatorProbability.independentPair_integrable_integral_le
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) (attempt.batch k)
      (finiteRawGradientErrorObservable h oracle Q B b k) C hindependent hstate hbatch
      (measurable_finiteRawGradientErrorObservable h oracle Q B b k).aemeasurable
      hnonnegative hsection hC hbound
  have hidentify : (fun omega ↦
      finiteRawGradientErrorObservable h oracle Q B b k
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega, attempt.batch k omega)) =ᵐ[P]
      activeRawGradientErrorIntegrand attempt k := by
    exact Filter.Eventually.of_forall fun omega ↦ by
      simp only [finiteRawGradientErrorObservable, activeRawGradientErrorIntegrand,
        dif_pos hk, StoppedAttempt.activeAt, StoppedAttempt.point]
  refine ⟨hpair.1.congr hidentify, ?_⟩
  rw [activeRawGradientErrorMeanSquare, ← integral_congr_ae hidentify]
  exact hpair.2

/-- Theorem 3.7: an active refresh batch has raw-error mean square bounded by
the oracle variance divided by its positive batch size. -/
theorem activeRawGradientError_refresh
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hrefresh : k % Q = 0) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
  classical
  let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
  have hstate : AEMeasurable (attempt.state kfin) P :=
    (attempt.measurable_state kfin).aemeasurable
  have hbatch : AEMeasurable (attempt.batch k) P :=
    (attempt.measurable_batch k).aemeasurable
  have hbatchIndependent : ProbabilityTheory.iIndepFun (attempt.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using attempt.independent_sample.precomp hinjective
  have hpredicate : MeasurableSet {s : PreBatchState n m |
      s.1 = 1 → s.2.1 ∈ h.region} := by
    have hset : {s : PreBatchState n m | s.1 = 1 → s.2.1 ∈ h.region} =
        {s : PreBatchState n m | s.1 ≠ 1} ∪
          {s : PreBatchState n m | s.2.1 ∈ h.region} := by
      ext s
      by_cases hs : s.1 = 1 <;> simp [hs]
    rw [hset]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl.union
      (h.isOpen_region.measurableSet.preimage (by fun_prop))
  have hvalid : ∀ᵐ s ∂P.map (attempt.state kfin),
      s.1 = 1 → s.2.1 ∈ h.region := by
    apply (ae_map_iff hstate hpredicate).2
    exact Filter.Eventually.of_forall fun omega hactive ↦ by
      have hactive' : attempt.activeAt kfin omega := by
        simpa only [StoppedAttempt.activeAt, kfin] using hactive
      simpa only [StoppedAttempt.point] using
        (point_mem_region_of_active attempt kfin omega hactive')
  have hsection : ∀ᵐ s ∂P.map (attempt.state kfin),
      Integrable (fun batch ↦ finiteRawGradientErrorObservable h oracle Q B b k
        (s, batch)) (P.map (attempt.batch k)) := by
    filter_upwards [hvalid] with s hsvalid
    by_cases hs : s.1 = 1
    · have hx : s.2.1 ∈ h.region := hsvalid hs
      have hfixed :=
        LALM.Correction.StochasticRun.EstimatorProbability.fixedPointRefreshBatchMeanSquare_le
          (oracle := oracle) s.2.1 hx (attempt.sample k) B
          (fun i ↦ attempt.hasLaw_sample k i) hbatchIndependent
      have hsectionMeasurable : Measurable (fun batch ↦
          finiteRawGradientErrorObservable h oracle Q B b k (s, batch)) :=
        (measurable_finiteRawGradientErrorObservable h oracle Q B b k).comp
          (measurable_const.prodMk measurable_id)
      have hobs (batch : ℕ → Ξ) :
          finiteRawGradientErrorObservable h oracle Q B b k (s, batch) =
            ‖(B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
                (oracle.sampleGradient s.2.1 (batch i) - gradient f s.2.1)‖ ^ 2 := by
        rw [finiteRawGradientErrorObservable, if_pos hs,
          rawEstimateAt_of_refresh oracle Q B b k s.2.1 s.2.2.1 s.2.2.2.2
            batch hrefresh, h.objectiveGradientExtension_eq hx]
        rw [← LALM.Correction.StochasticRun.EstimatorProbability.batchAverage_sub]
      refine (integrable_map_measure hsectionMeasurable.aestronglyMeasurable hbatch).2 ?_
      exact hfixed.1.congr (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [Function.comp_apply, StoppedAttempt.batch] using
          (hobs (attempt.batch k omega)).symm)
    · simpa only [finiteRawGradientErrorObservable, if_neg hs] using
        (integrable_const (μ := P.map (attempt.batch k)) (0 : ℝ))
  have hbound : ∀ᵐ s ∂P.map (attempt.state kfin),
      (∫ batch, finiteRawGradientErrorObservable h oracle Q B b k
        (s, batch) ∂P.map (attempt.batch k)) ≤
          (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
    filter_upwards [hvalid] with s hsvalid
    by_cases hs : s.1 = 1
    · have hx : s.2.1 ∈ h.region := hsvalid hs
      have hfixed :=
        LALM.Correction.StochasticRun.EstimatorProbability.fixedPointRefreshBatchMeanSquare_le
          (oracle := oracle) s.2.1 hx (attempt.sample k) B
          (fun i ↦ attempt.hasLaw_sample k i) hbatchIndependent
      have hsectionMeasurable : Measurable (fun batch ↦
          finiteRawGradientErrorObservable h oracle Q B b k (s, batch)) :=
        (measurable_finiteRawGradientErrorObservable h oracle Q B b k).comp
          (measurable_const.prodMk measurable_id)
      have hobs (batch : ℕ → Ξ) :
          finiteRawGradientErrorObservable h oracle Q B b k (s, batch) =
            ‖(B : ℝ)⁻¹ • ∑ i ∈ Finset.range B,
                (oracle.sampleGradient s.2.1 (batch i) - gradient f s.2.1)‖ ^ 2 := by
        rw [finiteRawGradientErrorObservable, if_pos hs,
          rawEstimateAt_of_refresh oracle Q B b k s.2.1 s.2.2.1 s.2.2.2.2
            batch hrefresh, h.objectiveGradientExtension_eq hx]
        rw [← LALM.Correction.StochasticRun.EstimatorProbability.batchAverage_sub]
      rw [integral_map hbatch hsectionMeasurable.aestronglyMeasurable]
      rw [integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ by
        simpa only [Function.comp_apply, StoppedAttempt.batch] using
          hobs (attempt.batch k omega))]
      exact hfixed.2
    · simp only [finiteRawGradientErrorObservable, if_neg hs, integral_zero]
      positivity
  have hbridge := activeRawGradientErrorMeanSquare_le_of_statewiseBounds
    attempt k hk (fun _ ↦ (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ))
      hsection (integrable_const _) hbound
  refine ⟨hbridge.1, hbridge.2.trans_eq ?_⟩
  rw [integral_const, Measure.real,
    Measure.map_apply_of_aemeasurable hstate MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, ENNReal.toReal_one, one_smul]

/-- Helper for Theorem 3.7: the measurable statewise majorant used by a
nonrefresh SPIDER update. Its gradient term uses the globally measurable
extension and agrees with `gradient f` on the regularity region. -/
noncomputable def finiteUpdateConditionalBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (b : ℕ+) : PreBatchState n m → ℝ := fun s ↦
  if s.1 = 1 then
    ‖s.2.2.2.2 - h.objectiveGradientExtension s.2.2.1‖ ^ 2 +
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        ‖s.2.1 - s.2.2.1‖ ^ 2
  else 0

/-- Helper for Theorem 3.7: the statewise nonrefresh majorant is zero on an
inactive pre-batch state and has the displayed two-term form on an active one. -/
theorem finiteUpdateConditionalBound_of_active
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (b : ℕ+) (s : PreBatchState n m) (hs : s.1 = 1) :
    finiteUpdateConditionalBound h oracle b s =
      ‖s.2.2.2.2 - h.objectiveGradientExtension s.2.2.1‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖s.2.1 - s.2.2.1‖ ^ 2 := by
  simp only [finiteUpdateConditionalBound, if_pos hs]

/-- Helper for Theorem 3.7: the statewise nonrefresh majorant vanishes on an
inactive pre-batch state. -/
theorem finiteUpdateConditionalBound_of_inactive
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (b : ℕ+) (s : PreBatchState n m) (hs : s.1 ≠ 1) :
    finiteUpdateConditionalBound h oracle b s = 0 := by
  simp only [finiteUpdateConditionalBound, if_neg hs]

/-- Helper for Theorem 3.7: the statewise nonrefresh majorant is measurable. -/
theorem measurable_finiteUpdateConditionalBound
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (b : ℕ+) :
    Measurable (finiteUpdateConditionalBound h oracle b) := by
  have hflag : Measurable (fun s : PreBatchState n m ↦ s.1) := by
    fun_prop
  have hcurrent : Measurable (fun s : PreBatchState n m ↦ s.2.1) := by
    fun_prop
  have hprevious : Measurable (fun s : PreBatchState n m ↦ s.2.2.1) := by
    fun_prop
  have hraw : Measurable (fun s : PreBatchState n m ↦ s.2.2.2.2) := by
    fun_prop
  have hgradient : Measurable (fun s : PreBatchState n m ↦
      h.objectiveGradientExtension s.2.2.1) :=
    h.measurable_objectiveGradientExtension.comp hprevious
  have hactive : Measurable (fun s : PreBatchState n m ↦
      ‖s.2.2.2.2 - h.objectiveGradientExtension s.2.2.1‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖s.2.1 - s.2.2.1‖ ^ 2) :=
    ((hraw.sub hgradient).norm.pow_const 2).add
      (((hcurrent.sub hprevious).norm.pow_const 2).const_mul
        ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)))
  unfold finiteUpdateConditionalBound
  apply Measurable.ite
  · exact measurableSet_eq_fun hflag measurable_const
  · exact hactive
  · exact measurable_const

/-- Helper for Theorem 3.7: the statewise nonrefresh majorant is nonnegative. -/
theorem finiteUpdateConditionalBound_nonneg
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (b : ℕ+) (s : PreBatchState n m) :
    0 ≤ finiteUpdateConditionalBound h oracle b s := by
  by_cases hs : s.1 = 1
  · rw [finiteUpdateConditionalBound_of_active h oracle b s hs]
    positivity
  · rw [finiteUpdateConditionalBound_of_inactive h oracle b s hs]

/-- Helper for Theorem 3.7: on every positive in-horizon transition, the
statewise nonrefresh majorant is bounded by the preceding stopped raw error and
displacement observables. -/
theorem finiteUpdateConditionalBound_state_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hk : k < K) (hkpos : 0 < k) (omega : Ω) :
    finiteUpdateConditionalBound h oracle b
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega) ≤
      activeRawGradientErrorIntegrand attempt (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementIntegrand attempt (k - 1) omega := by
  let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
  by_cases hactive : attempt.activeAt kfin omega
  · let j : Fin K := ⟨k - 1, by omega⟩
    have hprev : attempt.activeAt j.castSucc omega := by
      have hprev' := attempt.activeAt_of_le omega (k - 1) k
        (Nat.sub_le k 1) (Nat.le_of_lt hk) hactive
      simpa only [j, Fin.castSucc_mk, kfin] using hprev'
    have hprevNat : attempt.activeAt
        ⟨k - 1, Nat.lt_succ_of_lt (by omega : k - 1 < K)⟩ omega := by
      simpa only [j, Fin.castSucc_mk] using hprev
    have hsucc : j.succ = kfin := by
      apply Fin.ext
      dsimp [j, kfin]
      omega
    have hstored := successor_rawEstimate_eq_of_active attempt j omega hprev
    have hstored' :
        (attempt.state kfin omega).2.2.2.2 =
          rawEstimateAt oracle Q B b (k - 1)
            (attempt.state j.castSucc omega).2.1
            (attempt.state j.castSucc omega).2.2.1
            (attempt.state j.castSucc omega).2.2.2.2
            (attempt.batch (k - 1) omega) := by
      simpa only [hsucc] using hstored
    have hpreviousField :
        (attempt.state kfin omega).2.2.1 =
          (attempt.state j.castSucc omega).2.1 := by
      simpa only [hsucc] using
        (successor_previousPoint_eq_of_active attempt j omega hprev)
    have hx := point_mem_region_of_active attempt kfin omega hactive
    have hy := point_mem_region_of_active attempt j.castSucc omega hprev
    have hy' : h.objectiveGradientExtension
          ((attempt.state j.castSucc omega).2.1) =
        gradient f ((attempt.state j.castSucc omega).2.1) := by
      simpa only [StoppedAttempt.point] using
        (h.objectiveGradientExtension_eq hy)
    have hyNat : h.objectiveGradientExtension
          (attempt.point ⟨k - 1, Nat.lt_succ_of_lt (by omega : k - 1 < K)⟩ omega) =
        gradient f (attempt.point ⟨k - 1,
          Nat.lt_succ_of_lt (by omega : k - 1 < K)⟩ omega) := by
      simpa only [j, Fin.castSucc_mk] using
        (h.objectiveGradientExtension_eq hy)
    have hactiveFlag :
        (attempt.state kfin omega).1 = 1 := by
      simpa only [StoppedAttempt.activeAt, kfin] using hactive
    have hpredSucc : k - 1 + 1 = k := by
      omega
    rw [finiteUpdateConditionalBound_of_active h oracle b _ hactiveFlag]
    rw [activeRawGradientErrorIntegrand, dif_pos (by omega),
      if_pos hprevNat]
    rw [activeDisplacementIntegrand, dif_pos (by omega)]
    rw [hpreviousField, hy', hyNat]
    simp only [StoppedAttempt.point]
    rw [hstored']
    simpa [j, kfin, hpredSucc]
  · have hright :
        0 ≤ activeRawGradientErrorIntegrand attempt (k - 1) omega +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activeDisplacementIntegrand attempt (k - 1) omega := by
      exact add_nonneg
        (activeRawGradientErrorIntegrand_nonneg attempt (k - 1) omega)
        (mul_nonneg (by positivity)
          (activeDisplacementIntegrand_nonneg attempt (k - 1) omega))
    have hflag :
        (attempt.state kfin omega).1 ≠ 1 := by
      simpa only [StoppedAttempt.activeAt, kfin] using hactive
    rw [finiteUpdateConditionalBound_of_inactive h oracle b _ hflag]
    exact hright

/-- Helper for Theorem 3.7: a prefix invariant makes the statewise
nonrefresh majorant integrable after composition with the actual stopped state. -/
theorem integrable_finiteUpdateConditionalBound_comp
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (k : ℕ) (hk : k < K) (hkpos : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand attempt (k - 1)) P) :
    Integrable (fun omega ↦ finiteUpdateConditionalBound h oracle b
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)) P := by
  have hstateMeasurable : Measurable (fun omega ↦
      finiteUpdateConditionalBound h oracle b
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)) :=
    (measurable_finiteUpdateConditionalBound h oracle b).comp
      (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩)
  have hdisplacement := integrable_activeDisplacementMeanSquare
    attempt invariant (k - 1)
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
      finiteUpdateConditionalBound_nonneg h oracle b
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega)
  · exact Filter.Eventually.of_forall fun omega ↦
      finiteUpdateConditionalBound_state_le attempt k hk hkpos omega

/-- Helper for Theorem 3.7: integrating the statewise nonrefresh majorant is
controlled by the preceding stopped raw-error and displacement moments. -/
theorem integral_finiteUpdateConditionalBound_map_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (k : ℕ) (hk : k < K) (hkpos : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand attempt (k - 1)) P) :
    (∫ s, finiteUpdateConditionalBound h oracle b s ∂P.map
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)) ≤
      activeRawGradientErrorMeanSquare attempt (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementMeanSquare attempt (k - 1) := by
  have hstate : AEMeasurable
      (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩) P :=
    (attempt.measurable_state ⟨k, Nat.lt_succ_of_lt hk⟩).aemeasurable
  have hcomp := integrable_finiteUpdateConditionalBound_comp
    attempt invariant k hk hkpos hprevious
  have hdisplacement := integrable_activeDisplacementMeanSquare
    attempt invariant (k - 1)
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
    (∫ s, finiteUpdateConditionalBound h oracle b s ∂P.map
        (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)) =
        ∫ omega, finiteUpdateConditionalBound h oracle b
          (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega) ∂P :=
      integral_map hstate
        ((measurable_finiteUpdateConditionalBound h oracle b).aestronglyMeasurable :
          AEStronglyMeasurable (finiteUpdateConditionalBound h oracle b)
            (P.map (attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩)))
    _ ≤ ∫ omega,
        (activeRawGradientErrorIntegrand attempt (k - 1) omega +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activeDisplacementIntegrand attempt (k - 1) omega) ∂P :=
      integral_mono hcomp hmajorant fun omega ↦
        finiteUpdateConditionalBound_state_le attempt k hk hkpos omega
    _ = activeRawGradientErrorMeanSquare attempt (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activeDisplacementMeanSquare attempt (k - 1) := by
      rw [integral_add hprevious hscaled, integral_const_mul,
        activeRawGradientErrorMeanSquare, activeDisplacementMeanSquare]

/-- Helper for Theorem 3.7: on an active nonrefresh state, the raw observable
is the preceding centered error plus the centered same-sample innovation. -/
theorem finiteRawGradientErrorObservable_of_update
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (Q B b : ℕ+) (k : ℕ) (s : PreBatchState n m) (batch : ℕ → Ξ)
    (hs : s.1 = 1) (hx : s.2.1 ∈ h.region)
    (hupdate : k % Q ≠ 0) :
    finiteRawGradientErrorObservable h oracle Q B b k (s, batch) =
      ‖(s.2.2.2.2 - gradient f s.2.2.1) +
        (b : ℝ)⁻¹ • ∑ i ∈ Finset.range b,
          ((oracle.sampleGradient s.2.1 (batch i) -
              oracle.sampleGradient s.2.2.1 (batch i)) -
            (gradient f s.2.1 - gradient f s.2.2.1))‖ ^ 2 := by
  rw [finiteRawGradientErrorObservable, if_pos hs,
    rawEstimateAt_of_not_refresh oracle Q B b k s.2.1 s.2.2.1 s.2.2.2.2
      batch hupdate, h.objectiveGradientExtension_eq hx]
  apply congrArg (fun z : EuclideanSpace ℝ (Fin n) ↦ ‖z‖ ^ 2)
  rw [LALM.Correction.StochasticRun.EstimatorProbability.batchAverage_sub]
  abel

/-- Helper for Theorem 3.7: at a fixed active state in the regularity region,
one independent nonrefresh batch is integrable and obeys the statewise update
majorant. -/
theorem finiteRawGradientErrorObservable_updateBatch_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (hupdate : k % Q ≠ 0)
    (hbatchIndependent : ProbabilityTheory.iIndepFun (attempt.sample k) P)
    (s : PreBatchState n m) (hs : s.1 = 1)
    (hx : s.2.1 ∈ h.region) (hy : s.2.2.1 ∈ h.region) :
    Integrable (fun batch ↦ finiteRawGradientErrorObservable h oracle Q B b k
        (s, batch)) (P.map (attempt.batch k)) ∧
      (∫ batch, finiteRawGradientErrorObservable h oracle Q B b k
          (s, batch) ∂P.map (attempt.batch k)) ≤
        finiteUpdateConditionalBound h oracle b s := by
  classical
  have hbatch : AEMeasurable (attempt.batch k) P :=
    (attempt.measurable_batch k).aemeasurable
  have hsectionMeasurable : Measurable (fun batch ↦
      finiteRawGradientErrorObservable h oracle Q B b k (s, batch)) :=
    (measurable_finiteRawGradientErrorObservable h oracle Q B b k).comp
      (measurable_const.prodMk measurable_id)
  have hfixed :=
    LALM.Correction.StochasticRun.EstimatorProbability.fixedPointUpdateBatchMeanSquare_le
      (oracle := oracle) s.2.1 hx s.2.2.1 hy
        (s.2.2.2.2 - gradient f s.2.2.1) (attempt.sample k) b
        (fun i ↦ attempt.hasLaw_sample k i) hbatchIndependent
  have hobs (batch : ℕ → Ξ) :=
    finiteRawGradientErrorObservable_of_update h oracle Q B b k s batch hs hx hupdate
  have hC : finiteUpdateConditionalBound h oracle b s =
      ‖s.2.2.2.2 - gradient f s.2.2.1‖ ^ 2 +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          ‖s.2.1 - s.2.2.1‖ ^ 2 := by
    rw [finiteUpdateConditionalBound_of_active h oracle b s hs,
      h.objectiveGradientExtension_eq hy]
  constructor
  · refine (integrable_map_measure
      hsectionMeasurable.aestronglyMeasurable hbatch).2 ?_
    exact hfixed.1.congr (Filter.Eventually.of_forall fun omega ↦ by
      simpa only [Function.comp_apply, StoppedAttempt.batch] using
        (hobs (attempt.batch k omega)).symm)
  · rw [hC]
    rw [integral_map hbatch hsectionMeasurable.aestronglyMeasurable]
    rw [integral_congr_ae (Filter.Eventually.of_forall fun omega ↦ by
      simpa only [Function.comp_apply, StoppedAttempt.batch] using
        hobs (attempt.batch k omega))]
    exact hfixed.2

/-- Theorem 3.7: a finite active nonrefresh step adds at most one
mean-square-Lipschitz displacement innovation to the preceding raw error. -/
theorem activeRawGradientError_update
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (k : ℕ) (hk : k < K) (hupdate : k % Q ≠ 0)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand attempt (k - 1)) P) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P ∧
      activeRawGradientErrorMeanSquare attempt k ≤
        activeRawGradientErrorMeanSquare attempt (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activeDisplacementMeanSquare attempt (k - 1) := by
  classical
  have hkpos : 0 < k :=
    Nat.pos_of_ne_zero fun hkZero ↦ hupdate (by simp only [hkZero, Nat.zero_mod])
  let kfin : Fin (K + 1) := ⟨k, Nat.lt_succ_of_lt hk⟩
  have hstate : AEMeasurable (attempt.state kfin) P :=
    (attempt.measurable_state kfin).aemeasurable
  have hbatchIndependent : ProbabilityTheory.iIndepFun (attempt.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using attempt.independent_sample.precomp hinjective
  have hcurrentPredicate : MeasurableSet {s : PreBatchState n m |
      s.1 = 1 → s.2.1 ∈ h.region} := by
    have hset : {s : PreBatchState n m | s.1 = 1 → s.2.1 ∈ h.region} =
        {s : PreBatchState n m | s.1 ≠ 1} ∪
          {s : PreBatchState n m | s.2.1 ∈ h.region} := by
      ext s
      by_cases hs : s.1 = 1 <;> simp [hs]
    rw [hset]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl.union
      (h.isOpen_region.measurableSet.preimage (by fun_prop))
  have hpreviousPredicate : MeasurableSet {s : PreBatchState n m |
      s.1 = 1 → s.2.2.1 ∈ h.region} := by
    have hset : {s : PreBatchState n m | s.1 = 1 → s.2.2.1 ∈ h.region} =
        {s : PreBatchState n m | s.1 ≠ 1} ∪
          {s : PreBatchState n m | s.2.2.1 ∈ h.region} := by
      ext s
      by_cases hs : s.1 = 1 <;> simp [hs]
    rw [hset]
    exact (measurableSet_eq_fun (by fun_prop) measurable_const).compl.union
      (h.isOpen_region.measurableSet.preimage (by fun_prop))
  have hvalidCurrent : ∀ᵐ s ∂P.map (attempt.state kfin),
      s.1 = 1 → s.2.1 ∈ h.region := by
    apply (ae_map_iff hstate hcurrentPredicate).2
    exact Filter.Eventually.of_forall fun omega hactiveFlag ↦ by
      have hactive : attempt.activeAt kfin omega := by
        simpa only [StoppedAttempt.activeAt, kfin] using hactiveFlag
      simpa only [StoppedAttempt.point] using
        (point_mem_region_of_active attempt kfin omega hactive)
  have hvalidPrevious : ∀ᵐ s ∂P.map (attempt.state kfin),
      s.1 = 1 → s.2.2.1 ∈ h.region := by
    apply (ae_map_iff hstate hpreviousPredicate).2
    exact Filter.Eventually.of_forall fun omega hactiveFlag ↦ by
      have hactive : attempt.activeAt kfin omega := by
        simpa only [StoppedAttempt.activeAt, kfin] using hactiveFlag
      let j : Fin K := ⟨k - 1, by omega⟩
      have hprev : attempt.activeAt j.castSucc omega := by
        have hprev' := attempt.activeAt_of_le omega (k - 1) k
          (Nat.sub_le k 1) (Nat.le_of_lt hk) hactive
        simpa only [j, Fin.castSucc_mk, kfin] using hprev'
      have hsucc : j.succ = kfin := by
        apply Fin.ext
        dsimp [j, kfin]
        omega
      have hpreviousField :
          (attempt.state kfin omega).2.2.1 =
            (attempt.state j.castSucc omega).2.1 := by
        simpa only [hsucc] using
          (successor_previousPoint_eq_of_active attempt j omega hprev)
      rw [hpreviousField]
      simpa only [StoppedAttempt.point] using
        (point_mem_region_of_active attempt j.castSucc omega hprev)
  have hsection : ∀ᵐ s ∂P.map (attempt.state kfin),
      Integrable (fun batch ↦ finiteRawGradientErrorObservable h oracle Q B b k
        (s, batch)) (P.map (attempt.batch k)) := by
    filter_upwards [hvalidCurrent, hvalidPrevious] with s hsCurrent hsPrevious
    by_cases hs : s.1 = 1
    · exact (finiteRawGradientErrorObservable_updateBatch_le
        attempt k hupdate hbatchIndependent s hs (hsCurrent hs) (hsPrevious hs)).1
    · simpa only [finiteRawGradientErrorObservable, if_neg hs] using
        (integrable_const (μ := P.map (attempt.batch k)) (0 : ℝ))
  have hbound : ∀ᵐ s ∂P.map (attempt.state kfin),
      (∫ batch, finiteRawGradientErrorObservable h oracle Q B b k
          (s, batch) ∂P.map (attempt.batch k)) ≤
        finiteUpdateConditionalBound h oracle b s := by
    filter_upwards [hvalidCurrent, hvalidPrevious] with s hsCurrent hsPrevious
    by_cases hs : s.1 = 1
    · exact (finiteRawGradientErrorObservable_updateBatch_le
        attempt k hupdate hbatchIndependent s hs (hsCurrent hs) (hsPrevious hs)).2
    · rw [finiteUpdateConditionalBound_of_inactive h oracle b s hs]
      simp only [finiteRawGradientErrorObservable, if_neg hs, integral_zero]
      exact le_rfl
  have hCcomp := integrable_finiteUpdateConditionalBound_comp
    attempt invariant k hk hkpos hprevious
  have hCmap : Integrable (finiteUpdateConditionalBound h oracle b)
      (P.map (attempt.state kfin)) :=
    (integrable_map_measure
      (measurable_finiteUpdateConditionalBound h oracle b).aestronglyMeasurable
      hstate).2 hCcomp
  have hbridge := activeRawGradientErrorMeanSquare_le_of_statewiseBounds
    attempt k hk (finiteUpdateConditionalBound h oracle b) hsection hCmap hbound
  exact ⟨hbridge.1, hbridge.2.trans
    (integral_finiteUpdateConditionalBound_map_le
      attempt invariant k hk hkpos hprevious)⟩

/-- Theorem 3.7: the oracle assumptions and a stopped-prefix invariant imply
the full finite SPIDER moment recursion for the actual stopped observables. -/
theorem finiteStoppedSPIDERRecursion_of_prefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt) :
    FiniteStoppedSPIDERRecursion attempt := by
  have hraw : ∀ k, k < K →
      Integrable (activeRawGradientErrorIntegrand attempt k) P := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro hk
        by_cases hrefresh : k % Q = 0
        · exact (activeRawGradientError_refresh attempt k hk hrefresh).1
        · have hkpos : 0 < k :=
            Nat.pos_of_ne_zero fun hkZero ↦
              hrefresh (by simp only [hkZero, Nat.zero_mod])
          have hprevious : Integrable
              (activeRawGradientErrorIntegrand attempt (k - 1)) P :=
            ih (k - 1) (by omega) (by omega)
          exact (activeRawGradientError_update
            attempt invariant k hk hrefresh hprevious).1
  refine
    { raw_integrable := hraw
      refresh_bound := ?_
      update_bound := ?_ }
  · intro k hk hrefresh
    exact (activeRawGradientError_refresh attempt k hk hrefresh).2
  · intro k hk hkpos hupdate
    have hprevious : Integrable
        (activeRawGradientErrorIntegrand attempt (k - 1)) P :=
      hraw (k - 1) (by omega)
    exact (activeRawGradientError_update
      attempt invariant k hk hupdate hprevious).2

/-- Theorem 3.7: a stopped-prefix invariant canonically supplies both pieces
of the finite stopped energy coupling. -/
theorem finiteStoppedEnergyCoupling_of_prefixInvariant
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt) :
    FiniteStoppedEnergyCoupling attempt where
  pathInvariant := invariant
  spiderRecursion := finiteStoppedSPIDERRecursion_of_prefixInvariant attempt invariant

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
