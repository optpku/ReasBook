/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorConditionalBound

public section

open MeasureTheory
open scoped BigOperators NNReal

namespace LALM.Correction.StochasticRun.Localization

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
variable {Q B b : ℕ+} {confidence : ℝ}

/-- Helper for Corollary 4.2: statewise fresh-batch bounds transfer through
adapted-state independence to the actual survival-masked raw-error moment. -/
theorem activeRawGradientErrorMeanSquare_le_of_sectionBounds
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (C : LocalizedPreBatchState h params X → ℝ)
    (hsection : ∀ s, Integrable (fun batch ↦
      localizedRawGradientErrorObservable h oracle params Q B b X k
        (s, batch)) (P.map fun omega i ↦ run.sample k i omega))
    (hC : Integrable C
      (P.map (localizedPreBatchState run X initial_mem h_region k)))
    (hbound : ∀ s,
      (∫ batch, localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch) ∂P.map fun omega i ↦ run.sample k i omega) ≤ C s) :
    Integrable (activeRawGradientErrorIntegrand run X k) P ∧
      activeRawGradientErrorMeanSquare run X k ≤
        ∫ s, C s ∂P.map (localizedPreBatchState run X initial_mem h_region k) := by
  have hstate := aemeasurable_localizedPreBatchState
    run X hX initial_mem h_region k
  have hfreshBatch : AEMeasurable (fun omega i ↦ run.sample k i omega) P :=
    aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable
  have hindependent := indepFun_localizedPreBatchState_freshBatch
    run X hX initial_mem h_region k
  have hnonnegative : ∀ z :
      LocalizedPreBatchState h params X × (ℕ → Ξ),
      0 ≤ localizedRawGradientErrorObservable h oracle params Q B b X k z := by
    rintro ⟨s, batch⟩
    cases s with
    | inl inactive =>
        rw [localizedRawGradientErrorObservable_apply]
    | inr active =>
        rw [localizedRawGradientErrorObservable_apply]
        positivity
  have hpair := EstimatorProbability.independentPair_integrable_integral_le
    (localizedPreBatchState run X initial_mem h_region k)
    (fun omega i ↦ run.sample k i omega)
    (localizedRawGradientErrorObservable h oracle params Q B b X k) C
    hindependent hstate hfreshBatch
    (measurable_localizedRawGradientErrorObservable
      h oracle params Q B b X k).aemeasurable
    hnonnegative (Filter.Eventually.of_forall hsection) hC
    (Filter.Eventually.of_forall hbound)
  have hidentify : (fun omega ↦
      localizedRawGradientErrorObservable h oracle params Q B b X k
        (localizedPreBatchState run X initial_mem h_region k omega,
          fun i ↦ run.sample k i omega)) =ᵐ[P]
      activeRawGradientErrorIntegrand run X k :=
    Filter.Eventually.of_forall fun omega ↦
      localizedRawGradientErrorObservable_apply_run
        run X initial_mem h_region k omega
  -- Identify the independent pair with the actual masked run observable.
  refine ⟨hpair.1.congr hidentify, ?_⟩
  rw [activeRawGradientErrorMeanSquare_def,
    ← integral_congr_ae hidentify]
  exact hpair.2

/-- Helper for Corollary 4.2: a localized refresh has integrable active raw
error and resets its mean square to the large-batch variance scale. -/
theorem activeRawGradientError_refresh
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hrefresh : k % Q = 0) :
    Integrable (activeRawGradientErrorIntegrand run X k) P ∧
      activeRawGradientErrorMeanSquare run X k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) := by
  classical
  have hfreshBatch : AEMeasurable (fun omega i ↦ run.sample k i omega) P :=
    aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using run.independent_sample.precomp hinjective
  have hsection : ∀ s : LocalizedPreBatchState h params X,
      Integrable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) (P.map fun omega i ↦ run.sample k i omega) := by
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
          (integrable_const (μ :=
            P.map fun omega i ↦ run.sample k i omega) (0 : ℝ))
    | inr active =>
        have hcurrent : active.1.1 ∈ h.region :=
          h_region.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed := EstimatorProbability.fixedPointRefreshBatchMeanSquare_le
          (oracle := oracle) active.1.1 hcurrent (run.sample k) B
          (run.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        refine (integrable_map_measure
          hsectionMeasurable.aestronglyMeasurable hfreshBatch).2 ?_
        simpa only [Function.comp_def,
          localizedRawGradientErrorObservable_of_refresh, hrefresh,
          hgradient] using hfixed.1
  have hbound : ∀ s : LocalizedPreBatchState h params X,
      (∫ batch, localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch) ∂P.map fun omega i ↦ run.sample k i omega) ≤
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
          h_region.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed := EstimatorProbability.fixedPointRefreshBatchMeanSquare_le
          (oracle := oracle) active.1.1 hcurrent (run.sample k) B
          (run.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        rw [integral_map hfreshBatch hsectionMeasurable.aestronglyMeasurable]
        simpa only [Function.comp_apply,
          localizedRawGradientErrorObservable_of_refresh, hrefresh,
          hgradient] using hfixed.2
  have hstate := aemeasurable_localizedPreBatchState
    run X hX initial_mem h_region k
  have hbridge := activeRawGradientErrorMeanSquare_le_of_sectionBounds
    run X hX initial_mem h_region k
    (fun _ ↦ (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ))
    hsection (integrable_const _) hbound
  refine ⟨hbridge.1, hbridge.2.trans_eq ?_⟩
  -- The mapped adapted-state law remains a probability measure.
  rw [integral_const, Measure.real,
    Measure.map_apply_of_aemeasurable hstate MeasurableSet.univ]
  simp only [Set.preimage_univ, measure_univ, ENNReal.toReal_one, one_smul]

/-- Helper for Corollary 4.2: a localized nonrefresh step adds at most one
mean-square-Lipschitz displacement innovation to the preceding active error. -/
theorem activeRawGradientError_update
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hupdate : k % Q ≠ 0)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand run X (k - 1)) P) :
    Integrable (activeRawGradientErrorIntegrand run X k) P ∧
      activeRawGradientErrorMeanSquare run X k ≤
        activeRawGradientErrorMeanSquare run X (k - 1) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activePointDisplacementMeanSquare run X (k - 1) := by
  classical
  have hk : 0 < k :=
    Nat.pos_of_ne_zero fun hkZero ↦ hupdate (by simp only [hkZero, Nat.zero_mod])
  have hfreshBatch : AEMeasurable (fun omega i ↦ run.sample k i omega) P :=
    aemeasurable_pi_lambda _ fun i ↦ (run.hasLaw_sample k i).aemeasurable
  have hbatchIndependent : ProbabilityTheory.iIndepFun (run.sample k) P := by
    have hinjective : Function.Injective (fun i : ℕ ↦ (k, i)) := by
      intro i j hij
      exact congrArg Prod.snd hij
    simpa only using run.independent_sample.precomp hinjective
  have hsection : ∀ s : LocalizedPreBatchState h params X,
      Integrable (fun batch ↦
        localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch)) (P.map fun omega i ↦ run.sample k i omega) := by
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
          (integrable_const (μ :=
            P.map fun omega i ↦ run.sample k i omega) (0 : ℝ))
    | inr active =>
        have hcurrent : active.1.1 ∈ h.region :=
          h_region.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed := EstimatorProbability.fixedPointUpdateBatchMeanSquare_le
          (oracle := oracle) active.1.1 hcurrent active.1.2.1
          active.previous_mem_region
          (active.1.2.2.2 - gradient f active.1.2.1)
          (run.sample k) b (run.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        refine (integrable_map_measure
          hsectionMeasurable.aestronglyMeasurable hfreshBatch).2 ?_
        refine hfixed.1.congr (Filter.Eventually.of_forall fun omega ↦ ?_)
        rw [Function.comp_apply,
          localizedRawGradientErrorObservable_of_update active
          (fun i ↦ run.sample k i omega) k hupdate, hgradient]
  have hbound : ∀ s : LocalizedPreBatchState h params X,
      (∫ batch, localizedRawGradientErrorObservable h oracle params Q B b X k
          (s, batch) ∂P.map fun omega i ↦ run.sample k i omega) ≤
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
          h_region.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hfixed := EstimatorProbability.fixedPointUpdateBatchMeanSquare_le
          (oracle := oracle) active.1.1 hcurrent active.1.2.1
          active.previous_mem_region
          (active.1.2.2.2 - gradient f active.1.2.1)
          (run.sample k) b (run.hasLaw_sample k) hbatchIndependent
        have hgradient := h.objectiveGradientExtension_eq hcurrent
        rw [integral_map hfreshBatch hsectionMeasurable.aestronglyMeasurable,
          localizedUpdateConditionalBound_apply]
        rw [integral_congr_ae (Filter.Eventually.of_forall fun omega ↦
          localizedRawGradientErrorObservable_of_update active
            (fun i ↦ run.sample k i omega) k hupdate), hgradient]
        exact hfixed.2
  have hC := integrable_localizedUpdateConditionalBound_map
    run X hX initial_mem h_region k hk hprevious
  have hbridge := activeRawGradientErrorMeanSquare_le_of_sectionBounds
    run X hX initial_mem h_region k
    (localizedUpdateConditionalBound h oracle params b X)
    hsection hC hbound
  -- The mapped conditional-bound theorem already owns enlargement to the
  -- predecessor survival event.
  exact ⟨hbridge.1, hbridge.2.trans
    (integral_localizedUpdateConditionalBound_map_le
      run X hX initial_mem h_region k hk hprevious)⟩

/-- Helper for Corollary 4.2: the active raw SPIDER error accumulates only
the displacement innovations since the most recent refresh index. -/
theorem activeRawGradientError_le_lastRefresh
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ) :
    Integrable (activeRawGradientErrorIntegrand run X k) P ∧
      activeRawGradientErrorMeanSquare run X k ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              activePointDisplacementMeanSquare run X j := by
  classical
  -- Strong induction resets at refresh indices and extends one update at a time.
  induction k using Nat.strong_induction_on with
  | h k ih =>
      by_cases hrefresh : k % Q = 0
      · have hone := activeRawGradientError_refresh
          run X hX initial_mem h_region k hrefresh
        refine ⟨hone.1, ?_⟩
        simpa only [hrefresh, Nat.sub_zero, Finset.Ico_self,
          Finset.sum_empty, mul_zero, add_zero] using hone.2
      · have hkPositive : 0 < k :=
          Nat.pos_of_ne_zero fun hkZero ↦
            hrefresh (by simp only [hkZero, Nat.zero_mod])
        have hkPredSucc : k - 1 + 1 = k := by omega
        have hprevious := ih (k - 1) (by omega)
        have hone := activeRawGradientError_update
          run X hX initial_mem h_region k hrefresh hprevious.1
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
          have hpreviousModLt : (k - 1) % Q < Q :=
            Nat.mod_lt (k - 1) Q.pos
          by_contra hnot
          have heq : (k - 1) % Q + 1 = Q := by omega
          apply hrefresh
          rw [hmodSucc, heq, Nat.mod_self]
        have hkModSucc : k % Q = (k - 1) % Q + 1 := by
          rw [hmodSucc, Nat.mod_eq_of_lt hpreviousRemainderSucc]
        have hblockStart :
            k - k % Q = (k - 1) - (k - 1) % Q := by
          omega
        have hstart_le : k - k % Q ≤ k - 1 := by
          have hkModPositive : 0 < k % Q := Nat.pos_of_ne_zero hrefresh
          omega
        have hblockSum :
            (∑ j ∈ Finset.Ico (k - k % Q) k,
                activePointDisplacementMeanSquare run X j) =
              (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  activePointDisplacementMeanSquare run X j) +
                activePointDisplacementMeanSquare run X (k - 1) := by
          calc
            (∑ j ∈ Finset.Ico (k - k % Q) k,
                activePointDisplacementMeanSquare run X j) =
                ∑ j ∈ Finset.Ico (k - k % Q) ((k - 1) + 1),
                  activePointDisplacementMeanSquare run X j := by
                    rw [hkPredSucc]
            _ = (∑ j ∈ Finset.Ico (k - k % Q) (k - 1),
                  activePointDisplacementMeanSquare run X j) +
                activePointDisplacementMeanSquare run X (k - 1) :=
              Finset.sum_Ico_succ_top hstart_le
                (activePointDisplacementMeanSquare run X)
            _ = (∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                  activePointDisplacementMeanSquare run X j) +
                activePointDisplacementMeanSquare run X (k - 1) := by
              rw [hblockStart]
        -- Insert the induction bound, then merge the final displacement into the block sum.
        calc
          activeRawGradientErrorMeanSquare run X k ≤
              activeRawGradientErrorMeanSquare run X (k - 1) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  activePointDisplacementMeanSquare run X (k - 1) := hone.2
          _ ≤ ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico ((k - 1) - (k - 1) % Q) (k - 1),
                    activePointDisplacementMeanSquare run X j) +
              (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                activePointDisplacementMeanSquare run X (k - 1) :=
            add_le_add hprevious.2 le_rfl
          _ = (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
                (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
                  ∑ j ∈ Finset.Ico (k - k % Q) k,
                    activePointDisplacementMeanSquare run X j := by
            rw [hblockSum]
            ring

end LALM.Correction.StochasticRun.Localization

end
