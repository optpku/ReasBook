/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorObservables

public section

open MeasureTheory
open scoped NNReal

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

/-- Helper for Corollary 4.2: the actual localized conditional bound is
dominated by the preceding survival-masked raw error and displacement. -/
theorem localizedUpdateConditionalBound_apply_run_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk : 0 < k) (omega : Ω) :
    localizedUpdateConditionalBound h oracle params b X
        (localizedPreBatchState run X initial_mem h_region k omega) ≤
      activeRawGradientErrorIntegrand run X (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activePointDisplacementIntegrand run X (k - 1) omega := by
  classical
  have hkPredSucc : k - 1 + 1 = k := by omega
  rw [localizedUpdateConditionalBound_apply_run
    run X initial_mem h_region k hk omega]
  -- On current survival, antitonicity exposes the same two predecessor terms.
  by_cases hcurrent : omega ∈ survivalEvent run X k
  · have hprevious : omega ∈ survivalEvent run X (k - 1) :=
      survivalEvent_antitone run X (Nat.sub_le k 1) hcurrent
    rw [Set.indicator_of_mem hcurrent,
      activeRawGradientErrorIntegrand_of_mem run X (k - 1) omega hprevious,
      activePointDisplacementIntegrand_of_mem run X (k - 1) omega hprevious,
      hkPredSucc]
  · simp only [Set.indicator_of_notMem hcurrent]
    -- If only the predecessor event survives, the right side remains nonnegative.
    by_cases hprevious : omega ∈ survivalEvent run X (k - 1)
    · rw [activeRawGradientErrorIntegrand_of_mem
          run X (k - 1) omega hprevious,
        activePointDisplacementIntegrand_of_mem
          run X (k - 1) omega hprevious,
        hkPredSucc]
      positivity
    · rw [activeRawGradientErrorIntegrand_of_not_mem
          run X (k - 1) omega hprevious,
        activePointDisplacementIntegrand_of_not_mem
          run X (k - 1) omega hprevious]
      simp only [mul_zero, add_zero]
      exact le_rfl

/-- Helper for Corollary 4.2: an integrable preceding active raw error makes
the localized conditional bound integrable along the adapted run state. -/
theorem integrable_localizedUpdateConditionalBound_comp
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand run X (k - 1)) P) :
    Integrable (fun omega ↦
      localizedUpdateConditionalBound h oracle params b X
        (localizedPreBatchState run X initial_mem h_region k omega)) P := by
  have hstate := aemeasurable_localizedPreBatchState
    run X hX initial_mem h_region k
  have hmeasurable : AEStronglyMeasurable (fun omega ↦
      localizedUpdateConditionalBound h oracle params b X
        (localizedPreBatchState run X initial_mem h_region k omega)) P :=
    ((measurable_localizedUpdateConditionalBound h oracle params b X).comp_aemeasurable
      hstate).aestronglyMeasurable
  have hdisplacement := integrable_activePointDisplacementIntegrand
    run X hX initial_mem h_region (k - 1)
  have hscaled : Integrable (fun omega ↦
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        activePointDisplacementIntegrand run X (k - 1) omega) P :=
    hdisplacement.const_mul
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
  have hmajorant : Integrable (fun omega ↦
      activeRawGradientErrorIntegrand run X (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activePointDisplacementIntegrand run X (k - 1) omega) P :=
    hprevious.add hscaled
  -- The pointwise bridge and nonnegativity place the composite below this majorant.
  refine Integrable.mono_nonneg hmajorant hmeasurable ?_ ?_
  · exact Filter.Eventually.of_forall fun omega ↦
      localizedUpdateConditionalBound_nonneg
        (oracle := oracle)
        (localizedPreBatchState run X initial_mem h_region k omega)
  · exact Filter.Eventually.of_forall fun omega ↦
      localizedUpdateConditionalBound_apply_run_le
        run X initial_mem h_region k hk omega

/-- Helper for Corollary 4.2: composite integrability transports to the law
of the localized adapted pre-batch state. -/
theorem integrable_localizedUpdateConditionalBound_map
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand run X (k - 1)) P) :
    Integrable (localizedUpdateConditionalBound h oracle params b X)
      (P.map (localizedPreBatchState run X initial_mem h_region k)) := by
  have hstate := aemeasurable_localizedPreBatchState
    run X hX initial_mem h_region k
  have hcomp := integrable_localizedUpdateConditionalBound_comp
    run X hX initial_mem h_region k hk hprevious
  -- Apply the map-integrability equivalence only after proving the composite case.
  exact (integrable_map_measure
    (measurable_localizedUpdateConditionalBound h oracle params b X).aestronglyMeasurable
    hstate).2 hcomp

/-- Helper for Corollary 4.2: integrating the localized conditional bound
under the adapted-state law is controlled by the two preceding active moments. -/
theorem integral_localizedUpdateConditionalBound_map_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X)
    (k : ℕ) (hk : 0 < k)
    (hprevious : Integrable
      (activeRawGradientErrorIntegrand run X (k - 1)) P) :
    (∫ s, localizedUpdateConditionalBound h oracle params b X s
        ∂P.map (localizedPreBatchState run X initial_mem h_region k)) ≤
      activeRawGradientErrorMeanSquare run X (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activePointDisplacementMeanSquare run X (k - 1) := by
  have hstate := aemeasurable_localizedPreBatchState
    run X hX initial_mem h_region k
  have hcomp := integrable_localizedUpdateConditionalBound_comp
    run X hX initial_mem h_region k hk hprevious
  have hdisplacement := integrable_activePointDisplacementIntegrand
    run X hX initial_mem h_region (k - 1)
  have hscaled : Integrable (fun omega ↦
      (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
        activePointDisplacementIntegrand run X (k - 1) omega) P :=
    hdisplacement.const_mul
      ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))
  have hmajorant : Integrable (fun omega ↦
      activeRawGradientErrorIntegrand run X (k - 1) omega +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activePointDisplacementIntegrand run X (k - 1) omega) P :=
    hprevious.add hscaled
  -- Pull back the mapped integral, compare pointwise, and identify both moments.
  calc
    (∫ s, localizedUpdateConditionalBound h oracle params b X s
        ∂P.map (localizedPreBatchState run X initial_mem h_region k)) =
        ∫ omega, localizedUpdateConditionalBound h oracle params b X
          (localizedPreBatchState run X initial_mem h_region k omega) ∂P :=
      integral_map hstate
        (measurable_localizedUpdateConditionalBound h oracle params b X).aestronglyMeasurable
    _ ≤ ∫ omega,
        (activeRawGradientErrorIntegrand run X (k - 1) omega +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            activePointDisplacementIntegrand run X (k - 1) omega) ∂P :=
      integral_mono hcomp hmajorant fun omega ↦
        localizedUpdateConditionalBound_apply_run_le
          run X initial_mem h_region k hk omega
    _ = activeRawGradientErrorMeanSquare run X (k - 1) +
        (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
          activePointDisplacementMeanSquare run X (k - 1) := by
      rw [integral_add hprevious hscaled, integral_const_mul,
        activeRawGradientErrorMeanSquare_def,
        activePointDisplacementMeanSquare_def]

end LALM.Correction.StochasticRun.Localization

end
