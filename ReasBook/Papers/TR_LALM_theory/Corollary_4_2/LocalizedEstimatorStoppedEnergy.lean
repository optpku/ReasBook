/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.LocalizedEstimatorOneStep
public import TR_LALM_theory.Corollary_4_2.StochasticEstimator

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

/-- Helper for Corollary 4.2: radial clipping cannot increase the
survival-restricted mean-square gradient error. -/
theorem activeGradientErrorMeanSquare_le_activeRawGradientError
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (k : ℕ)
    (hraw : Integrable (activeRawGradientErrorIntegrand run X k) P) :
    (∫ omega in survivalEvent run X k, ‖run.gradientError k omega‖ ^ 2 ∂P) ≤
      activeRawGradientErrorMeanSquare run X k := by
  have hsurvival := nullMeasurableSet_survivalEvent run X hX k
  have hclipped : Integrable
      ((survivalEvent run X k).indicator
        (fun omega ↦ ‖run.gradientError k omega‖ ^ 2)) P :=
    (integrableOn_gradientErrorSquare_preExit
      run X hX initial_mem h_region k).integrable_indicator₀ hsurvival
  -- On survival, region regularity puts the true gradient inside the clipping ball.
  have hpointwise (omega : Ω) :
      (survivalEvent run X k).indicator
          (fun omega' ↦ ‖run.gradientError k omega'‖ ^ 2) omega ≤
        activeRawGradientErrorIntegrand run X k omega := by
    by_cases homega : omega ∈ survivalEvent run X k
    · have hsegment :=
        (preExitPrefixBounds run X initial_mem h_region omega k homega).1 k
          (Nat.lt_succ_self k)
      have hx : run.point k omega ∈ h.region :=
        base_mem_region h (run.point k omega) (run.baseStep k omega) hsegment
      rw [Set.indicator_of_mem homega,
        activeRawGradientErrorIntegrand_of_mem run X k omega homega,
        run.gradientError_apply, run.gradientEstimate_apply, SPIDER.estimate_apply]
      exact pow_le_pow_left₀ (norm_nonneg _)
        (SPIDER.norm_clip_sub_le h.gradientBound _ _
          (h.norm_gradient_le _ hx)) 2
    · rw [Set.indicator_of_notMem homega,
        activeRawGradientErrorIntegrand_of_not_mem run X k omega homega]
  -- Integrate the pointwise clipping contraction in the two canonical spellings.
  rw [← integral_indicator₀ hsurvival, activeRawGradientErrorMeanSquare_def]
  exact integral_mono hclipped hraw hpointwise

/-- Helper for Corollary 4.2: accumulated active corrected displacement is
bounded by the corrected factor times stopped base-step energy. -/
theorem sumActivePointDisplacementMeanSquare_le_stoppedBaseStepEnergy
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (K : ℕ) :
    ∑ k ∈ Finset.range K, activePointDisplacementMeanSquare run X k ≤
      displacementFactor h params.delta ^ 2 * stoppedBaseStepEnergy run X K := by
  -- Sum the fixed-index survival bounds before identifying the stopped energy.
  calc
    ∑ k ∈ Finset.range K, activePointDisplacementMeanSquare run X k ≤
        ∑ k ∈ Finset.range K,
          displacementFactor h params.delta ^ 2 *
            ∫ omega in survivalEvent run X k,
              ‖run.baseStep k omega‖ ^ 2 ∂P := by
      exact Finset.sum_le_sum fun k _hk ↦
        activePointDisplacementMeanSquare_le_baseStep
          run X hX initial_mem h_region k
    _ = displacementFactor h params.delta ^ 2 *
        stoppedBaseStepEnergy run X K := by
      rw [stoppedBaseStepEnergy_def, Finset.mul_sum]

/-- Helper for Corollary 4.2: the stopped corrected estimator-error energy
obeys the refresh-block SPIDER variance estimate. -/
theorem stoppedGradientErrorEnergy_le
    (run : StochasticRun h oracle P x₀ multiplier₀ params Q B b)
    (X : Set (EuclideanSpace ℝ (Fin n))) (hX : MeasurableSet X)
    (initial_mem : x₀ ∈ X)
    (h_region : RegionCondition h oracle params confidence X) (K : ℕ) :
    stoppedGradientErrorEnergy run X K ≤
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
        ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          stoppedBaseStepEnergy run X K := by
  classical
  -- Route correction: localization supplies only survival-restricted path bounds,
  -- so the global-prefix accumulated estimator theorem is not applicable here.
  -- Compose the latest-refresh raw estimate with clipping at each active index.
  have hactiveBound (k : ℕ) (hk : k < K) :
      (∫ omega in survivalEvent run X k,
          ‖run.gradientError k omega‖ ^ 2 ∂P) ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              activePointDisplacementMeanSquare run X j := by
    have hraw := activeRawGradientError_le_lastRefresh
      run X hX initial_mem h_region k
    exact (activeGradientErrorMeanSquare_le_activeRawGradientError
      run X hX initial_mem h_region k hraw.1).trans hraw.2
  have hblockCount := LALM.Correction.StochasticRun.sumBlockPrefixes_le
    (activePointDisplacementMeanSquare run X)
    (activePointDisplacementMeanSquare_nonneg run X) Q K Q.pos
  have hdisplacement :=
    sumActivePointDisplacementMeanSquare_le_stoppedBaseStepEnergy
      run X hX initial_mem h_region K
  have hvarianceCoefficient :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  have hblockCoefficient :
      0 ≤ (Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) hvarianceCoefficient
  -- Sum, count each displacement at most once per refresh position, and transport once.
  rw [stoppedGradientErrorEnergy_def]
  calc
    ∑ k ∈ Finset.range K,
        ∫ omega in survivalEvent run X k,
          ‖run.gradientError k omega‖ ^ 2 ∂P ≤
        ∑ k ∈ Finset.range K,
          ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                activePointDisplacementMeanSquare run X j) := by
      exact Finset.sum_le_sum fun k hk ↦
        hactiveBound k (Finset.mem_range.mp hk)
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ k ∈ Finset.range K,
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                activePointDisplacementMeanSquare run X j := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ((Q : ℝ) * ∑ k ∈ Finset.range K,
              activePointDisplacementMeanSquare run X k) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hblockCount hvarianceCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))) *
            ∑ k ∈ Finset.range K,
              activePointDisplacementMeanSquare run X k := by
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))) *
            (displacementFactor h params.delta ^ 2 *
              stoppedBaseStepEnergy run X K) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hdisplacement hblockCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
              displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            stoppedBaseStepEnergy run X K := by
      ring

end LALM.Correction.StochasticRun.Localization

end
