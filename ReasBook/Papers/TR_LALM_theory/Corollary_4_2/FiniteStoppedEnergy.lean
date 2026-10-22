/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis
public import TR_LALM_theory.Corollary_4_2.StochasticEstimator
import all TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis
import all TR_LALM_theory.Corollary_4_2.StoppedScheduledAttempt

public section

open MeasureTheory
open scoped BigOperators NNReal

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

/-- Helper for Corollary 4.2: every finite stopped raw-error integrand is
integrable, including the absorbing zero branch after the horizon. -/
theorem integrable_activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    Integrable (activeRawGradientErrorIntegrand attempt k) P := by
  by_cases hk : k < K
  · exact (activeRawGradientError_le_lastRefresh attempt k hk).1
  · have heq : activeRawGradientErrorIntegrand attempt k = fun _ : Ω ↦ (0 : ℝ) := by
      funext omega
      simp only [LALM.Correction.StoppedAttemptAnalysis.activeRawGradientErrorIntegrand,
        dif_neg hk]
    rw [heq]
    exact integrable_const _

/-- Helper for Corollary 4.2: clipping contracts the finite stopped gradient
error pointwise, with both branches zero after localization stops. -/
theorem activeGradientErrorIntegrand_le_activeRawGradientErrorIntegrand
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    activeGradientErrorIntegrand attempt k omega ≤
      activeRawGradientErrorIntegrand attempt k omega := by
  by_cases hk : k < K
  · simp only [LALM.Correction.StoppedAttemptAnalysis.activeGradientErrorIntegrand,
      dif_pos hk, LALM.Correction.StoppedAttemptAnalysis.activeRawGradientErrorIntegrand,
      dif_pos hk]
    cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega with
    | inl inactive =>
        simp [localizedRawGradientErrorObservable_apply]
    | inr active =>
        have hx : active.1.1 ∈ h.region :=
          attempt.region_condition.thickening_subset
            (Metric.self_subset_cthickening X active.current_mem)
        have hgradient : ‖gradient f active.1.1‖ ≤ h.gradientBound :=
          h.norm_gradient_le active.1.1 hx
        have hclip := SPIDER.norm_clip_sub_le h.gradientBound
          (canonicalRawEstimateAt oracle Q B b k active.1
            (attempt.batch k omega)) (gradient f active.1.1)
          hgradient
        dsimp
        rw [localizedRawGradientErrorObservable_apply]
        simp only [h.objectiveGradientExtension_eq hx]
        exact pow_le_pow_left₀ (norm_nonneg _) hclip 2
  · simp only [LALM.Correction.StoppedAttemptAnalysis.activeGradientErrorIntegrand,
      dif_neg hk, LALM.Correction.StoppedAttemptAnalysis.activeRawGradientErrorIntegrand,
      dif_neg hk]
    exact le_rfl

/-- Helper for Corollary 4.2: the clipped finite error integral is bounded by
the corresponding raw estimator integral. -/
theorem activeGradientErrorMeanSquare_le_activeRawGradientError
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) :
    (∫ omega, activeGradientErrorIntegrand attempt k omega ∂P) ≤
      activeRawGradientErrorMeanSquare attempt k := by
  have hraw := integrable_activeRawGradientErrorIntegrand attempt k
  have hclip := integrable_activeGradientErrorIntegrand attempt k
  simp only [LALM.Correction.StoppedAttemptAnalysis.activeRawGradientErrorMeanSquare]
  exact integral_mono hclip hraw
    (activeGradientErrorIntegrand_le_activeRawGradientErrorIntegrand attempt k)

/-- Helper for Corollary 4.2: one finite corrected transition is bounded by
the displacement factor times its active base step. -/
theorem norm_stoppedPointDisplacement_le_baseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) (hk : k < K) :
    ‖StoppedAttempt.point attempt (k + 1) omega -
        StoppedAttempt.point attempt k omega‖ ≤
      displacementFactor h params.delta *
        ‖StoppedAttempt.baseStep attempt k omega‖ := by
  have hfactorNonneg : 0 ≤ displacementFactor h params.delta := by
    rw [displacementFactor_def]
    have hstepConstantNonneg : 0 ≤ stepConstant h := by
      rw [stepConstant_def]
      positivity
    exact add_nonneg (by norm_num)
      (mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta))
  simp only [LALM.Correction.StoppedAttempt.point, dif_pos hk]
  cases hstate : attempt.state ⟨k, Nat.lt_succ_of_lt hk⟩ omega with
  | inl inactive =>
      unfold StoppedAttempt.paddedPointTransition
      change ‖StoppedAttempt.point attempt k omega -
        StoppedAttempt.point attempt k omega‖ ≤ _
      rw [sub_self, norm_zero]
      exact mul_nonneg hfactorNonneg (norm_nonneg _)
  | inr active =>
      unfold StoppedAttempt.paddedPointTransition
      change ‖canonicalActiveNextPointAt h oracle params Q B b k
          (active, attempt.batch k omega) - StoppedAttempt.point attempt k omega‖ ≤ _
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
      rw [StoppedAttempt.activeState_baseStep_eq_baseStep attempt k omega hk
        active hstate]
      exact hdisplacement

/-- Helper for Corollary 4.2: a finite stopped displacement square is bounded
by the corresponding scaled base-step square. -/
theorem activeDisplacementIntegrand_le_scaledBaseStep
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (k : ℕ) (omega : Ω) :
    activeDisplacementIntegrand attempt k omega ≤
      displacementFactor h params.delta ^ 2 *
        activeBaseStepIntegrand attempt k omega := by
  by_cases hk : k < K
  · simp only [LALM.Correction.StoppedAttemptAnalysis.activeDisplacementIntegrand,
      LALM.Correction.StoppedAttemptAnalysis.activeBaseStepIntegrand, hk,
      ↓reduceIte]
    have hnorm := norm_stoppedPointDisplacement_le_baseStep attempt k omega hk
    have hfactorNonneg : 0 ≤ displacementFactor h params.delta *
        ‖StoppedAttempt.baseStep attempt k omega‖ :=
      mul_nonneg (by
        rw [displacementFactor_def]
        have hstepConstantNonneg : 0 ≤ stepConstant h := by
          rw [stepConstant_def]
          positivity
        exact add_nonneg (by norm_num)
          (mul_nonneg hstepConstantNonneg (NNReal.coe_nonneg params.delta)))
        (norm_nonneg _)
    calc
      ‖StoppedAttempt.point attempt (k + 1) omega -
          StoppedAttempt.point attempt k omega‖ ^ 2 ≤
          (displacementFactor h params.delta *
            ‖StoppedAttempt.baseStep attempt k omega‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) hfactorNonneg).2 hnorm
      _ = displacementFactor h params.delta ^ 2 *
          ‖StoppedAttempt.baseStep attempt k omega‖ ^ 2 := by ring
  · simp only [LALM.Correction.StoppedAttemptAnalysis.activeDisplacementIntegrand,
      LALM.Correction.StoppedAttemptAnalysis.activeBaseStepIntegrand, hk,
      ↓reduceIte]
    norm_num

/-- Helper for Corollary 4.2: finite stopped displacement energy is controlled
by scaled finite base-step energy. -/
theorem sumActiveDisplacementEnergy_le_scaledBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    stoppedDisplacementEnergy attempt ≤
      displacementFactor h params.delta ^ 2 * stoppedBaseStepEnergy attempt := by
  have hterm (k : ℕ) :
      (∫ omega, activeDisplacementIntegrand attempt k omega ∂P) ≤
        displacementFactor h params.delta ^ 2 *
          ∫ omega, activeBaseStepIntegrand attempt k omega ∂P := by
    calc
      (∫ omega, activeDisplacementIntegrand attempt k omega ∂P) ≤
          (∫ omega, displacementFactor h params.delta ^ 2 *
            activeBaseStepIntegrand attempt k omega ∂P) :=
        integral_mono
          (integrable_activeDisplacementIntegrand attempt k)
          ((integrable_activeBaseStepIntegrand attempt k).const_mul _)
          (activeDisplacementIntegrand_le_scaledBaseStep attempt k)
      _ = displacementFactor h params.delta ^ 2 *
          ∫ omega, activeBaseStepIntegrand attempt k omega ∂P := by
        rw [integral_const_mul]
  change (∑ k ∈ Finset.range K,
      ∫ omega, activeDisplacementIntegrand attempt k omega ∂P) ≤
    displacementFactor h params.delta ^ 2 *
      (∑ k ∈ Finset.range K,
        ∫ omega, activeBaseStepIntegrand attempt k omega ∂P)
  calc
    (∑ k ∈ Finset.range K,
        ∫ omega, activeDisplacementIntegrand attempt k omega ∂P) ≤
      ∑ k ∈ Finset.range K,
        displacementFactor h params.delta ^ 2 *
          ∫ omega, activeBaseStepIntegrand attempt k omega ∂P := by
      exact Finset.sum_le_sum fun k hk ↦ hterm k
    _ = displacementFactor h params.delta ^ 2 *
        ∑ k ∈ Finset.range K,
          ∫ omega, activeBaseStepIntegrand attempt k omega ∂P := by
      rw [Finset.mul_sum]

/-! The following aggregate estimate is the finite stopped counterpart of the
    refresh-block SPIDER estimate.  It deliberately uses only active finite
    coordinates, so no infinite corrected tail is involved. -/

/-- Helper for Corollary 4.2: the finite stopped clipped-gradient energy is
bounded by the refresh noise budget and the finite corrected displacement
energy. -/
theorem stoppedGradientErrorEnergy_le_scaledBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    stoppedGradientErrorEnergy attempt ≤
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
        ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
            displacementFactor h params.delta ^ 2 / (b : ℝ)) *
          stoppedBaseStepEnergy attempt := by
  classical
  have hactiveBound (k : ℕ) (hk : k < K) :
      (∫ omega, activeGradientErrorIntegrand attempt k omega ∂P) ≤
        (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ j ∈ Finset.Ico (k - k % Q) k,
              ∫ omega, activeDisplacementIntegrand attempt j omega ∂P := by
    exact (activeGradientErrorMeanSquare_le_activeRawGradientError attempt k).trans
      (activeRawGradientError_le_lastRefresh attempt k hk).2
  have hblockCount := StochasticRun.sumBlockPrefixes_le
    (fun j ↦ ∫ omega, activeDisplacementIntegrand attempt j omega ∂P)
    (fun j ↦ integral_nonneg fun omega ↦
      activeDisplacementIntegrand_nonneg attempt j omega) Q K Q.pos
  have hdisplacement := sumActiveDisplacementEnergy_le_scaledBaseStepEnergy attempt
  have hvarianceCoefficient :
      0 ≤ (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) := by
    positivity
  have hblockCoefficient :
      0 ≤ (Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg _) hvarianceCoefficient
  unfold stoppedGradientErrorEnergy
  calc
    ∑ k ∈ Finset.range K,
        ∫ omega, activeGradientErrorIntegrand attempt k omega ∂P ≤
        ∑ k ∈ Finset.range K,
          ((oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
            (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                ∫ omega, activeDisplacementIntegrand attempt j omega ∂P) := by
      exact Finset.sum_le_sum fun k hk ↦
        hactiveBound k (Finset.mem_range.mp hk)
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ∑ k ∈ Finset.range K,
              ∑ j ∈ Finset.Ico (k - k % Q) k,
                ∫ omega, activeDisplacementIntegrand attempt j omega ∂P := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        nsmul_eq_mul, Finset.mul_sum]
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          (oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ) *
            ((Q : ℝ) * ∑ k ∈ Finset.range K,
              ∫ omega, activeDisplacementIntegrand attempt k omega ∂P) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hblockCount hvarianceCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))) *
            ∑ k ∈ Finset.range K,
              ∫ omega, activeDisplacementIntegrand attempt k omega ∂P := by
      ring
    _ ≤ (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * ((oracle.meanSquareLipschitz : ℝ) ^ 2 / (b : ℝ))) *
            (displacementFactor h params.delta ^ 2 *
              stoppedBaseStepEnergy attempt) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hdisplacement hblockCoefficient) _
    _ = (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / (B : ℝ) +
          ((Q : ℝ) * (oracle.meanSquareLipschitz : ℝ) ^ 2 *
              displacementFactor h params.delta ^ 2 / (b : ℝ)) *
            stoppedBaseStepEnergy attempt := by
      ring

end StoppedAttemptAnalysis

end LALM.Correction

end
