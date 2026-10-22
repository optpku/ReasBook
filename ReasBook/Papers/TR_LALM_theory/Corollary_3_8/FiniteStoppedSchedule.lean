/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPath
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedPath

public section

open MeasureTheory
open scoped NNReal

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
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-! The following two certificates isolate the scalar schedule algebra from the
    pathwise and conditional-moment interfaces. -/

/-- Helper for Theorem 3.7: the stochastic error-step coefficient is positive. -/
lemma errorStepConstant_pos
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    0 < LALM.StochasticRun.errorStepConstant h params := by
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hfirst : 0 < (2 : ℝ) / params.beta := by positivity
  have hsecond : 0 ≤ LALM.multiplierErrorConstant h / params.rho := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  have hlyapunov : 0 < LALM.StochasticRun.lyapunovErrorConstant h params := by
    rw [LALM.StochasticRun.lyapunovErrorConstant_def]
    exact add_pos_of_pos_of_nonneg hfirst hsecond
  rw [LALM.StochasticRun.errorStepConstant_def]
  positivity

/-- Helper for Theorem 3.7: the prescribed base SPIDER batch absorbs the
    scheduled error-step coefficient by a factor of one half. -/
lemma scheduledErrorStepCoefficient_le_half
    (h : EqualityConstrained.Regularity f c)
    (oracle : EqualityConstrained.StochasticOracle f h.region ν)
    (params : LALM.Parameters h x₀ multiplier₀) (K : ℕ) :
    LALM.StochasticRun.errorStepConstant h params *
        ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) ≤
      (1 : ℝ) / 2 := by
  have hbatch :=
    (SPIDER.isSufficientInnerBatchSize_iff h oracle params
      (SPIDER.refreshPeriod K) (SPIDER.innerBatchSize h oracle params K)).mp
      (SPIDER.innerBatchSize_isSufficient h oracle params K)
  have hb : 0 < (SPIDER.innerBatchSize h oracle params K : ℝ) := by
    positivity
  have hdivided :
      (2 * LALM.StochasticRun.errorStepConstant h params *
          (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2) /
          (SPIDER.innerBatchSize h oracle params K : ℝ) ≤ 1 := by
    calc
      (2 * LALM.StochasticRun.errorStepConstant h params *
          (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2) /
          (SPIDER.innerBatchSize h oracle params K : ℝ) ≤
          (SPIDER.innerBatchSize h oracle params K : ℝ) /
            (SPIDER.innerBatchSize h oracle params K : ℝ) :=
        (div_le_div_iff_of_pos_right hb).2 hbatch
      _ = 1 := div_self hb.ne'
  calc
    LALM.StochasticRun.errorStepConstant h params *
        ((SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) =
        ((2 * LALM.StochasticRun.errorStepConstant h params *
            (SPIDER.refreshPeriod K : ℝ) * oracle.meanSquareLipschitz ^ 2) /
            (SPIDER.innerBatchSize h oracle params K : ℝ)) / 2 := by
      ring
    _ ≤ (1 : ℝ) / 2 :=
      div_le_div_of_nonneg_right hdivided (by norm_num)

/-- Theorem 3.7: the prescribed finite stopped base schedule bounds the
    clipped estimator-error and base-step energies by their canonical
    allowances, assuming the actual stopped moment recursion. -/
theorem finiteStoppedScheduledEnergyBounds
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (path : FiniteStoppedPath attempt)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (hbudget : path.baseStepBudget =
      LALM.StochasticRun.initialStepBound h params)
    (hcoefficient : path.errorStepCoefficient =
      LALM.StochasticRun.errorStepConstant h params) :
    stoppedGradientErrorEnergy attempt ≤
        LALM.StochasticRun.errorAverageConstant h oracle params ∧
      stoppedBaseStepEnergy attempt ≤
        LALM.StochasticRun.stepAverageConstant h oracle params := by
  have hsteps :
      stoppedBaseStepEnergy attempt ≤
        LALM.StochasticRun.initialStepBound h params +
          LALM.StochasticRun.errorStepConstant h params *
            stoppedGradientErrorEnergy attempt := by
    simpa only [hbudget, hcoefficient] using path.baseStepEnergy_le
  have herrors := stoppedGradientErrorEnergy_le attempt recursion
  rw [SPIDER.refreshBatchSize_coe K hK] at herrors
  have hKreal : 0 < (K : ℝ) := by positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have hvariance :
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / K =
        (oracle.noiseLevel : ℝ) ^ 2 := by
    field_simp [hKzero]
  rw [hvariance] at herrors
  have hDpos : 0 < LALM.StochasticRun.errorStepConstant h params :=
    errorStepConstant_pos h params
  have hDzero : LALM.StochasticRun.errorStepConstant h params ≠ 0 :=
    hDpos.ne'
  have hD0nonneg :
      0 ≤ LALM.StochasticRun.initialStepBound h params := by
    rw [← hbudget]
    exact path.baseStepBudget_nonneg
  have herrorNonneg : 0 ≤ stoppedGradientErrorEnergy attempt := by
    unfold stoppedGradientErrorEnergy
    apply Finset.sum_nonneg
    intro k hk
    unfold activeGradientErrorMeanSquare
    exact integral_nonneg (fun omega ↦
      activeGradientErrorIntegrand_nonneg attempt k omega)
  have hcoefficientNonneg :
      0 ≤ (SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ) := by
    positivity
  have hstepsScaled :=
    mul_le_mul_of_nonneg_left hsteps hcoefficientNonneg
  have hcombined :
      stoppedGradientErrorEnergy attempt ≤
        (oracle.noiseLevel : ℝ) ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) *
            (oracle.meanSquareLipschitz : ℝ) ^ 2 /
              (SPIDER.innerBatchSize h oracle params K : ℝ)) *
            (LALM.StochasticRun.initialStepBound h params +
              LALM.StochasticRun.errorStepConstant h params *
                stoppedGradientErrorEnergy attempt) :=
    herrors.trans (add_le_add (le_refl _) hstepsScaled)
  have habsorb := scheduledErrorStepCoefficient_le_half h oracle params K
  have habsorbCommuted :
      ((SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) *
          LALM.StochasticRun.errorStepConstant h params ≤ (1 : ℝ) / 2 := by
    simpa only [mul_comm] using habsorb
  have habsorbError :=
    mul_le_mul_of_nonneg_right habsorbCommuted herrorNonneg
  have hcoefficientLe :
      (SPIDER.refreshPeriod K : ℝ) *
          (oracle.meanSquareLipschitz : ℝ) ^ 2 /
            (SPIDER.innerBatchSize h oracle params K : ℝ) ≤
        ((1 : ℝ) / 2) /
          LALM.StochasticRun.errorStepConstant h params :=
    (le_div_iff₀ hDpos).2 habsorbCommuted
  have hinitialContribution :=
    mul_le_mul_of_nonneg_right hcoefficientLe hD0nonneg
  have hinitialNormalized :
      ((SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) *
          LALM.StochasticRun.initialStepBound h params ≤
        LALM.StochasticRun.initialStepBound h params /
          (2 * LALM.StochasticRun.errorStepConstant h params) := by
    calc
      ((SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 /
          (SPIDER.innerBatchSize h oracle params K : ℝ)) *
          LALM.StochasticRun.initialStepBound h params ≤
          ((1 : ℝ) / 2) /
              LALM.StochasticRun.errorStepConstant h params *
            LALM.StochasticRun.initialStepBound h params := hinitialContribution
      _ = LALM.StochasticRun.initialStepBound h params /
          (2 * LALM.StochasticRun.errorStepConstant h params) := by
        field_simp [hDzero]
  have hbound :
      stoppedGradientErrorEnergy attempt ≤
        (oracle.noiseLevel : ℝ) ^ 2 +
          LALM.StochasticRun.initialStepBound h params /
            (2 * LALM.StochasticRun.errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy attempt := by
    calc
      stoppedGradientErrorEnergy attempt ≤
          (oracle.noiseLevel : ℝ) ^ 2 +
            ((SPIDER.refreshPeriod K : ℝ) *
              (oracle.meanSquareLipschitz : ℝ) ^ 2 /
                (SPIDER.innerBatchSize h oracle params K : ℝ)) *
              (LALM.StochasticRun.initialStepBound h params +
                LALM.StochasticRun.errorStepConstant h params *
                  stoppedGradientErrorEnergy attempt) := hcombined
      _ = (oracle.noiseLevel : ℝ) ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) *
            (oracle.meanSquareLipschitz : ℝ) ^ 2 /
              (SPIDER.innerBatchSize h oracle params K : ℝ)) *
            LALM.StochasticRun.initialStepBound h params +
          (((SPIDER.refreshPeriod K : ℝ) *
            (oracle.meanSquareLipschitz : ℝ) ^ 2 /
              (SPIDER.innerBatchSize h oracle params K : ℝ)) *
              LALM.StochasticRun.errorStepConstant h params) *
            stoppedGradientErrorEnergy attempt := by
        ring
      _ ≤ (oracle.noiseLevel : ℝ) ^ 2 +
          LALM.StochasticRun.initialStepBound h params /
            (2 * LALM.StochasticRun.errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy attempt :=
        add_le_add (add_le_add (le_refl _) hinitialNormalized) habsorbError
  have hinitialDouble :
      2 * (LALM.StochasticRun.initialStepBound h params /
        (2 * LALM.StochasticRun.errorStepConstant h params)) =
        LALM.StochasticRun.initialStepBound h params /
          LALM.StochasticRun.errorStepConstant h params := by
    field_simp [hDzero]
  have herrorBound :
      stoppedGradientErrorEnergy attempt ≤
        LALM.StochasticRun.errorAverageConstant h oracle params := by
    rw [LALM.StochasticRun.errorAverageConstant_def]
    linarith [hbound, hinitialDouble]
  have hstepBound :
      stoppedBaseStepEnergy attempt ≤
        LALM.StochasticRun.stepAverageConstant h oracle params := by
    calc
      stoppedBaseStepEnergy attempt ≤
          LALM.StochasticRun.initialStepBound h params +
            LALM.StochasticRun.errorStepConstant h params *
              stoppedGradientErrorEnergy attempt := hsteps
      _ ≤ LALM.StochasticRun.initialStepBound h params +
          LALM.StochasticRun.errorStepConstant h params *
            LALM.StochasticRun.errorAverageConstant h oracle params :=
        add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left herrorBound hDpos.le)
      _ = LALM.StochasticRun.stepAverageConstant h oracle params := by
        rw [LALM.StochasticRun.errorAverageConstant_def,
          LALM.StochasticRun.stepAverageConstant_def]
        field_simp [hDzero]
        ring
  exact ⟨herrorBound, hstepBound⟩

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
