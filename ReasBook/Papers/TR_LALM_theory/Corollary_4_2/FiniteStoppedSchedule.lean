/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedAttempt
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedPath
public import TR_LALM_theory.Corollary_4_2.ScheduleCertificate
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedPath
import all TR_LALM_theory.Corollary_4_2.ScheduleCertificate

public section

open MeasureTheory
open scoped NNReal

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

variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Corollary 4.2: the prescribed finite SPIDER schedule bounds the stopped
estimator-error and base-step energies by `Γe` and `Γp`, respectively. -/
theorem finiteStoppedScheduledEnergyBounds
    (attempt : SPIDER.Correction.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (path : FiniteStoppedPath attempt)
    (hbudget : path.baseStepBudget = initialStepBound h params)
    (hcoefficient : path.errorStepCoefficient = errorStepConstant h params) :
    stoppedGradientErrorEnergy attempt ≤ errorAverageConstant h oracle params ∧
      stoppedBaseStepEnergy attempt ≤ stepAverageConstant h oracle params := by
  have hsteps :
      stoppedBaseStepEnergy attempt ≤
        initialStepBound h params + errorStepConstant h params *
          stoppedGradientErrorEnergy attempt := by
    simpa only [hbudget, hcoefficient] using path.baseStepEnergy_le
  have herrors := stoppedGradientErrorEnergy_le_scaledBaseStepEnergy attempt
  rw [SPIDER.refreshBatchSize_coe K hK] at herrors
  have hKreal : 0 < (K : ℝ) := by
    positivity
  have hKzero : (K : ℝ) ≠ 0 := hKreal.ne'
  have hvariance :
      (K : ℝ) * (oracle.noiseLevel : ℝ) ^ 2 / K =
        (oracle.noiseLevel : ℝ) ^ 2 := by
    field_simp [hKzero]
  rw [hvariance] at herrors
  have hDpos : 0 < errorStepConstant h params :=
    errorStepConstant_pos h params
  have hDzero : errorStepConstant h params ≠ 0 := hDpos.ne'
  have hD0nonneg : 0 ≤ initialStepBound h params := by
    rw [← hbudget]
    exact path.baseStepBudget_nonneg
  have herrorNonneg := stoppedGradientErrorEnergy_nonneg attempt
  have hcoefficientNonneg :
      0 ≤ (SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ) := by
    positivity
  have hstepsScaled :=
    mul_le_mul_of_nonneg_left hsteps hcoefficientNonneg
  have hcombined :
      stoppedGradientErrorEnergy attempt ≤
        (oracle.noiseLevel : ℝ) ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) *
            (oracle.meanSquareLipschitz : ℝ) ^ 2 *
              displacementFactor h params.delta ^ 2 /
                (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
            (initialStepBound h params + errorStepConstant h params *
              stoppedGradientErrorEnergy attempt) :=
    herrors.trans (add_le_add (le_refl _) hstepsScaled)
  have habsorb := SPIDER.Correction.scheduledErrorStepCoefficient_le_half
    h oracle params K
  have habsorbCommuted :
      ((SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
          errorStepConstant h params ≤ (1 : ℝ) / 2 := by
    simpa only [mul_comm] using habsorb
  have habsorbError :=
    mul_le_mul_of_nonneg_right habsorbCommuted herrorNonneg
  have hcoefficientLe :
      (SPIDER.refreshPeriod K : ℝ) *
          (oracle.meanSquareLipschitz : ℝ) ^ 2 *
            displacementFactor h params.delta ^ 2 /
              (SPIDER.Correction.innerBatchSize h oracle params K : ℝ) ≤
        ((1 : ℝ) / 2) / errorStepConstant h params :=
    (le_div_iff₀ hDpos).2 habsorbCommuted
  have hinitialContribution :=
    mul_le_mul_of_nonneg_right hcoefficientLe hD0nonneg
  have hinitialNormalized :
      ((SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
          initialStepBound h params ≤
        initialStepBound h params / (2 * errorStepConstant h params) := by
    calc
      ((SPIDER.refreshPeriod K : ℝ) *
        (oracle.meanSquareLipschitz : ℝ) ^ 2 *
          displacementFactor h params.delta ^ 2 /
            (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
          initialStepBound h params ≤
          ((1 : ℝ) / 2) / errorStepConstant h params *
            initialStepBound h params := hinitialContribution
      _ = initialStepBound h params / (2 * errorStepConstant h params) := by
        field_simp [hDzero]
  have hbound :
      stoppedGradientErrorEnergy attempt ≤
        (oracle.noiseLevel : ℝ) ^ 2 +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy attempt := by
    calc
      stoppedGradientErrorEnergy attempt ≤
          (oracle.noiseLevel : ℝ) ^ 2 +
            ((SPIDER.refreshPeriod K : ℝ) *
              (oracle.meanSquareLipschitz : ℝ) ^ 2 *
                displacementFactor h params.delta ^ 2 /
                  (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
              (initialStepBound h params + errorStepConstant h params *
                stoppedGradientErrorEnergy attempt) := hcombined
      _ = (oracle.noiseLevel : ℝ) ^ 2 +
          ((SPIDER.refreshPeriod K : ℝ) *
            (oracle.meanSquareLipschitz : ℝ) ^ 2 *
              displacementFactor h params.delta ^ 2 /
                (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
            initialStepBound h params +
          (((SPIDER.refreshPeriod K : ℝ) *
            (oracle.meanSquareLipschitz : ℝ) ^ 2 *
              displacementFactor h params.delta ^ 2 /
                (SPIDER.Correction.innerBatchSize h oracle params K : ℝ)) *
              errorStepConstant h params) * stoppedGradientErrorEnergy attempt := by
        ring
      _ ≤ (oracle.noiseLevel : ℝ) ^ 2 +
          initialStepBound h params / (2 * errorStepConstant h params) +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy attempt :=
        add_le_add (add_le_add (le_refl _) hinitialNormalized) habsorbError
  have hinitialDouble :
      2 * (initialStepBound h params / (2 * errorStepConstant h params)) =
        initialStepBound h params / errorStepConstant h params := by
    field_simp [hDzero]
  have herrorBound :
      stoppedGradientErrorEnergy attempt ≤
        errorAverageConstant h oracle params := by
    rw [errorAverageConstant_def]
    linarith [hbound, hinitialDouble]
  have hstepBound :
      stoppedBaseStepEnergy attempt ≤ stepAverageConstant h oracle params := by
    calc
      stoppedBaseStepEnergy attempt ≤
          initialStepBound h params + errorStepConstant h params *
            stoppedGradientErrorEnergy attempt := hsteps
      _ ≤ initialStepBound h params +
          errorStepConstant h params * errorAverageConstant h oracle params :=
        add_le_add (le_refl _)
          (mul_le_mul_of_nonneg_left herrorBound hDpos.le)
      _ = stepAverageConstant h oracle params := by
        rw [errorAverageConstant_def, stepAverageConstant_def]
        field_simp [hDzero]
        ring
  exact ⟨herrorBound, hstepBound⟩

end StoppedAttemptAnalysis

end LALM.Correction

end
