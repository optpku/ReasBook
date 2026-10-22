/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.FiniteStoppedSchedule
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedSchedule

public section

open MeasureTheory
open scoped ENNReal NNReal

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

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}

/-- Helper for Corollary 4.2: a confidence-scaled finite exit threshold and an
error-energy budget bound the probability of finite stopped failure. -/
theorem FiniteStoppedExitControl.failureProbability_le
    (control : FiniteStoppedExitControl attempt)
    (budget : ℝ) (confidence_pos : 0 < confidence)
    (threshold_eq : control.threshold = budget / confidence)
    (energy_le : stoppedGradientErrorEnergy attempt ≤ budget) :
    P (successEvent attempt)ᶜ ≤ ENNReal.ofReal confidence := by
  have hproduct :
      ENNReal.ofReal control.threshold * P (successEvent attempt)ᶜ ≤
        ENNReal.ofReal budget := by
    exact control.complement_mul_le.trans (ENNReal.ofReal_le_ofReal energy_le)
  have hthresholdNeZero : ENNReal.ofReal control.threshold ≠ 0 :=
    (ENNReal.ofReal_ne_zero_iff).2 control.threshold_pos
  have hthresholdNeTop : ENNReal.ofReal control.threshold ≠ ⊤ :=
    ENNReal.ofReal_ne_top
  apply (ENNReal.mul_le_mul_iff_left hthresholdNeZero hthresholdNeTop).mp
  calc
    P (successEvent attempt)ᶜ * ENNReal.ofReal control.threshold =
        ENNReal.ofReal control.threshold * P (successEvent attempt)ᶜ := mul_comm _ _
    _ ≤ ENNReal.ofReal budget := hproduct
    _ = ENNReal.ofReal confidence * ENNReal.ofReal control.threshold := by
      rw [mul_comm, threshold_eq, ENNReal.ofReal_div_of_pos confidence_pos,
        ENNReal.div_mul_cancel
          ((ENNReal.ofReal_ne_zero_iff).2 confidence_pos) ENNReal.ofReal_ne_top]

/-- Corollary 4.2: a confidence-scaled finite exit threshold and an
error-energy budget give the source success-probability lower bound. -/
theorem FiniteStoppedExitControl.successProbability_lower
    (control : FiniteStoppedExitControl attempt)
    (budget : ℝ) (confidence_pos : 0 < confidence)
    (threshold_eq : control.threshold = budget / confidence)
    (energy_le : stoppedGradientErrorEnergy attempt ≤ budget) :
    ENNReal.ofReal (1 - confidence) ≤ P (successEvent attempt) := by
  have hfailure := control.failureProbability_le budget confidence_pos
    threshold_eq energy_le
  have hsuccess :
      P (successEvent attempt) = 1 - P (successEvent attempt)ᶜ := by
    have hcomplement := prob_compl_eq_one_sub₀ (μ := P)
      (measurableSet_successEvent attempt).compl.nullMeasurableSet
    simpa only [compl_compl] using hcomplement
  rw [hsuccess, ENNReal.ofReal_sub 1 confidence_pos.le, ENNReal.ofReal_one]
  exact tsub_le_tsub_left hfailure 1

/-- Corollary 4.2: the prescribed finite stopped schedule and the source exit
threshold imply survival through the finite horizon with probability at least
`1 - confidence`. -/
theorem finiteStoppedScheduledSuccessProbability
    (attempt : SPIDER.Correction.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (path : FiniteStoppedPath attempt)
    (budget_eq : path.baseStepBudget = initialStepBound h params)
    (coefficient_eq : path.errorStepCoefficient = errorStepConstant h params)
    (control : FiniteStoppedExitControl attempt)
    (threshold_eq : control.threshold =
      errorAverageConstant h oracle params / confidence) :
    ENNReal.ofReal (1 - confidence) ≤ P (successEvent attempt) := by
  have henergy :=
    (finiteStoppedScheduledEnergyBounds attempt hK path budget_eq coefficient_eq).1
  exact control.successProbability_lower
    (errorAverageConstant h oracle params) confidence_pos threshold_eq henergy

end StoppedAttemptAnalysis

end LALM.Correction

end
