/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedLocalization
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedLocalization

public section

open MeasureTheory
open scoped ENNReal NNReal

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
variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
  confidence K X}

open LALM.StochasticRun.Localization

/-- Helper for Theorem 3.7: the retained endpoint of a failed finite stopped
attempt, indexed by the proof that the first exit occurs by the horizon. -/
noncomputable def firstExitPointOfFailure
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    EuclideanSpace ℝ (Fin n) :=
  attempt.point
    ⟨StoppedAttempt.firstExitEndpoint attempt omega,
      Nat.lt_succ_iff.mpr
        ((StoppedAttempt.not_mem_successEvent_iff_firstExitEndpoint_le
          attempt omega).mp hfailure)⟩ omega

/-- Helper for Theorem 3.7: the failed endpoint retained by the stopped state
is outside the localization set. -/
theorem firstExitPointOfFailure_not_mem
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    firstExitPointOfFailure attempt omega hfailure ∉ X := by
  exact firstExitEndpoint_point_not_mem_of_failure_canonical
    attempt omega hfailure

/-- Helper for Theorem 3.7: the active-prefix multiplier invariant gives the
TeX feasibility bound at the retained first-exit endpoint. -/
theorem firstExitPointOfFailure_constraint_norm_le
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt)
    (omega : Ω) (hfailure : omega ∉ attempt.successEvent) :
    ‖c (firstExitPointOfFailure attempt omega hfailure)‖ ≤
      2 * (params.multiplierBound : ℝ) / params.rho := by
  have hproduct := firstExitEndpoint_constraint_norm_le
    attempt invariant omega hfailure
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  apply (le_div_iff₀ hrho).2
  simpa only [firstExitPointOfFailure, mul_comm] using hproduct

/-- Helper for Theorem 3.7: localization of the initial point makes the
initial-potential gap nonnegative. -/
theorem initialPotentialGap_nonneg_of_stoppedAttempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) :
    0 ≤ LALM.initialPotentialBound h params -
      LALM.lyapunovLowerBound h params := by
  have hx₀ : x₀ ∈ h.region :=
    attempt.region_condition.thickening_subset
      (Metric.self_subset_cthickening X attempt.initial_mem)
  have hobjective : h.objectiveLower ≤ f x₀ :=
    h.objectiveLower_le x₀ hx₀
  have hmultiplierConstant :
      0 ≤ LALM.multiplierPrimalConstant h params.delta params.beta params.rho
        params.multiplierBound := by
    rw [LALM.multiplierPrimalConstant_def]
    positivity
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hgradientTerm :
      0 ≤ (h.gradientBound : ℝ) * params.delta := by positivity
  have hmultiplierTerm :
      0 ≤ 4 * (params.multiplierBound : ℝ) ^ 2 / params.rho := by
    positivity
  have hcorrectionTerm :
      0 ≤ (LALM.multiplierPrimalConstant h params.delta params.beta params.rho
          params.multiplierBound / params.rho) * (params.delta : ℝ) ^ 2 :=
    mul_nonneg (div_nonneg hmultiplierConstant hrho.le) (sq_nonneg _)
  have hlowerCorrection :
      0 ≤ (params.multiplierBound : ℝ) ^ 2 / (2 * params.rho) := by
    positivity
  rw [LALM.initialPotentialBound_def, LALM.lyapunovLowerBound_def]
  linarith

/-- Helper for Theorem 3.7: the finite stopped localization hypotheses make
the canonical initial step allowance strictly positive. -/
theorem initialStepBound_pos_of_stoppedAttempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) :
    0 < LALM.StochasticRun.initialStepBound h params := by
  have hgap := initialPotentialGap_nonneg_of_stoppedAttempt attempt
  have hdelta : 0 < (params.delta : ℝ) := params.spec.1.1
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  rw [LALM.StochasticRun.initialStepBound_def]
  positivity

/-- Helper for Theorem 3.7: the finite stopped localization hypotheses make
the scheduled estimator-error allowance strictly positive. -/
theorem errorAverageConstant_pos_of_stoppedAttempt
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b
      confidence K X) :
    0 < LALM.StochasticRun.errorAverageConstant h oracle params := by
  have hinitial := initialStepBound_pos_of_stoppedAttempt attempt
  have hcoefficient := errorStepConstant_pos h params
  rw [LALM.StochasticRun.errorAverageConstant_def]
  positivity

/-- Helper for Theorem 3.7: the coefficient in the stopped objective bound is
strictly positive. -/
theorem lyapunovErrorConstant_pos
    (h : EqualityConstrained.Regularity f c)
    (params : LALM.Parameters h x₀ multiplier₀) :
    0 < LALM.StochasticRun.lyapunovErrorConstant h params := by
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hrho : 0 < (params.rho : ℝ) := params.spec.1.2.2.1
  have hmultiplierError : 0 ≤ LALM.multiplierErrorConstant h := by
    rw [LALM.multiplierErrorConstant_def]
    positivity
  rw [LALM.StochasticRun.lyapunovErrorConstant_def]
  positivity

/-- Theorem 3.7: the remaining pathwise objective estimate at a first exit.
All objects in this interface are projections of the actual finite stopped
attempt; it is the finite counterpart of the Lyapunov completion-of-squares
line in the TeX proof. -/
structure FiniteStoppedObjectiveExitBound
    (path : FiniteStoppedPath attempt) where
  /-- At a failed endpoint, the objective is controlled by deterministic
  potential and the actual stopped estimator-error energy. -/
  objective_le :
    ∀ (omega : Ω) (hfailure : omega ∉ attempt.successEvent),
      f (firstExitPointOfFailure attempt omega hfailure) ≤
        LALM.deterministicObjectiveBound h params +
          2 * LALM.StochasticRun.lyapunovErrorConstant h params *
            pathwiseGradientErrorEnergy attempt omega

/-- Theorem 3.7: the actual failed-endpoint feasibility bound, stochastic
sublevel containment, and objective estimate construct the TeX exit-energy
threshold `Γe / confidence`. -/
theorem finiteStoppedExitControl_exists_of_objectiveExitBound
    (path : FiniteStoppedPath attempt)
    (objective : FiniteStoppedObjectiveExitBound path)
    (confidence_pos : 0 < confidence) :
    ∃ control : FiniteStoppedExitControl path,
      control.threshold =
        LALM.StochasticRun.errorAverageConstant h oracle params /
          confidence := by
  have herrorPos :
      0 < LALM.StochasticRun.errorAverageConstant h oracle params :=
    errorAverageConstant_pos_of_stoppedAttempt attempt
  have hexit : ∀ omega, omega ∉ attempt.successEvent →
      LALM.StochasticRun.errorAverageConstant h oracle params / confidence <
        pathwiseGradientErrorEnergy attempt omega := by
    intro omega hfailure
    have houtside := firstExitPointOfFailure_not_mem attempt omega hfailure
    have hconstraint := firstExitPointOfFailure_constraint_norm_le
      attempt path.invariant omega hfailure
    have hobjectiveUpper := objective.objective_le omega hfailure
    have hobjectiveLower :
        objectiveBound h oracle params confidence <
          f (firstExitPointOfFailure attempt omega hfailure) := by
      apply lt_of_not_ge
      intro hobjective
      apply houtside
      apply attempt.region_condition.sublevel_subset
      exact (mem_sublevel h oracle params confidence _).2
        ⟨hobjective, hconstraint⟩
    have hcoefficientPos :
        0 < LALM.StochasticRun.lyapunovErrorConstant h params :=
      lyapunovErrorConstant_pos h params
    rw [objectiveBound_def] at hobjectiveLower
    have hnormalizeErrorThreshold :
        2 * LALM.StochasticRun.lyapunovErrorConstant h params *
            LALM.StochasticRun.errorAverageConstant h oracle params / confidence =
          2 * LALM.StochasticRun.lyapunovErrorConstant h params *
            (LALM.StochasticRun.errorAverageConstant h oracle params /
              confidence) := by
      ring
    rw [hnormalizeErrorThreshold] at hobjectiveLower
    nlinarith
  let control : FiniteStoppedExitControl path := {
    threshold := LALM.StochasticRun.errorAverageConstant h oracle params /
      confidence
    threshold_pos := div_pos herrorPos confidence_pos
    exit_implies_energy_gt := hexit
  }
  exact ⟨control, rfl⟩

/-- Theorem 3.7: under the actual first-exit geometry, the prescribed finite
stopped schedule survives through the horizon with probability at least
`1 - confidence`. -/
theorem finiteStoppedScheduledSuccessProbability_of_objectiveExitBound
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (path : FiniteStoppedPath attempt)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (budget_eq : path.baseStepBudget =
      LALM.StochasticRun.initialStepBound h params)
    (coefficient_eq : path.errorStepCoefficient =
      LALM.StochasticRun.errorStepConstant h params)
    (objective : FiniteStoppedObjectiveExitBound path) :
    ENNReal.ofReal (1 - confidence) ≤ P (attempt.successEvent) := by
  obtain ⟨control, hthreshold⟩ :=
    finiteStoppedExitControl_exists_of_objectiveExitBound
      path objective confidence_pos
  exact finiteStoppedScheduledSuccessProbability attempt hK confidence_pos
    path recursion budget_eq coefficient_eq control hthreshold

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
