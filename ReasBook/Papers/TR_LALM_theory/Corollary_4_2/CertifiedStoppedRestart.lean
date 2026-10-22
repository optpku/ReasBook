/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedRestart
public import TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis
public import TR_LALM_theory.Corollary_4_2.StoppedRestartAccounting

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.Correction

universe u v

variable {n m : ℕ}
variable {Ξ : Type u} [MeasurableSpace Ξ] {ν : Measure Ξ} [IsProbabilityMeasure ν]
variable {Ω : Type v} [MeasurableSpace Ω] {ℙ : Measure Ω} [IsProbabilityMeasure ℙ]
variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {h : EqualityConstrained.Regularity f c}
variable {oracle : EqualityConstrained.StochasticOracle f h.region ν}
variable {params : Parameters h x₀ multiplier₀}
variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

open StoppedAttemptAnalysis

/-- Corollary 4.2: a certified stopped safeguarded restart consists of the
finite absorbing restart interface together with one finite analytic
certificate for every attempt. -/
structure CertifiedStoppedSafeguardedRestart where
  /-- The finite absorbing restart whose attempts and selectors are independent. -/
  restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
    (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
    (confidence := confidence) (K := K) (hK := hK) (X := X)
  /-- The finite analytic certificate attached to each stopped attempt. -/
  certificate : ∀ i,
    StoppedAttemptCertificate (restart.attempt i) hK

namespace CertifiedStoppedSafeguardedRestart

/-- Corollary 4.2: package an existing stopped restart with a uniform family of
finite attempt certificates. -/
def ofRestart
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (certificate : ∀ i, StoppedAttemptCertificate (restart.attempt i) hK) :
    CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle) (ℙ := ℙ)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  { restart, certificate }

/-- Helper for Corollary 4.2: retrieve the finite certificate for one restart
attempt without exposing the structure constructor. -/
def attemptCertificate
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (i : ℕ) :
    StoppedAttemptCertificate (certified.restart.attempt i) hK :=
  certified.certificate i

/-- Helper for Corollary 4.2: the attached certificate supplies the finite
success probability bound in its native stopped-attempt event. -/
theorem attempt_successProbability_lower_analysis
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (i : ℕ) :
    ENNReal.ofReal (1 - confidence) ≤
      ℙ (StoppedAttemptAnalysis.successEvent (certified.restart.attempt i)) :=
  (certified.certificate i).successProbability_lower

/-- Helper for Corollary 4.2: the analysis success event and the restart
success event have the same probability. -/
theorem attempt_successProbability_lower
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (i : ℕ) :
    ENNReal.ofReal (1 - confidence) ≤
      ℙ (StoppedSafeguardedRestart.successEvent certified.restart i) := by
  rw [StoppedSafeguardedRestart.successEvent_eq_attempt_success certified.restart i]
  rw [← StoppedAttemptAnalysis.successEvent_eq_stoppedAttempt]
  exact certified.attempt_successProbability_lower_analysis i

/-- Helper for Corollary 4.2: expose the finite stopped residual numerator
bound for one attempt. -/
theorem attempt_restrictedResidual_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X)) (i : ℕ) :
    successRestrictedResidualNumerator (certified.restart.attempt i) hK ≤
      ℙ (StoppedAttemptAnalysis.successEvent (certified.restart.attempt i)) *
        (certified.certificate i).residualPerSuccessBound :=
  (certified.certificate i).successRestrictedResidual_le

/-- Corollary 4.2: a certified stopped restart inherits the geometric tail
bound from its uniform finite success certificates. -/
theorem attemptCount_tail_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) (t : ℕ) :
    ℙ {ω | (t : ℕ∞) <
      StoppedSafeguardedRestart.attemptCount certified.restart ω} ≤
      ENNReal.ofReal confidence ^ t :=
  StoppedSafeguardedRestart.attemptCount_tail_le certified.restart
    confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i) t

/-- Corollary 4.2: a certified stopped restart terminates almost surely. -/
theorem terminatesAE
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∀ᵐ omega ∂ℙ,
      StoppedSafeguardedRestart.firstAccepted certified.restart omega ≠ ⊤ :=
  StoppedSafeguardedRestart.terminatesAE certified.restart confidence_pos
    confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart has the expected geometric
attempt-count bound. -/
theorem expectedAttemptCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.attemptCount certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (1 / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedAttemptCount_le certified.restart
    confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart has expected active-transition
work at most `K / (1 - confidence)`. -/
theorem expectedTotalIterations_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.totalIterations certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedTotalIterations_le certified.restart
    confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart bounds expected constraint
evaluations by the charged stopped-transition budget. -/
theorem expectedConstraintEvaluationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.constraintEvaluationCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((2 * K : ℕ) : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedConstraintEvaluationCount_le
    certified.restart confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart bounds expected Jacobian
evaluations by the charged stopped-transition budget. -/
theorem expectedJacobianEvaluationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.jacobianEvaluationCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((2 * K : ℕ) : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedJacobianEvaluationCount_le
    certified.restart confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart bounds expected primal solves by
the charged stopped-transition budget. -/
theorem expectedPrimalSolveCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.primalSolveCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedPrimalSolveCount_le
    certified.restart confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart bounds expected correction solves
by the charged stopped-transition budget. -/
theorem expectedCorrectionSolveCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.correctionSolveCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedCorrectionSolveCount_le
    certified.restart confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart bounds expected abstract
membership tests by the charged stopped-transition budget. -/
theorem expectedMembershipTestCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.membershipTestCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedMembershipTestCount_le
    certified.restart confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart bounds the aggregate corrected
SOC charge by `7 * K / (1 - confidence)`. -/
theorem expectedSocOperationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.socOperationCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((7 * K : ℕ) : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedSocOperationCount_le certified.restart
    confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 4.2: a certified stopped restart satisfies the exact expected
SPIDER gradient-work bound from the article. -/
theorem expectedGradientEvaluationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (ℙ := ℙ) (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (hX : MeasurableSet X) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.gradientEvaluationCount
          certified.restart omega : ℝ≥0∞) ∂ℙ ≤
      ENNReal.ofReal (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.Correction.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ) /
        (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedGradientEvaluationCount_le
    certified.restart confidence_pos confidence_lt_one hX
    (fun i ↦ certified.attempt_successProbability_lower i)

end CertifiedStoppedSafeguardedRestart

end LALM.Correction

end
