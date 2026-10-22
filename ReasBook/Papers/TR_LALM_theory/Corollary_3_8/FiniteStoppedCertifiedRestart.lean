/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartAccounting
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedRestartAccounting

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LALM.FiniteStopped

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
variable {X : Set (EuclideanSpace ℝ (Fin n))} {hK : 2 ≤ K}

open StoppedAttemptAnalysis

/-- Corollary 3.8: a certified finite stopped restart consists of the restart
law and the canonical finite analytic certificate attached to each attempt. -/
structure CertifiedStoppedSafeguardedRestart where
  /-- The countable family of finite stopped attempts and uniform selectors. -/
  restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
    (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
    (confidence := confidence) (K := K) (hK := hK) (X := X)
  /-- The finite success and residual certificate of each attempt. -/
  certificate : ∀ i,
    FiniteStoppedCanonicalCertificate (restart.attempt i) hK

namespace CertifiedStoppedSafeguardedRestart

/-- Corollary 3.8: package a stopped restart with an explicit family of finite
canonical attempt certificates. -/
def ofRestart
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (certificate : ∀ i,
      FiniteStoppedCanonicalCertificate (restart.attempt i) hK) :
    CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  { restart, certificate }

/-- Helper for Corollary 3.8: choose the source-shaped certificate supplied by
the canonical finite stopped analysis for one attempt. -/
noncomputable def canonicalAttemptCertificate
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) :
    FiniteStoppedCanonicalCertificate attempt hK :=
  Classical.choose
    (finiteStoppedCanonicalSourceCertificate_exists_of_canonicalAttempt
      attempt hK confidence_pos confidence_lt_one)

/-- Helper for Corollary 3.8: the chosen canonical certificate has exactly the
residual scale stated in the article. -/
theorem canonicalAttemptCertificate_residualPerSuccessBound
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) :
    FiniteStoppedCanonicalCertificate.residualPerSuccessBound
        (canonicalAttemptCertificate attempt hK confidence_pos
          confidence_lt_one) =
      Real.toNNReal
        (LALM.StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) :=
  Classical.choose_spec
    (finiteStoppedCanonicalSourceCertificate_exists_of_canonicalAttempt
      attempt hK confidence_pos confidence_lt_one)

/-- Corollary 3.8: every stopped restart built from canonical finite attempts
is automatically certified under the article's numerical conditions. -/
noncomputable def canonical
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X) :=
  { restart
    certificate := fun i ↦ canonicalAttemptCertificate (restart.attempt i) hK
      confidence_pos confidence_lt_one }

/-- Corollary 3.8: every certificate in the canonical stopped restart carries
the source residual scale. -/
theorem canonical_certificate_residualPerSuccessBound
    (restart : StoppedSafeguardedRestart (h := h) (oracle := oracle) (P := P)
      (x₀ := x₀) (multiplier₀ := multiplier₀) (params := params)
      (confidence := confidence) (K := K) (hK := hK) (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (i : ℕ) :
    FiniteStoppedCanonicalCertificate.residualPerSuccessBound
        ((canonical restart confidence_pos confidence_lt_one).certificate i) =
      Real.toNNReal
        (LALM.StochasticRun.complexityConstant h oracle params /
          ((1 - confidence) * ((K : ℝ) - 1))) :=
  canonicalAttemptCertificate_residualPerSuccessBound
    (restart.attempt i) hK confidence_pos confidence_lt_one

/-- Helper for Corollary 3.8: retrieve the finite certificate attached to one
restart attempt. -/
def attemptCertificate
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X)) (i : ℕ) :
    FiniteStoppedCanonicalCertificate (certified.restart.attempt i) hK :=
  certified.certificate i

/-- Helper for Corollary 3.8: each certified finite attempt succeeds with
probability at least `1 - confidence`. -/
theorem attempt_successProbability_lower
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X)) (i : ℕ) :
    ENNReal.ofReal (1 - confidence) ≤
      P (StoppedSafeguardedRestart.successEvent certified.restart i) :=
  (certified.certificate i).successProbability_lower

/-- Helper for Corollary 3.8: each certified attempt controls the genuine
success-restricted residual under its independent uniform output law. -/
theorem attempt_uniformSuccessResidualNumerator_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X)) (i : ℕ) :
    canonicalUniformSuccessResidualNumerator (certified.restart.attempt i) hK ≤
      P (StoppedSafeguardedRestart.successEvent certified.restart i) *
        ((certified.certificate i).residualPerSuccessBound : ℝ≥0∞) :=
  (certified.certificate i).uniformSuccessResidualNumerator_le
    (finiteStoppedPrefixInvariant (certified.restart.attempt i))

/-- Corollary 3.8: certified finite attempts yield the geometric tail bound
for the one-based restart count. -/
theorem attemptCount_tail_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1)
    (t : ℕ) :
    P {omega | (t : ℕ∞) <
      StoppedSafeguardedRestart.attemptCount certified.restart omega} ≤
      ENNReal.ofReal confidence ^ t :=
  StoppedSafeguardedRestart.attemptCount_tail_le certified.restart
    confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i) t

/-- Corollary 3.8: a certified finite stopped restart terminates almost surely. -/
theorem terminatesAE
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∀ᵐ omega ∂P,
      StoppedSafeguardedRestart.firstAccepted certified.restart omega ≠ ⊤ :=
  StoppedSafeguardedRestart.terminatesAE certified.restart confidence_pos
    confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: the expected number of certified finite attempts is at most
`1 / (1 - confidence)`. -/
theorem expectedAttemptCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.attemptCount certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (1 / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedAttemptCount_le certified.restart
    confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: expected active transitions of a certified restart are at
most `K / (1 - confidence)`. -/
theorem expectedTotalIterations_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.totalIterations certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedTotalIterations_le certified.restart
    confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: expected stochastic-gradient work of a certified restart
satisfies the exact SPIDER bound in the article. -/
theorem expectedGradientEvaluationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.gradientEvaluationCount
          certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal (((
        (K ⌈/⌉ (SPIDER.refreshPeriod K : ℕ)) *
            (SPIDER.refreshBatchSize K : ℕ) +
          2 * K * (SPIDER.innerBatchSize h oracle params K : ℕ) : ℕ) : ℝ) /
        (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedGradientEvaluationCount_le
    certified.restart confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: expected deterministic constraint evaluations are bounded
by the active-transition budget. -/
theorem expectedConstraintEvaluationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.constraintEvaluationCount
          certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedConstraintEvaluationCount_le
    certified.restart confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: expected deterministic Jacobian evaluations are bounded by
the active-transition budget. -/
theorem expectedJacobianEvaluationCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.jacobianEvaluationCount
          certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedJacobianEvaluationCount_le
    certified.restart confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: expected exact base linear-system solves are bounded by the
active-transition budget. -/
theorem expectedLinearSystemSolveCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.linearSystemSolveCount
          certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedLinearSystemSolveCount_le
    certified.restart confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

/-- Corollary 3.8: expected exact-real localization membership tests are
bounded by the active-transition budget. -/
theorem expectedMembershipTestCount_le
    (certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
      (P := P) (x₀ := x₀) (multiplier₀ := multiplier₀)
      (params := params) (confidence := confidence) (K := K) (hK := hK)
      (X := X))
    (confidence_pos : 0 < confidence) (confidence_lt_one : confidence < 1) :
    ∫⁻ omega,
        (StoppedSafeguardedRestart.membershipTestCount
          certified.restart omega : ℝ≥0∞) ∂P ≤
      ENNReal.ofReal ((K : ℝ) / (1 - confidence)) :=
  StoppedSafeguardedRestart.expectedMembershipTestCount_le
    certified.restart confidence_pos confidence_lt_one
    (fun i ↦ certified.attempt_successProbability_lower i)

end CertifiedStoppedSafeguardedRestart

end LALM.FiniteStopped

end
