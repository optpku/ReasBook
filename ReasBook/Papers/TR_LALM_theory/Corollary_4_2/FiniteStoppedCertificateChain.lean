/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.FiniteStoppedLocalization
public import TR_LALM_theory.Corollary_4_2.FiniteStoppedCertificate
public import TR_LALM_theory.Corollary_4_2.CanonicalStoppedCertificate
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedLocalization
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedCertificate

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

variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Corollary 4.2: the finite scheduled energy estimate, finite exit geometry,
and success-restricted residual estimate together produce a stopped-attempt
certificate, without an infinite `ScheduledRun`. -/
theorem finiteStoppedScheduledCertificate_exists
    (attempt : SPIDER.Correction.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (path : FiniteStoppedPath attempt)
    (budget_eq : path.baseStepBudget = initialStepBound h params)
    (coefficient_eq : path.errorStepCoefficient = errorStepConstant h params)
    (control : FiniteStoppedExitControl attempt)
    (threshold_eq : control.threshold =
      errorAverageConstant h oracle params / confidence)
    (residualNumeratorBound : ℝ)
    (residualNumerator_le : successRestrictedResidualNumerator attempt hK ≤
      ENNReal.ofReal (residualNumeratorBound / ((K : ℝ) - 1))) :
    ∃ certificate : StoppedAttemptCertificate attempt hK,
      certificate.residualPerSuccessBound =
        normalizedResidualScale residualNumeratorBound confidence K := by
  have hprobability := finiteStoppedScheduledSuccessProbability attempt hK
    confidence_pos path budget_eq coefficient_eq control threshold_eq
  exact certificate_exists_of_successProbability_and_residual attempt hK
    confidence_lt_one hprobability residualNumeratorBound residualNumerator_le

/-- Corollary 4.2: the finite stopped certificate specializes to the source
`stochasticComplexityConstant` numerator and the existing source residual-scale
definition. -/
theorem finiteStoppedScheduledSourceCertificate_exists
    (attempt : SPIDER.Correction.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (path : FiniteStoppedPath attempt)
    (budget_eq : path.baseStepBudget = initialStepBound h params)
    (coefficient_eq : path.errorStepCoefficient = errorStepConstant h params)
    (control : FiniteStoppedExitControl attempt)
    (threshold_eq : control.threshold =
      errorAverageConstant h oracle params / confidence)
    (residualNumerator_le : successRestrictedResidualNumerator attempt hK ≤
      ENNReal.ofReal
        (stochasticComplexityConstant h oracle params / ((K : ℝ) - 1))) :
    ∃ certificate : StoppedAttemptCertificate attempt hK,
      certificate.residualPerSuccessBound =
        CanonicalStoppedCertificate.stoppedResidualPerSuccessBound
          (h := h) (oracle := oracle) (params := params) confidence K := by
  obtain ⟨certificate, certificate_scale⟩ :=
    finiteStoppedScheduledCertificate_exists attempt hK confidence_pos
      confidence_lt_one path budget_eq coefficient_eq control threshold_eq
      (stochasticComplexityConstant h oracle params) residualNumerator_le
  refine ⟨certificate, ?_⟩
  calc
    certificate.residualPerSuccessBound =
        normalizedResidualScale (stochasticComplexityConstant h oracle params)
          confidence K := certificate_scale
    _ = CanonicalStoppedCertificate.stoppedResidualPerSuccessBound
          (h := h) (oracle := oracle) (params := params) confidence K := by
      apply ENNReal.coe_injective
      rw [coe_normalizedResidualScale,
        CanonicalStoppedCertificate.coe_stoppedResidualPerSuccessBound]

end StoppedAttemptAnalysis

namespace CanonicalStoppedRestart

open StoppedAttemptAnalysis

variable {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}

/-- Corollary 4.2: finite path, exit, and residual estimates for one canonical
base attempt yield a certified canonical stopped restart, and every restart
copy retains the normalized residual scale of the base certificate. -/
theorem finiteStoppedScheduledCertifiedRestart_exists
    (base : SPIDER.Correction.StoppedScheduledAttempt h oracle
      (canonicalProductMeasure ν) x₀ multiplier₀ params confidence K X)
    (hK : 2 ≤ K) (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (path : FiniteStoppedPath base)
    (budget_eq : path.baseStepBudget = initialStepBound h params)
    (coefficient_eq : path.errorStepCoefficient = errorStepConstant h params)
    (control : FiniteStoppedExitControl base)
    (threshold_eq : control.threshold =
      errorAverageConstant h oracle params / confidence)
    (residualNumeratorBound : ℝ)
    (residualNumerator_le : successRestrictedResidualNumerator base hK ≤
      ENNReal.ofReal (residualNumeratorBound / ((K : ℝ) - 1))) :
    ∃ certified : CertifiedStoppedSafeguardedRestart (h := h) (oracle := oracle)
        (ℙ := canonicalStoppedRestartMeasure ν K hK) (x₀ := x₀)
        (multiplier₀ := multiplier₀) (params := params)
        (confidence := confidence) (K := K) (hK := hK) (X := X),
      ∀ i, (certified.certificate i).residualPerSuccessBound =
        normalizedResidualScale residualNumeratorBound confidence K := by
  obtain ⟨certificate, certificate_scale⟩ :=
    finiteStoppedScheduledCertificate_exists base hK confidence_pos
      confidence_lt_one path budget_eq coefficient_eq control threshold_eq
      residualNumeratorBound residualNumerator_le
  let certified := certifiedStoppedSafeguardedRestart_of_base
    (hK := hK) base certificate
  refine ⟨certified, ?_⟩
  intro i
  calc
    (certified.certificate i).residualPerSuccessBound =
        certificate.residualPerSuccessBound := by
      exact certifiedStoppedSafeguardedRestart_of_base_residualPerSuccessBound
        base certificate i
    _ = normalizedResidualScale residualNumeratorBound confidence K :=
      certificate_scale

end CanonicalStoppedRestart

end LALM.Correction

end
