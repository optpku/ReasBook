/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedResidual
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedResidual

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

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

open LALM.FiniteStopped

/-- Theorem 3.7: normalize the finite canonical residual integral by the
uniform output range `1, ..., K - 1`.  This is the unrestricted stopped-prefix
quantity; the certificate below uses its success-restricted counterpart. -/
noncomputable def canonicalResidualNumerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((∫ omega, canonicalPathwiseResidualEnergy attempt omega ∂P) /
      ((K : ℝ) - 1))

/-- Theorem 3.7: normalize only the residual energy on the successful stopped
event. This is the finite analogue of restricting to `attempt.successEvent`
before the uniform output selector is integrated out. -/
noncomputable def canonicalSuccessRestrictedResidualNumerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X) : ℝ≥0∞ :=
  ENNReal.ofReal
    ((∫ omega, attempt.successEvent.indicator
        (canonicalPathwiseResidualEnergy attempt) omega ∂P) /
      ((K : ℝ) - 1))

/-- Helper for Theorem 3.7: success restriction can only decrease the
unrestricted stopped-prefix residual numerator. -/
theorem canonicalSuccessRestrictedResidualNumerator_le
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (hintegrable : Integrable (canonicalPathwiseResidualEnergy attempt) P) :
    canonicalSuccessRestrictedResidualNumerator attempt ≤
      canonicalResidualNumerator attempt := by
  have hKreal : 0 < (K : ℝ) - 1 := by
    have hKnat : 1 < K := by omega
    exact sub_pos.mpr (by exact_mod_cast hKnat)
  have hrestricted : Integrable (attempt.successEvent.indicator
      (canonicalPathwiseResidualEnergy attempt)) P :=
    hintegrable.indicator
      (LALM.FiniteStopped.StoppedAttempt.measurableSet_successEvent attempt)
  have hpoint (omega : Ω) :
      attempt.successEvent.indicator
          (canonicalPathwiseResidualEnergy attempt) omega ≤
        canonicalPathwiseResidualEnergy attempt omega := by
    by_cases hsuccess : omega ∈ attempt.successEvent
    · simp only [Set.indicator_of_mem hsuccess]
      exact le_rfl
    · simp only [Set.indicator_of_notMem hsuccess]
      exact canonicalPathwiseResidualEnergy_nonneg attempt omega
  have hintegral :
      (∫ omega, attempt.successEvent.indicator
          (canonicalPathwiseResidualEnergy attempt) omega ∂P) ≤
        ∫ omega, canonicalPathwiseResidualEnergy attempt omega ∂P :=
    integral_mono hrestricted hintegrable hpoint
  unfold canonicalSuccessRestrictedResidualNumerator canonicalResidualNumerator
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_div_iff_of_pos_right hKreal).2 hintegral

/-- Theorem 3.7: a finite canonical stopped certificate records the survival
probability and the success-restricted normalized residual numerator. -/
structure FiniteStoppedCanonicalCertificate
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X) (hK : 2 ≤ K) where
  /-- The finite stopped attempt survives the prescribed horizon with the
  source confidence lower bound. -/
  successProbability_lower :
    ENNReal.ofReal (1 - confidence) ≤ P (attempt.successEvent)
  /-- The nonnegative residual scale carried by the certificate. -/
  residualPerSuccessBound : ℝ≥0
  /-- The normalized success-restricted residual numerator is bounded by the
  success probability times the declared scale. -/
  canonicalSuccessRestrictedResidualNumerator_le :
    canonicalSuccessRestrictedResidualNumerator attempt ≤
      P (attempt.successEvent) * (residualPerSuccessBound : ℝ≥0∞)

/-- Helper for Theorem 3.7: the finite canonical residual numerator is bounded
by the source residual constant after dividing by the output range. -/
theorem canonicalResidualNumerator_le_of_finiteStoppedCanonicalResidualNumerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (path : FiniteStoppedPath attempt)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (hbudget : path.baseStepBudget =
      LALM.StochasticRun.initialStepBound h params)
    (hcoefficient : path.errorStepCoefficient =
      LALM.StochasticRun.errorStepConstant h params) :
    canonicalResidualNumerator attempt ≤
      ENNReal.ofReal
        (LALM.StochasticRun.complexityConstant h oracle params /
          ((K : ℝ) - 1)) := by
  have hKreal : 0 < (K : ℝ) - 1 := by
    have hKnat : 1 < K := by omega
    exact sub_pos.mpr (by exact_mod_cast hKnat)
  have hreal := finiteStoppedCanonicalResidualNumerator_le
    (f' := f) (c' := c) attempt hK path recursion hbudget hcoefficient
  unfold canonicalResidualNumerator
  apply ENNReal.ofReal_le_ofReal
  exact (div_le_div_iff_of_pos_right hKreal).2 hreal

/-- Helper for Theorem 3.7: the success-restricted finite canonical numerator
inherits the source residual constant bound. -/
theorem canonicalSuccessRestrictedResidualNumerator_le_of_finiteStoppedCanonicalResidualNumerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (path : FiniteStoppedPath attempt)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (hbudget : path.baseStepBudget =
      LALM.StochasticRun.initialStepBound h params)
    (hcoefficient : path.errorStepCoefficient =
      LALM.StochasticRun.errorStepConstant h params) :
    canonicalSuccessRestrictedResidualNumerator attempt ≤
      ENNReal.ofReal
        (LALM.StochasticRun.complexityConstant h oracle params /
          ((K : ℝ) - 1)) := by
  have hintegrable := integrable_canonicalPathwiseResidualEnergy_of_prefixInvariant
    (f' := f) (c' := c) attempt path.invariant hK
  exact (canonicalSuccessRestrictedResidualNumerator_le attempt hK hintegrable).trans
    (canonicalResidualNumerator_le_of_finiteStoppedCanonicalResidualNumerator
      (f := f) (c := c) attempt hK path recursion hbudget hcoefficient)

/-- Helper for Theorem 3.7: the finite canonical numerator can be converted
into a success-probability-weighted residual scale. -/
theorem finiteStoppedCanonicalCertificate_exists_of_numerator
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (_confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (hprobability : ENNReal.ofReal (1 - confidence) ≤
      P (attempt.successEvent))
    (bound : ℝ)
    (hnumerator : canonicalSuccessRestrictedResidualNumerator attempt ≤
      ENNReal.ofReal (bound / ((K : ℝ) - 1))) :
    ∃ certificate : FiniteStoppedCanonicalCertificate attempt hK,
      certificate.residualPerSuccessBound =
        Real.toNNReal
          (bound / ((1 - confidence) * ((K : ℝ) - 1))) := by
  let residualBound : ℝ≥0 := Real.toNNReal
    (bound / ((1 - confidence) * ((K : ℝ) - 1)))
  have hKreal : 0 < (K : ℝ) - 1 := by
    have hKnat : 1 < K := by omega
    exact sub_pos.mpr (by exact_mod_cast hKnat)
  have honeMinus : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hscale : (residualBound : ℝ≥0∞) =
      ENNReal.ofReal
        (bound / ((1 - confidence) * ((K : ℝ) - 1))) := by
    rfl
  have hnormalize :
      ENNReal.ofReal (bound / ((K : ℝ) - 1)) =
        ENNReal.ofReal (1 - confidence) * (residualBound : ℝ≥0∞) := by
    rw [hscale, ← ENNReal.ofReal_mul honeMinus.le]
    congr 1
    field_simp [honeMinus.ne', hKreal.ne']
  have hresidual : canonicalSuccessRestrictedResidualNumerator attempt ≤
      P (attempt.successEvent) * (residualBound : ℝ≥0∞) := by
    calc
      canonicalSuccessRestrictedResidualNumerator attempt ≤
          ENNReal.ofReal (bound / ((K : ℝ) - 1)) := hnumerator
      _ = ENNReal.ofReal (1 - confidence) *
          (residualBound : ℝ≥0∞) := hnormalize
      _ ≤ P (attempt.successEvent) * (residualBound : ℝ≥0∞) := by
        simpa only [mul_comm] using
          mul_le_mul_left hprobability (residualBound : ℝ≥0∞)
  refine ⟨{
    successProbability_lower := hprobability
    residualPerSuccessBound := residualBound
    canonicalSuccessRestrictedResidualNumerator_le := hresidual }, ?_⟩
  rfl

/-- Theorem 3.7: the canonical finite stopped attempt has the source-shaped
residual certificate once its path and schedule interfaces are supplied. -/
theorem finiteStoppedCanonicalSourceCertificate_exists
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1)
    (path : FiniteStoppedPath attempt)
    (recursion : FiniteStoppedSPIDERRecursion attempt)
    (hbudget : path.baseStepBudget =
      LALM.StochasticRun.initialStepBound h params)
    (hcoefficient : path.errorStepCoefficient =
      LALM.StochasticRun.errorStepConstant h params)
    (control : FiniteStoppedExitControl path)
    (threshold_eq : control.threshold =
      LALM.StochasticRun.errorAverageConstant h oracle params / confidence) :
    ∃ certificate : FiniteStoppedCanonicalCertificate attempt hK,
      certificate.residualPerSuccessBound =
        Real.toNNReal
          (LALM.StochasticRun.complexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))) := by
  have hprobability := finiteStoppedScheduledSuccessProbability attempt hK
    confidence_pos path recursion hbudget hcoefficient control threshold_eq
  have hnumerator :=
    canonicalSuccessRestrictedResidualNumerator_le_of_finiteStoppedCanonicalResidualNumerator
      (f := f) (c := c) attempt hK path recursion hbudget hcoefficient
  exact finiteStoppedCanonicalCertificate_exists_of_numerator attempt hK
    confidence_pos confidence_lt_one hprobability
    (LALM.StochasticRun.complexityConstant h oracle params) hnumerator

/-- Theorem 3.7: every canonical finite stopped scheduled attempt carries the
source-shaped success and residual certificate under the article's numerical
conditions, without additional path, recursion, or exit-control assumptions. -/
theorem finiteStoppedCanonicalSourceCertificate_exists_of_canonicalAttempt
    (attempt : SPIDER.StoppedScheduledAttempt h oracle P x₀ multiplier₀
      params confidence K X)
    (hK : 2 ≤ K)
    (confidence_pos : 0 < confidence)
    (confidence_lt_one : confidence < 1) :
    ∃ certificate : FiniteStoppedCanonicalCertificate attempt hK,
      certificate.residualPerSuccessBound =
        Real.toNNReal
          (LALM.StochasticRun.complexityConstant h oracle params /
            ((1 - confidence) * ((K : ℝ) - 1))) := by
  obtain ⟨path, hbudget, hcoefficient⟩ :=
    finiteStoppedPath_exists attempt (by omega)
  have objectiveBound : FiniteStoppedObjectiveExitBound path :=
    finiteStoppedObjectiveExitBound_of_canonicalCertificate
      (canonicalFiniteStoppedPathCertificate attempt) (by omega) path
  obtain ⟨control, threshold_eq⟩ :=
    finiteStoppedExitControl_exists_of_objectiveExitBound path objectiveBound
      confidence_pos
  exact finiteStoppedCanonicalSourceCertificate_exists attempt hK
    confidence_pos confidence_lt_one path
    (canonicalFiniteStoppedSPIDERRecursion attempt) hbudget hcoefficient
    control threshold_eq

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
