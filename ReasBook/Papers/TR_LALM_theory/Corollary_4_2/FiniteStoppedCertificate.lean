/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.StoppedAttemptAnalysis

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

/-- Corollary 4.2: normalize a finite-horizon residual numerator bound by the
success probability and the output horizon. -/
noncomputable def normalizedResidualScale
    (bound confidence : ℝ) (K : ℕ) : ℝ≥0 :=
  Real.toNNReal (bound / ((1 - confidence) * ((K : ℝ) - 1)))

/-- Helper for Corollary 4.2: the normalized finite residual scale has the
corresponding `ENNReal.ofReal` representation. -/
theorem coe_normalizedResidualScale
    (bound confidence : ℝ) (K : ℕ) :
    (normalizedResidualScale bound confidence K : ℝ≥0∞) =
      ENNReal.ofReal (bound / ((1 - confidence) * ((K : ℝ) - 1))) := by
  rfl

/-- Corollary 4.2: a finite stopped attempt yields a certificate directly from
its success-probability lower bound and its success-restricted residual bound.
This adapter is finite-horizon and does not require an infinite `ScheduledRun`. -/
theorem certificate_exists_of_successProbability_and_residual
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (hK : 2 ≤ K) (confidence_lt_one : confidence < 1)
    (hprobability : ENNReal.ofReal (1 - confidence) ≤ P (successEvent attempt))
    (bound : ℝ)
    (hnumerator : successRestrictedResidualNumerator attempt hK ≤
      ENNReal.ofReal (bound / ((K : ℝ) - 1))) :
    ∃ certificate : StoppedAttemptCertificate attempt hK,
      certificate.residualPerSuccessBound =
        normalizedResidualScale bound confidence K := by
  let residualBound := normalizedResidualScale bound confidence K
  have hKnat : 1 < K := by omega
  have hKreal : (1 : ℝ) < (K : ℝ) := by exact_mod_cast hKnat
  have hdenominator : 0 < (K : ℝ) - 1 := sub_pos.mpr hKreal
  have honeMinus : 0 < 1 - confidence := sub_pos.mpr confidence_lt_one
  have hresidualBoundCoe : (residualBound : ℝ≥0∞) =
      ENNReal.ofReal (bound / ((1 - confidence) * ((K : ℝ) - 1))) := by
    exact coe_normalizedResidualScale bound confidence K
  have hnormalize :
      ENNReal.ofReal (bound / ((K : ℝ) - 1)) =
        ENNReal.ofReal (1 - confidence) * (residualBound : ℝ≥0∞) := by
    rw [hresidualBoundCoe]
    rw [← ENNReal.ofReal_mul honeMinus.le]
    congr 1
    field_simp [honeMinus.ne', hdenominator.ne']
  have hresidual : successRestrictedResidualNumerator attempt hK ≤
      P (successEvent attempt) * (residualBound : ℝ≥0∞) := by
    calc
      successRestrictedResidualNumerator attempt hK ≤
          ENNReal.ofReal (bound / ((K : ℝ) - 1)) := hnumerator
      _ = ENNReal.ofReal (1 - confidence) * (residualBound : ℝ≥0∞) :=
        hnormalize
      _ ≤ P (successEvent attempt) * (residualBound : ℝ≥0∞) := by
        simpa only [mul_comm] using
          mul_le_mul_left hprobability (residualBound : ℝ≥0∞)
  refine ⟨{
    successProbability_lower := hprobability
    residualPerSuccessBound := residualBound
    successRestrictedResidual_le := hresidual }, rfl⟩

end StoppedAttemptAnalysis

end LALM.Correction

end
