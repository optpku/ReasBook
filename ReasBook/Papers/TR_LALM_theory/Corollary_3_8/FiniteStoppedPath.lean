/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergyRecursion
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedEnergyRecursion

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
variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}

/-! These finite sums are the random variables used by the exit argument.  They
    contain only the actual stopped observables; inactive summands are zero by
    definition. -/

/-- Helper for Theorem 3.7: the pathwise clipped-estimator error energy of a
finite stopped base attempt. -/
noncomputable def pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, activeGradientErrorIntegrand attempt k omega

/-- Helper for Theorem 3.7: the pathwise active base-step energy of a finite
stopped base attempt. -/
noncomputable def pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k omega

/-- Helper for Theorem 3.7: the finite pathwise estimator-error energy is
measurable. -/
theorem measurable_pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Measurable (pathwiseGradientErrorEnergy attempt) := by
  unfold pathwiseGradientErrorEnergy
  exact Finset.measurable_sum _ fun k _hk ↦
    measurable_activeGradientErrorIntegrand attempt k

/-- Helper for Theorem 3.7: the finite pathwise base-step energy is
measurable. -/
theorem measurable_pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Measurable (pathwiseBaseStepEnergy attempt) := by
  unfold pathwiseBaseStepEnergy
  exact Finset.measurable_sum _ fun k _hk ↦
    measurable_activeBaseStepIntegrand attempt k

/-- Helper for Theorem 3.7: the finite pathwise estimator-error energy is
integrable. -/
theorem integrable_pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Integrable (pathwiseGradientErrorEnergy attempt) P := by
  unfold pathwiseGradientErrorEnergy
  exact integrable_finsetSum (Finset.range K) fun k _hk ↦
    integrable_activeGradientErrorIntegrand attempt k

/-- Helper for Theorem 3.7: a prefix invariant makes the finite pathwise
base-step energy integrable. -/
theorem integrable_pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt) :
    Integrable (pathwiseBaseStepEnergy attempt) P := by
  unfold pathwiseBaseStepEnergy
  exact integrable_finsetSum (Finset.range K) fun k _hk ↦
    integrable_activeBaseStepMeanSquare attempt invariant k

/-- Helper for Theorem 3.7: integrating the finite pathwise estimator-error
energy recovers the stopped estimator-error energy. -/
theorem integral_pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    (∫ omega, pathwiseGradientErrorEnergy attempt omega ∂P) =
      stoppedGradientErrorEnergy attempt := by
  unfold pathwiseGradientErrorEnergy stoppedGradientErrorEnergy
    activeGradientErrorMeanSquare
  rw [integral_finsetSum (Finset.range K)
    (fun k _hk ↦ integrable_activeGradientErrorIntegrand attempt k)]

/-- Helper for Theorem 3.7: integrating a finite pathwise base-step energy
recovers the corresponding stopped energy. -/
theorem integral_pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (invariant : FiniteStoppedPrefixInvariant attempt) :
    (∫ omega, pathwiseBaseStepEnergy attempt omega ∂P) =
      stoppedBaseStepEnergy attempt := by
  unfold pathwiseBaseStepEnergy stoppedBaseStepEnergy
    activeBaseStepMeanSquare
  rw [integral_finsetSum (Finset.range K)
    (fun k _hk ↦ integrable_activeBaseStepMeanSquare attempt invariant k)]

/-- Helper for Theorem 3.7: the finite pathwise estimator-error energy is
nonnegative. -/
theorem pathwiseGradientErrorEnergy_nonneg
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (omega : Ω) :
    0 ≤ pathwiseGradientErrorEnergy attempt omega := by
  unfold pathwiseGradientErrorEnergy
  exact Finset.sum_nonneg fun k _hk ↦
    activeGradientErrorIntegrand_nonneg attempt k omega

/-- Theorem 3.7: a finite stopped base path packages the pathwise Lyapunov
telescope and its two analytic energy constants. -/
structure FiniteStoppedPath
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- The actual prefix invariant used by the telescope. -/
  invariant : FiniteStoppedPrefixInvariant attempt
  /-- The deterministic allowance for active base-step energy. -/
  baseStepBudget : ℝ
  /-- The coefficient multiplying pathwise estimator error. -/
  errorStepCoefficient : ℝ
  /-- The deterministic allowance is nonnegative. -/
  baseStepBudget_nonneg : 0 ≤ baseStepBudget
  /-- The telescope coefficient is nonnegative. -/
  errorStepCoefficient_nonneg : 0 ≤ errorStepCoefficient
  /-- Every sample path satisfies the active-prefix base-step telescope. -/
  pathwise_baseStepEnergy_le :
    ∀ omega, pathwiseBaseStepEnergy attempt omega ≤
      baseStepBudget + errorStepCoefficient *
        pathwiseGradientErrorEnergy attempt omega

/-- Helper for Theorem 3.7: a finite pathwise telescope integrates to the
stopped base-step energy inequality. -/
theorem FiniteStoppedPath.baseStepEnergy_le
    (path : FiniteStoppedPath attempt) :
    stoppedBaseStepEnergy attempt ≤
      path.baseStepBudget + path.errorStepCoefficient *
        stoppedGradientErrorEnergy attempt := by
  have hleft := integrable_pathwiseBaseStepEnergy attempt path.invariant
  have herror := integrable_pathwiseGradientErrorEnergy attempt
  have hright : Integrable
      (fun omega ↦ path.baseStepBudget + path.errorStepCoefficient *
        pathwiseGradientErrorEnergy attempt omega) P :=
    (integrable_const _).add (herror.const_mul _)
  calc
    stoppedBaseStepEnergy attempt =
        ∫ omega, pathwiseBaseStepEnergy attempt omega ∂P :=
      (integral_pathwiseBaseStepEnergy attempt path.invariant).symm
    _ ≤ ∫ omega, path.baseStepBudget + path.errorStepCoefficient *
        pathwiseGradientErrorEnergy attempt omega ∂P :=
      integral_mono hleft hright path.pathwise_baseStepEnergy_le
    _ = path.baseStepBudget + path.errorStepCoefficient *
        stoppedGradientErrorEnergy attempt := by
      rw [integral_add (integrable_const _)
          (herror.const_mul path.errorStepCoefficient), integral_const_mul,
        integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
        one_smul, integral_pathwiseGradientErrorEnergy]

/-! Exit control is kept as a path-indexed interface.  The strict inequality
    is the exact finite first-exit implication used by Markov's estimate. -/

/-- Theorem 3.7: a finite pathwise exit threshold and its energy implication. -/
structure FiniteStoppedExitControl
    (path : FiniteStoppedPath attempt) where
  /-- The error-energy threshold at which finite localization failure is known. -/
  threshold : ℝ
  /-- The threshold is strictly positive. -/
  threshold_pos : 0 < threshold
  /-- Leaving the finite success event forces the threshold energy. -/
  exit_implies_energy_gt :
    ∀ omega, omega ∉ attempt.successEvent →
      threshold < pathwiseGradientErrorEnergy attempt omega

/-- Helper for Theorem 3.7: finite exit control gives the Markov product bound
for the failure probability. -/
theorem FiniteStoppedExitControl.complement_mul_le
    (path : FiniteStoppedPath attempt)
    (control : FiniteStoppedExitControl path) :
    ENNReal.ofReal control.threshold * P (attempt.successEvent)ᶜ ≤
      ENNReal.ofReal (stoppedGradientErrorEnergy attempt) := by
  let g : Ω → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (pathwiseGradientErrorEnergy attempt omega)
  have hg : Measurable g := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_pathwiseGradientErrorEnergy attempt)
  have hsubset : (attempt.successEvent)ᶜ ⊆ {omega |
      ENNReal.ofReal control.threshold ≤ g omega} := by
    intro omega homega
    have hgt := control.exit_implies_energy_gt omega homega
    change ENNReal.ofReal control.threshold ≤
      ENNReal.ofReal (pathwiseGradientErrorEnergy attempt omega)
    exact ENNReal.ofReal_le_ofReal hgt.le
  have hmarkov := mul_meas_ge_le_lintegral (μ := P) hg
    (ENNReal.ofReal control.threshold)
  have hmeasure :
      ENNReal.ofReal control.threshold * P (attempt.successEvent)ᶜ ≤
        ENNReal.ofReal control.threshold *
          P {omega | ENNReal.ofReal control.threshold ≤ g omega} :=
    mul_le_mul_of_nonneg_left (measure_mono hsubset) zero_le
  have hintegral : (∫⁻ omega, g omega ∂P) =
      ENNReal.ofReal (stoppedGradientErrorEnergy attempt) := by
    dsimp [g]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_pathwiseGradientErrorEnergy attempt)
      (Filter.Eventually.of_forall (fun omega ↦
        pathwiseGradientErrorEnergy_nonneg attempt omega))]
    rw [integral_pathwiseGradientErrorEnergy]
  calc
    ENNReal.ofReal control.threshold * P (attempt.successEvent)ᶜ ≤
        ENNReal.ofReal control.threshold *
          P {omega | ENNReal.ofReal control.threshold ≤ g omega} := hmeasure
    _ ≤ ∫⁻ omega, g omega ∂P := hmarkov
    _ = ENNReal.ofReal (stoppedGradientErrorEnergy attempt) := hintegral

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
