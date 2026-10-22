/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_4_2.FiniteStoppedEnergy
import all TR_LALM_theory.Corollary_4_2.FiniteStoppedEnergy

public section

open MeasureTheory
open scoped BigOperators ENNReal NNReal

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

/-! These pathwise sums are finite by construction.  They are intentionally
    separate from the expectation-valued energies: the exit argument needs a
    measurable random variable before applying Markov's inequality. -/

/-- Helper for Corollary 4.2: the pathwise clipped-gradient error energy of a
finite stopped attempt. -/
noncomputable def pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, activeGradientErrorIntegrand attempt k ω

/-- Helper for Corollary 4.2: the pathwise active base-step energy of a finite
stopped attempt. -/
noncomputable def pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k ω

/-- Helper for Corollary 4.2: the pathwise corrected-displacement energy of a
finite stopped attempt. -/
noncomputable def pathwiseDisplacementEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, activeDisplacementIntegrand attempt k ω

/-- Helper for Corollary 4.2: the finite pathwise clipped-gradient energy is
measurable. -/
theorem measurable_pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Measurable (pathwiseGradientErrorEnergy attempt) := by
  unfold pathwiseGradientErrorEnergy
  exact Finset.measurable_sum _ fun k _hk ↦
    measurable_activeGradientErrorIntegrand attempt k

/-- Helper for Corollary 4.2: the finite pathwise base-step energy is
measurable. -/
theorem measurable_pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Measurable (pathwiseBaseStepEnergy attempt) := by
  unfold pathwiseBaseStepEnergy
  exact Finset.measurable_sum _ fun k _hk ↦
    measurable_activeBaseStepIntegrand attempt k

/-- Helper for Corollary 4.2: the finite pathwise displacement energy is
measurable. -/
theorem measurable_pathwiseDisplacementEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Measurable (pathwiseDisplacementEnergy attempt) := by
  unfold pathwiseDisplacementEnergy
  exact Finset.measurable_sum _ fun k _hk ↦
    measurable_activeDisplacementIntegrand attempt k

/-- Helper for Corollary 4.2: the finite pathwise clipped-gradient energy is
integrable. -/
theorem integrable_pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Integrable (pathwiseGradientErrorEnergy attempt) P := by
  unfold pathwiseGradientErrorEnergy
  exact integrable_finsetSum (Finset.range K) fun k _hk ↦
    integrable_activeGradientErrorIntegrand attempt k

/-- Helper for Corollary 4.2: the finite pathwise base-step energy is
integrable. -/
theorem integrable_pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Integrable (pathwiseBaseStepEnergy attempt) P := by
  unfold pathwiseBaseStepEnergy
  exact integrable_finsetSum (Finset.range K) fun k _hk ↦
    integrable_activeBaseStepIntegrand attempt k

/-- Helper for Corollary 4.2: the finite pathwise displacement energy is
integrable. -/
theorem integrable_pathwiseDisplacementEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    Integrable (pathwiseDisplacementEnergy attempt) P := by
  unfold pathwiseDisplacementEnergy
  exact integrable_finsetSum (Finset.range K) fun k _hk ↦
    integrable_activeDisplacementIntegrand attempt k

/-- Helper for Corollary 4.2: integrating a finite pathwise energy recovers its
stopped expectation energy. -/
theorem integral_pathwiseGradientErrorEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    (∫ ω, pathwiseGradientErrorEnergy attempt ω ∂P) =
      stoppedGradientErrorEnergy attempt := by
  unfold pathwiseGradientErrorEnergy stoppedGradientErrorEnergy
  rw [integral_finsetSum (Finset.range K)
    (fun k _hk ↦ integrable_activeGradientErrorIntegrand attempt k)]

/-- Helper for Corollary 4.2: integrating a finite pathwise base-step energy
recovers its stopped expectation energy. -/
theorem integral_pathwiseBaseStepEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    (∫ ω, pathwiseBaseStepEnergy attempt ω ∂P) =
      stoppedBaseStepEnergy attempt := by
  unfold pathwiseBaseStepEnergy stoppedBaseStepEnergy
  rw [integral_finsetSum (Finset.range K)
    (fun k _hk ↦ integrable_activeBaseStepIntegrand attempt k)]

/-- Helper for Corollary 4.2: integrating a finite pathwise displacement energy
recovers its stopped expectation energy. -/
theorem integral_pathwiseDisplacementEnergy
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) :
    (∫ ω, pathwiseDisplacementEnergy attempt ω ∂P) =
      stoppedDisplacementEnergy attempt := by
  unfold pathwiseDisplacementEnergy stoppedDisplacementEnergy
  rw [integral_finsetSum (Finset.range K)
    (fun k _hk ↦ integrable_activeDisplacementIntegrand attempt k)]

/-! A finite path packages the pathwise telescope separately from the
    probabilistic error recursion.  This is the interface used by the
    canonical stopped certificate; proving the field once avoids unfolding
    the localized transition in every energy argument. -/

/-- Corollary 4.2: a finite stopped path with a pathwise Lyapunov telescope. -/
structure FiniteStoppedPath
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) where
  /-- The deterministic allowance for the active base-step energy. -/
  baseStepBudget : ℝ
  /-- The coefficient multiplying pathwise estimator error in the telescope. -/
  errorStepCoefficient : ℝ
  /-- The allowance is nonnegative. -/
  baseStepBudget_nonneg : 0 ≤ baseStepBudget
  /-- The telescope coefficient is nonnegative. -/
  errorStepCoefficient_nonneg : 0 ≤ errorStepCoefficient
  /-- Every finite sample path satisfies the active-prefix base-step telescope. -/
  pathwise_baseStepEnergy_le :
    ∀ ω, pathwiseBaseStepEnergy attempt ω ≤
      baseStepBudget + errorStepCoefficient * pathwiseGradientErrorEnergy attempt ω

/-- Helper for Corollary 4.2: a pathwise finite telescope integrates to the
corresponding stopped base-step energy inequality. -/
theorem FiniteStoppedPath.baseStepEnergy_le
    (path : FiniteStoppedPath attempt) :
    stoppedBaseStepEnergy attempt ≤
      path.baseStepBudget + path.errorStepCoefficient *
        stoppedGradientErrorEnergy attempt := by
  have hleft := integrable_pathwiseBaseStepEnergy attempt
  have herror := integrable_pathwiseGradientErrorEnergy attempt
  have hright : Integrable
      (fun ω ↦ path.baseStepBudget + path.errorStepCoefficient *
        pathwiseGradientErrorEnergy attempt ω) P :=
    (integrable_const _).add (herror.const_mul _)
  calc
    stoppedBaseStepEnergy attempt =
        ∫ ω, pathwiseBaseStepEnergy attempt ω ∂P :=
      (integral_pathwiseBaseStepEnergy attempt).symm
    _ ≤ ∫ ω, path.baseStepBudget + path.errorStepCoefficient *
        pathwiseGradientErrorEnergy attempt ω ∂P :=
      integral_mono hleft hright path.pathwise_baseStepEnergy_le
    _ = path.baseStepBudget + path.errorStepCoefficient *
        stoppedGradientErrorEnergy attempt := by
      rw [integral_add (integrable_const _)
          (herror.const_mul path.errorStepCoefficient), integral_const_mul,
        integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
        one_smul, integral_pathwiseGradientErrorEnergy]

/-! The next structure records the second, probabilistic half of the finite
    energy coupling.  Its fields are deliberately inequalities, so a future
    canonical proof can supply them without committing to a particular
    implementation of the sample recursion. -/

/-- Corollary 4.2: aggregate finite stopped energy coupling hypotheses. -/
structure FiniteStoppedEnergyCoupling
    (path : FiniteStoppedPath attempt) where
  /-- The refresh-block estimator allowance. -/
  gradientErrorBudget : ℝ
  /-- The displacement coefficient in the estimator recursion. -/
  displacementErrorCoefficient : ℝ
  /-- The estimator allowance is nonnegative. -/
  gradientErrorBudget_nonneg : 0 ≤ gradientErrorBudget
  /-- The displacement coefficient is nonnegative. -/
  displacementErrorCoefficient_nonneg : 0 ≤ displacementErrorCoefficient
  /-- The stopped estimator energy obeys the refresh-block recursion. -/
  gradientErrorEnergy_le :
    stoppedGradientErrorEnergy attempt ≤ gradientErrorBudget +
      displacementErrorCoefficient * stoppedDisplacementEnergy attempt
  /-- The stopped displacement energy is controlled by the base-step energy. -/
  displacementEnergy_le :
    stoppedDisplacementEnergy attempt ≤
      displacementFactor h params.delta ^ 2 * stoppedBaseStepEnergy attempt

/-- Helper for Corollary 4.2: solve a nonnegative three-energy linear coupling
when the feedback coefficient is strictly below one. -/
theorem solve_finite_energy_coupling
    {E B₀ D A C α γ β : ℝ}
    (hE : E ≤ A + α * D)
    (hD : D ≤ γ * B₀)
    (hB : B₀ ≤ C + β * E)
    (hα : 0 ≤ α) (hγ : 0 ≤ γ)
    (hcontract : α * γ * β < 1) :
    E ≤ (A + α * γ * C) / (1 - α * γ * β) := by
  have hden : 0 < 1 - α * γ * β := sub_pos.mpr hcontract
  have hcombined : E ≤ A + α * γ * C + (α * γ * β) * E := by
    calc
      E ≤ A + α * D := hE
      _ ≤ A + α * (γ * B₀) :=
        by simpa only [add_comm] using
          (add_le_add_left (mul_le_mul_of_nonneg_left hD hα) A)
      _ ≤ A + α * γ * (C + β * E) := by
        have hbg := mul_le_mul_of_nonneg_left hB (mul_nonneg hα hγ)
        nlinarith
      _ = A + α * γ * C + (α * γ * β) * E := by ring
  apply (le_div_iff₀ hden).2
  nlinarith [hcombined]

/-! The generic solver above is retained as a small algebraic adapter, while
    the attempt-specific coupling below uses the mathematically meaningful
    three allowances (error, displacement, and base-step). -/

/-- Helper for Corollary 4.2: an attempt-specific energy coupling exposes its
feedback coefficient and aggregate inequalities. -/
structure FiniteStoppedEnergyCouplingData
    (path : FiniteStoppedPath attempt) where
  /-- The refresh-block error allowance. -/
  errorBudget : ℝ
  /-- The coefficient from base-step energy to estimator energy. -/
  errorBaseCoefficient : ℝ
  /-- The error allowance is nonnegative. -/
  errorBudget_nonneg : 0 ≤ errorBudget
  /-- The error/base coefficient is nonnegative. -/
  errorBaseCoefficient_nonneg : 0 ≤ errorBaseCoefficient
  /-- Aggregate estimator-energy inequality. -/
  errorEnergy_le :
    stoppedGradientErrorEnergy attempt ≤ errorBudget +
      errorBaseCoefficient * stoppedBaseStepEnergy attempt

/-- Helper for Corollary 4.2: the finite path and error recursion imply the
standard one-half absorption bound. -/
theorem FiniteStoppedEnergyCouplingData.errorEnergy_le_of_half
    (path : FiniteStoppedPath attempt)
    (data : FiniteStoppedEnergyCouplingData path)
    (hcontract : path.errorStepCoefficient * data.errorBaseCoefficient ≤ (1 : ℝ) / 2) :
    stoppedGradientErrorEnergy attempt ≤
      2 * (data.errorBudget + data.errorBaseCoefficient * path.baseStepBudget) := by
  have hbase := path.baseStepEnergy_le
  have herror := data.errorEnergy_le
  have hcoef : 0 ≤ data.errorBaseCoefficient := data.errorBaseCoefficient_nonneg
  have hstepcoef : 0 ≤ path.errorStepCoefficient := path.errorStepCoefficient_nonneg
  have hfeedback :=
    mul_le_mul_of_nonneg_left hbase data.errorBaseCoefficient_nonneg
  have herrorNonneg := stoppedGradientErrorEnergy_nonneg attempt
  have hbound : stoppedGradientErrorEnergy attempt ≤
      data.errorBudget + data.errorBaseCoefficient * path.baseStepBudget +
        (1 / 2 : ℝ) * stoppedGradientErrorEnergy attempt := by
    calc
      stoppedGradientErrorEnergy attempt ≤ data.errorBudget +
          data.errorBaseCoefficient * stoppedBaseStepEnergy attempt := herror
      _ ≤ data.errorBudget + data.errorBaseCoefficient *
          (path.baseStepBudget + path.errorStepCoefficient *
            stoppedGradientErrorEnergy attempt) :=
        by simpa only [add_comm] using
          (add_le_add_left hfeedback data.errorBudget)
      _ ≤ data.errorBudget + data.errorBaseCoefficient * path.baseStepBudget +
          (1 / 2 : ℝ) * stoppedGradientErrorEnergy attempt := by
        have hscaled := mul_le_mul_of_nonneg_right hcontract herrorNonneg
        nlinarith [hscaled]
  linarith

/-! Exit control is stated at the finite pathwise level.  The theorem below
    gives the exact Markov product inequality; converting it to a chosen
    confidence level is then a small ENNReal normalization step. -/

/-- Corollary 4.2: a finite pathwise exit threshold and its energy implication. -/
structure FiniteStoppedExitControl
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X) where
  /-- The error-energy threshold at which localization is known to fail. -/
  threshold : ℝ
  /-- The threshold is strictly positive. -/
  threshold_pos : 0 < threshold
  /-- Leaving the finite success event forces the threshold energy. -/
  exit_implies_energy_gt :
    ∀ ω, ω ∉ successEvent attempt →
      threshold < pathwiseGradientErrorEnergy attempt ω

/-- Helper for Corollary 4.2: finite stopped exit control yields the Markov
product bound for the failure probability. -/
theorem FiniteStoppedExitControl.complement_mul_le
    (control : FiniteStoppedExitControl attempt) :
    ENNReal.ofReal control.threshold * P (successEvent attempt)ᶜ ≤
      ENNReal.ofReal (stoppedGradientErrorEnergy attempt) := by
  let g : Ω → ℝ≥0∞ := fun ω ↦
    ENNReal.ofReal (pathwiseGradientErrorEnergy attempt ω)
  have hg : Measurable g := by
    exact ENNReal.measurable_ofReal.comp
      (measurable_pathwiseGradientErrorEnergy attempt)
  have hnonneg : ∀ ω, 0 ≤ pathwiseGradientErrorEnergy attempt ω := by
    intro ω
    unfold pathwiseGradientErrorEnergy
    exact Finset.sum_nonneg fun k _hk ↦
      activeGradientErrorIntegrand_nonneg attempt k ω
  have hsubset : (successEvent attempt)ᶜ ⊆ {ω |
      ENNReal.ofReal control.threshold ≤ g ω} := by
    intro ω hω
    have hgt := control.exit_implies_energy_gt ω hω
    change ENNReal.ofReal control.threshold ≤
      ENNReal.ofReal (pathwiseGradientErrorEnergy attempt ω)
    exact ENNReal.ofReal_le_ofReal hgt.le
  have hmarkov := mul_meas_ge_le_lintegral (μ := P) hg
    (ENNReal.ofReal control.threshold)
  have hmeasure :
      ENNReal.ofReal control.threshold * P (successEvent attempt)ᶜ ≤
        ENNReal.ofReal control.threshold *
          P {ω | ENNReal.ofReal control.threshold ≤ g ω} :=
        mul_le_mul_of_nonneg_left (measure_mono hsubset) zero_le
  have hintegral : (∫⁻ ω, g ω ∂P) =
      ENNReal.ofReal (stoppedGradientErrorEnergy attempt) := by
    dsimp [g]
    rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_pathwiseGradientErrorEnergy attempt)
      (Filter.Eventually.of_forall (fun ω ↦ hnonneg ω))]
    rw [integral_pathwiseGradientErrorEnergy]
  calc
    ENNReal.ofReal control.threshold * P (successEvent attempt)ᶜ ≤
        ENNReal.ofReal control.threshold *
          P {ω | ENNReal.ofReal control.threshold ≤ g ω} := hmeasure
    _ ≤ ∫⁻ ω, g ω ∂P := hmarkov
    _ = ENNReal.ofReal (stoppedGradientErrorEnergy attempt) := hintegral

end StoppedAttemptAnalysis

end LALM.Correction

end
