/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import TR_LALM_theory.Corollary_3_8.FiniteStoppedPath
import all TR_LALM_theory.Corollary_3_8.FiniteStoppedPath

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

/-- Helper for Theorem 3.7: finite-prefix data for the stopped base Lyapunov
telescope. The sequences are required to describe the actual stopped prefix
through the witness below; they are not free replacement observables. -/
structure FinitePrefixLyapunovData (N : ℕ) where
  /-- The finite Lyapunov rank at each prefix index. -/
  lyapunov : ℕ → ℝ
  /-- The squared base-step energy at each prefix index. -/
  stepEnergy : ℕ → ℝ
  /-- The squared clipped-estimator error at each prefix index. -/
  errorEnergy : ℕ → ℝ
  /-- The initial rank is bounded by the deterministic allowance. -/
  lyapunov_one_le_initial :
    lyapunov 1 ≤ LALM.initialPotentialBound h params
  /-- The terminal rank has the uniform lower bound. -/
  lyapunov_lower_le_terminal :
    LALM.lyapunovLowerBound h params ≤ lyapunov N
  /-- Every positive transition satisfies the one-step descent inequality. -/
  descent :
    ∀ {k : ℕ}, 1 ≤ k → k < N →
      lyapunov (k + 1) ≤ lyapunov k -
          (params.beta / 4) * stepEnergy k +
        LALM.StochasticRun.lyapunovErrorConstant h params *
          (errorEnergy k + errorEnergy (k - 1))

namespace FinitePrefixLyapunovData

variable {N : ℕ}
variable (data : FinitePrefixLyapunovData (h := h) (params := params) N)

/-- Helper for Theorem 3.7: a finite Lyapunov telescope bounds positive-prefix
base-step energy by the initial rank gap and adjacent estimator errors. -/
theorem sum_stepEnergy_pos_le
    (hN : 1 ≤ N)
    (herror_nonneg : ∀ k < N, 0 ≤ data.errorEnergy k) :
    (params.beta / 4) * (∑ k ∈ Finset.Ico 1 N, data.stepEnergy k) ≤
      data.lyapunov 1 - LALM.lyapunovLowerBound h params +
        2 * LALM.StochasticRun.lyapunovErrorConstant h params *
          ∑ k ∈ Finset.range N, data.errorEnergy k := by
  have hdescent :
      (∑ k ∈ Finset.Ico 1 N, (params.beta / 4) * data.stepEnergy k) ≤
        ∑ k ∈ Finset.Ico 1 N,
          ((data.lyapunov k - data.lyapunov (k + 1)) +
            LALM.StochasticRun.lyapunovErrorConstant h params *
              (data.errorEnergy k + data.errorEnergy (k - 1))) := by
    refine Finset.sum_le_sum fun k hk ↦ ?_
    have hkBounds := Finset.mem_Ico.mp hk
    have hstep := data.descent hkBounds.1 hkBounds.2
    linarith
  have hendpointLeft : 1 + (N - 1) = N := by omega
  have hendpointRight : N - 1 + 1 = N := by omega
  have htelescope :
      (∑ k ∈ Finset.Ico 1 N,
          (data.lyapunov k - data.lyapunov (k + 1))) =
        data.lyapunov 1 - data.lyapunov N := by
    rw [Finset.sum_Ico_eq_sum_range]
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpointLeft, hendpointRight] using
      (Finset.sum_range_sub' (fun k ↦ data.lyapunov (k + 1)) (N - 1))
  have hcurrentSubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 N, data.errorEnergy k) ≤
        ∑ k ∈ Finset.range N, data.errorEnergy k :=
    Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k hkRange _hkIco ↦ herror_nonneg k (Finset.mem_range.mp hkRange))
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 N, data.errorEnergy (k - 1)) =
        ∑ j ∈ Finset.range (N - 1), data.errorEnergy j := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    have hindex : 1 + j - 1 = j := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (N - 1) ⊆ Finset.range N := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 N, data.errorEnergy (k - 1)) ≤
        ∑ k ∈ Finset.range N, data.errorEnergy k := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k hkLong _hkShort ↦ herror_nonneg k (Finset.mem_range.mp hkLong))
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 N,
          (data.errorEnergy k + data.errorEnergy (k - 1))) ≤
        2 * ∑ k ∈ Finset.range N, data.errorEnergy k := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [← Finset.mul_sum, Finset.sum_add_distrib, htelescope,
    ← Finset.mul_sum] at hdescent
  have herrorCoefficientNonneg :
      0 ≤ LALM.StochasticRun.lyapunovErrorConstant h params := by
    rw [LALM.StochasticRun.lyapunovErrorConstant_def,
      LALM.multiplierErrorConstant_def]
    positivity
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors herrorCoefficientNonneg
  nlinarith [hdescent, data.lyapunov_lower_le_terminal,
    hcurrentErrors, hpreviousErrors, herrorContribution]

/-- Helper for Theorem 3.7: nonnegative step energies and adjacent-error
descent bound the terminal Lyapunov rank by the initial rank plus twice the
finite error energy. -/
theorem terminal_le_initial_plus_error
    (hN : 1 ≤ N)
    (hstep_nonneg : ∀ k < N, 0 ≤ data.stepEnergy k)
    (herror_nonneg : ∀ k < N, 0 ≤ data.errorEnergy k) :
    data.lyapunov N ≤ data.lyapunov 1 +
      2 * LALM.StochasticRun.lyapunovErrorConstant h params *
        ∑ k ∈ Finset.range N, data.errorEnergy k := by
  have hdescent :
      (∑ k ∈ Finset.Ico 1 N,
          -(LALM.StochasticRun.lyapunovErrorConstant h params *
            (data.errorEnergy k + data.errorEnergy (k - 1)))) ≤
        ∑ k ∈ Finset.Ico 1 N,
          (data.lyapunov k - data.lyapunov (k + 1)) := by
    apply Finset.sum_le_sum
    intro k hk
    have hkBounds := Finset.mem_Ico.mp hk
    have hstep := hstep_nonneg k (by omega)
    have hterm := data.descent hkBounds.1 hkBounds.2
    have hcoefficient : (0 : ℝ) ≤ params.beta / 4 := by positivity
    have hnonnegative :
        0 ≤ (params.beta / 4) * data.stepEnergy k :=
      mul_nonneg hcoefficient hstep
    linarith
  have htelescope :
      (∑ k ∈ Finset.Ico 1 N,
          (data.lyapunov k - data.lyapunov (k + 1))) =
        data.lyapunov 1 - data.lyapunov N := by
    rw [Finset.sum_Ico_eq_sum_range]
    have hendpoint : N - 1 + 1 = N := by omega
    simpa only [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
      hendpoint] using
      (Finset.sum_range_sub' (fun k ↦ data.lyapunov (k + 1)) (N - 1))
  have hcurrentSubset : Finset.Ico 1 N ⊆ Finset.range N := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
  have hcurrentErrors :
      (∑ k ∈ Finset.Ico 1 N, data.errorEnergy k) ≤
        ∑ k ∈ Finset.range N, data.errorEnergy k :=
    Finset.sum_le_sum_of_subset_of_nonneg hcurrentSubset
      (fun k hkRange _hkIco ↦ herror_nonneg k (Finset.mem_range.mp hkRange))
  have hpreviousErrorEq :
      (∑ k ∈ Finset.Ico 1 N, data.errorEnergy (k - 1)) =
        ∑ k ∈ Finset.range (N - 1), data.errorEnergy k := by
    rw [Finset.sum_Ico_eq_sum_range]
    apply Finset.sum_congr rfl
    intro k hk
    have hindex : 1 + k - 1 = k := by omega
    rw [hindex]
  have hpreviousSubset : Finset.range (N - 1) ⊆ Finset.range N := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have hpreviousErrors :
      (∑ k ∈ Finset.Ico 1 N, data.errorEnergy (k - 1)) ≤
        ∑ k ∈ Finset.range N, data.errorEnergy k := by
    rw [hpreviousErrorEq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hpreviousSubset
      (fun k hkLong _hkShort ↦ herror_nonneg k (Finset.mem_range.mp hkLong))
  have hadjacentErrors :
      (∑ k ∈ Finset.Ico 1 N,
          (data.errorEnergy k + data.errorEnergy (k - 1))) ≤
        2 * ∑ k ∈ Finset.range N, data.errorEnergy k := by
    rw [Finset.sum_add_distrib]
    linarith
  rw [Finset.sum_neg_distrib, htelescope] at hdescent
  have hcoefficientNonneg :
      0 ≤ LALM.StochasticRun.lyapunovErrorConstant h params := by
    rw [LALM.StochasticRun.lyapunovErrorConstant_def,
      LALM.multiplierErrorConstant_def]
    positivity
  have herrorContribution :=
    mul_le_mul_of_nonneg_left hadjacentErrors hcoefficientNonneg
  have hterminal :
      data.lyapunov N - data.lyapunov 1 ≤
        ∑ k ∈ Finset.Ico 1 N,
          LALM.StochasticRun.lyapunovErrorConstant h params *
            (data.errorEnergy k + data.errorEnergy (k - 1)) := by
    linarith [hdescent]
  have herrorContribution' :
      (∑ k ∈ Finset.Ico 1 N,
          LALM.StochasticRun.lyapunovErrorConstant h params *
            (data.errorEnergy k + data.errorEnergy (k - 1))) ≤
        2 * LALM.StochasticRun.lyapunovErrorConstant h params *
          ∑ k ∈ Finset.range N, data.errorEnergy k := by
    calc
      (∑ k ∈ Finset.Ico 1 N,
          LALM.StochasticRun.lyapunovErrorConstant h params *
            (data.errorEnergy k + data.errorEnergy (k - 1))) =
          LALM.StochasticRun.lyapunovErrorConstant h params *
            ∑ k ∈ Finset.Ico 1 N,
              (data.errorEnergy k + data.errorEnergy (k - 1)) := by
        rw [Finset.mul_sum]
      _ ≤ LALM.StochasticRun.lyapunovErrorConstant h params *
          (2 * ∑ k ∈ Finset.range N, data.errorEnergy k) :=
        herrorContribution
      _ = 2 * LALM.StochasticRun.lyapunovErrorConstant h params *
          ∑ k ∈ Finset.range N, data.errorEnergy k := by ring
  nlinarith [hterminal, herrorContribution']

/-- Helper for Theorem 3.7: restoring index zero gives the canonical finite
base-step allowance. -/
theorem sum_stepEnergy_le
    (hN : 1 ≤ N)
    (herror_nonneg : ∀ k < N, 0 ≤ data.errorEnergy k)
    (hzero : data.stepEnergy 0 ≤ (params.delta : ℝ) ^ 2) :
    ∑ k ∈ Finset.range N, data.stepEnergy k ≤
      LALM.StochasticRun.initialStepBound h params +
        LALM.StochasticRun.errorStepConstant h params *
          ∑ k ∈ Finset.range N, data.errorEnergy k := by
  have hpos := data.sum_stepEnergy_pos_le hN herror_nonneg
  have hbeta : 0 < (params.beta : ℝ) := params.spec.1.2.1
  have hscale : 0 ≤ 4 / (params.beta : ℝ) := by positivity
  have hscaled :
      (∑ k ∈ Finset.Ico 1 N, data.stepEnergy k) ≤
        4 * (data.lyapunov 1 - LALM.lyapunovLowerBound h params) /
            params.beta +
          (8 * LALM.StochasticRun.lyapunovErrorConstant h params /
            params.beta) * ∑ k ∈ Finset.range N, data.errorEnergy k := by
    calc
      (∑ k ∈ Finset.Ico 1 N, data.stepEnergy k) =
          (4 / params.beta) *
            ((params.beta / 4) *
              ∑ k ∈ Finset.Ico 1 N, data.stepEnergy k) := by
        field_simp [hbeta.ne']
      _ ≤ (4 / params.beta) *
          (data.lyapunov 1 - LALM.lyapunovLowerBound h params +
            2 * LALM.StochasticRun.lyapunovErrorConstant h params *
              ∑ k ∈ Finset.range N, data.errorEnergy k) :=
        mul_le_mul_of_nonneg_left hpos hscale
      _ = 4 * (data.lyapunov 1 - LALM.lyapunovLowerBound h params) /
            params.beta +
          (8 * LALM.StochasticRun.lyapunovErrorConstant h params /
            params.beta) * ∑ k ∈ Finset.range N, data.errorEnergy k := by
        ring
  have hgap := sub_le_sub_right data.lyapunov_one_le_initial
    (LALM.lyapunovLowerBound h params)
  have hgapScaled := mul_le_mul_of_nonneg_left hgap hscale
  have hgapNormalized :
      4 * (data.lyapunov 1 - LALM.lyapunovLowerBound h params) /
          params.beta ≤
        4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by
    calc
      4 * (data.lyapunov 1 - LALM.lyapunovLowerBound h params) /
          params.beta =
          (4 / params.beta) *
            (data.lyapunov 1 - LALM.lyapunovLowerBound h params) := by ring
      _ ≤ (4 / params.beta) *
          (LALM.initialPotentialBound h params -
            LALM.lyapunovLowerBound h params) := hgapScaled
      _ = 4 * (LALM.initialPotentialBound h params -
          LALM.lyapunovLowerBound h params) / params.beta := by ring
  have hdecomposition :
      (∑ k ∈ Finset.range N, data.stepEnergy k) = data.stepEnergy 0 +
        ∑ k ∈ Finset.Ico 1 N, data.stepEnergy k := by
    rw [Finset.sum_Ico_eq_sub _ hN]
    simp
  rw [hdecomposition,
    LALM.StochasticRun.initialStepBound_def,
    LALM.StochasticRun.errorStepConstant_def]
  linarith [hscaled, hgapNormalized, hzero]

end FinitePrefixLyapunovData

variable {Q B b : ℕ+} {confidence : ℝ} {K : ℕ}
variable {X : Set (EuclideanSpace ℝ (Fin n))}
variable {attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X}

/-- Helper for Theorem 3.7: a stopped path witness identifies finite Lyapunov
data with the actual active prefix and retains the genuine prefix invariant. -/
structure FiniteStoppedPathWitness
    (attempt : StoppedAttempt h oracle P x₀ multiplier₀ params Q B b confidence K X)
    where
  /-- The actual finite-prefix invariant. -/
  invariant : FiniteStoppedPrefixInvariant attempt
  /-- The active prefix length, bounded by the stopped horizon. -/
  prefixLength : Ω → ℕ
  /-- The initialized state belongs to the active prefix. -/
  prefixLength_pos : ∀ omega, 1 ≤ prefixLength omega
  /-- The active prefix is bounded by the prescribed horizon. -/
  prefixLength_le : ∀ omega, prefixLength omega ≤ K
  /-- The Lyapunov data on each actual active prefix. -/
  data : ∀ omega,
    FinitePrefixLyapunovData (h := h) (params := params) (prefixLength omega)
  /-- Prefix step energies are the actual stopped base-step squares. -/
  stepEnergy_eq_active :
    ∀ (omega : Ω) (k : ℕ), k < prefixLength omega →
      (data omega).stepEnergy k = activeBaseStepIntegrand attempt k omega
  /-- Prefix error energies are the actual stopped estimator-error squares. -/
  errorEnergy_eq_active :
    ∀ (omega : Ω) (k : ℕ), k < prefixLength omega →
      (data omega).errorEnergy k = activeGradientErrorIntegrand attempt k omega
  /-- The padded base-step energy vanishes after the active prefix. -/
  inactive_step_zero :
    ∀ (omega : Ω) (k : ℕ), prefixLength omega ≤ k → k < K →
      activeBaseStepIntegrand attempt k omega = 0
  /-- The padded estimator-error energy vanishes after the active prefix. -/
  inactive_error_zero :
    ∀ (omega : Ω) (k : ℕ), prefixLength omega ≤ k → k < K →
      activeGradientErrorIntegrand attempt k omega = 0
  /-- The index-zero active step is bounded by the localization radius. -/
  initial_step_bound :
    ∀ omega, (data omega).stepEnergy 0 ≤ (params.delta : ℝ) ^ 2
  /-- The canonical initial allowance is nonnegative. -/
  initial_budget_nonneg :
    0 ≤ LALM.StochasticRun.initialStepBound h params

namespace FiniteStoppedPathWitness

variable (witness : FiniteStoppedPathWitness attempt)

/-- Helper for Theorem 3.7: the stopped base-step sum equals the witnessed
active-prefix sum. -/
theorem baseStep_sum_eq_prefix (omega : Ω) :
    (∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k omega) =
      ∑ k ∈ Finset.range (witness.prefixLength omega),
        (witness.data omega).stepEnergy k := by
  have hsubset : Finset.range (witness.prefixLength omega) ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le
      (Finset.mem_range.mp hk) (witness.prefixLength_le omega))
  have hactive :
      (∑ k ∈ Finset.range (witness.prefixLength omega),
          activeBaseStepIntegrand attempt k omega) =
        ∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k omega :=
    Finset.sum_subset hsubset (fun k hkK hkPrefix ↦ by
      apply witness.inactive_step_zero omega k
      · exact Nat.not_lt.mp (by
          intro hkLength
          exact hkPrefix (Finset.mem_range.mpr hkLength))
      · exact Finset.mem_range.mp hkK)
  have hdata :
      (∑ k ∈ Finset.range (witness.prefixLength omega),
          (witness.data omega).stepEnergy k) =
        ∑ k ∈ Finset.range (witness.prefixLength omega),
          activeBaseStepIntegrand attempt k omega := by
    apply Finset.sum_congr rfl
    intro k hk
    exact witness.stepEnergy_eq_active omega k (Finset.mem_range.mp hk)
  exact hactive.symm.trans hdata.symm

/-- Helper for Theorem 3.7: the stopped estimator-error sum equals the
witnessed active-prefix sum. -/
theorem error_sum_eq_prefix (omega : Ω) :
    (∑ k ∈ Finset.range K, activeGradientErrorIntegrand attempt k omega) =
      ∑ k ∈ Finset.range (witness.prefixLength omega),
        (witness.data omega).errorEnergy k := by
  have hsubset : Finset.range (witness.prefixLength omega) ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr (Nat.lt_of_lt_of_le
      (Finset.mem_range.mp hk) (witness.prefixLength_le omega))
  have hactive :
      (∑ k ∈ Finset.range (witness.prefixLength omega),
          activeGradientErrorIntegrand attempt k omega) =
        ∑ k ∈ Finset.range K, activeGradientErrorIntegrand attempt k omega :=
    Finset.sum_subset hsubset (fun k hkK hkPrefix ↦ by
      apply witness.inactive_error_zero omega k
      · exact Nat.not_lt.mp (by
          intro hkLength
          exact hkPrefix (Finset.mem_range.mpr hkLength))
      · exact Finset.mem_range.mp hkK)
  have hdata :
      (∑ k ∈ Finset.range (witness.prefixLength omega),
          (witness.data omega).errorEnergy k) =
        ∑ k ∈ Finset.range (witness.prefixLength omega),
          activeGradientErrorIntegrand attempt k omega := by
    apply Finset.sum_congr rfl
    intro k hk
    exact witness.errorEnergy_eq_active omega k (Finset.mem_range.mp hk)
  exact hactive.symm.trans hdata.symm

/-- Helper for Theorem 3.7: a finite stopped-path witness constructs the
pathwise base-step telescope required by `FiniteStoppedPath`. -/
theorem pathwise_baseStepEnergy_le
    (witness : FiniteStoppedPathWitness attempt) (omega : Ω) :
    pathwiseBaseStepEnergy attempt omega ≤
      LALM.StochasticRun.initialStepBound h params +
        LALM.StochasticRun.errorStepConstant h params *
          pathwiseGradientErrorEnergy attempt omega := by
  have herror_nonneg : ∀ k < witness.prefixLength omega,
      0 ≤ (witness.data omega).errorEnergy k := by
    intro k hk
    rw [witness.errorEnergy_eq_active omega k hk]
    exact activeGradientErrorIntegrand_nonneg attempt k omega
  have hprefix :=
    FinitePrefixLyapunovData.sum_stepEnergy_le (witness.data omega)
      (witness.prefixLength_pos omega) herror_nonneg
      (witness.initial_step_bound omega)
  change (∑ k ∈ Finset.range K, activeBaseStepIntegrand attempt k omega) ≤
    LALM.StochasticRun.initialStepBound h params +
      LALM.StochasticRun.errorStepConstant h params *
        ∑ k ∈ Finset.range K, activeGradientErrorIntegrand attempt k omega
  rw [witness.baseStep_sum_eq_prefix omega,
    witness.error_sum_eq_prefix omega]
  exact hprefix

end FiniteStoppedPathWitness

/-- Helper for Theorem 3.7: a finite stopped-path witness produces a
`FiniteStoppedPath` with the canonical initial budget and error coefficient. -/
theorem finiteStoppedPath_exists_of_witness
    (witness : FiniteStoppedPathWitness attempt) :
    ∃ path : FiniteStoppedPath attempt,
      path.baseStepBudget = LALM.StochasticRun.initialStepBound h params ∧
        path.errorStepCoefficient = LALM.StochasticRun.errorStepConstant h params := by
  have herror_nonneg :
      0 ≤ LALM.StochasticRun.errorStepConstant h params := by
    rw [LALM.StochasticRun.errorStepConstant_def,
      LALM.StochasticRun.lyapunovErrorConstant_def,
      LALM.multiplierErrorConstant_def]
    positivity
  have hpathwise : ∀ omega,
      pathwiseBaseStepEnergy attempt omega ≤
        LALM.StochasticRun.initialStepBound h params +
          LALM.StochasticRun.errorStepConstant h params *
            pathwiseGradientErrorEnergy attempt omega := by
    intro omega
    exact witness.pathwise_baseStepEnergy_le omega
  let path : FiniteStoppedPath attempt := {
    invariant := witness.invariant
    baseStepBudget := LALM.StochasticRun.initialStepBound h params
    errorStepCoefficient := LALM.StochasticRun.errorStepConstant h params
    baseStepBudget_nonneg := witness.initial_budget_nonneg
    errorStepCoefficient_nonneg := herror_nonneg
    pathwise_baseStepEnergy_le := hpathwise
  }
  exact ⟨path, rfl, rfl⟩

end LALM.FiniteStopped.StoppedAttemptAnalysis

end
