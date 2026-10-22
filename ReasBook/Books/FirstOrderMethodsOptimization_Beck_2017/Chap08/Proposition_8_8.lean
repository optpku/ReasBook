/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Algorithm_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_17_1
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_35

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open MeasureTheory
open scoped ProbabilityTheory

noncomputable section

section

variable {E : Type u} {Ω : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
variable [MeasurableSpace E] [BorelSpace E]
variable {f : E → ℝ} {C XStar : Set E} {fOpt δ Θ : ℝ} {m : ℕ}
variable (L : Fin m → ℝ)
variable (h_problem : IsConstrainedConvexProblem (fun x : E ↦ (f x : EReal)) C XStar fOpt)
variable (i : ℕ → Ω → Fin m) (g : ℕ → C → Fin m → E) (x0 : C)

local notation "x[" k "]" =>
  finite_sum_stochastic_projected_subgradient_method
    C h_problem.feasible_closed h_problem.feasible_convex Θ L i g x0 k

/- Proposition 8.8 is `bridge/view`: it specializes the general stochastic projected-subgradient
rate from Theorem 8.35 to the sampled finite-sum Algorithm 8.12 surface. The source-facing owners
are therefore the Algorithm 8.12 iterate sequence
`finite_sum_stochastic_projected_subgradient_method`, its named stepsize
`finite_sum_stochastic_projected_subgradient_stepsize`, and the finite-sum bound constant
`finite_sum_stochastic_subgradient_bound_constant L = √m * √(∑ i, L_i^2)`. The proof still
bridges through the Chapter 8 stochastic oracle package and Theorem 8.35. -/

-- Proof sketch: apply Theorem 8.35 (2) to the Algorithm 8.12 iterate sequence and use the
-- canonical stepsize owner
-- `projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_oracle.L_tilde_f
--   (finite_sum_stochastic_projected_subgradient_stepsize Θ L)`
-- to identify the named finite-sum stepsize with the generic half-squared-diameter rule from
-- Theorem 8.35. Then substitute the finite-sum estimate
-- `(2 * (1 + log 3)) * L_tilde_f ≤ δ * finite_sum_stochastic_subgradient_bound_constant L`
-- into the resulting right-hand side.
/-- Proposition 8.8: if the stochastic projected subgradient oracle along the sampled Algorithm
8.12 iterates has bound constant `L_tilde_f` controlled by
`δ * finite_sum_stochastic_subgradient_bound_constant L`, and Algorithm 8.12 uses the canonical
half-squared-diameter stepsize rule from Theorem 8.30, then the expected best objective gap of
the first `k + 1` iterates satisfies the finite-sum `O(1 / √k)` estimate `E(f_best^k) - fOpt ≤
  δ * finite_sum_stochastic_subgradient_bound_constant L * √(2 Θ) / √(k + 2)`. -/
theorem finite_sum_stochastic_projected_subgradient_expected_best_value_gap_le
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun n ω ↦ (x[n] ω : E))
        (fun n ω ↦ g n (x[n] ω) (i n ω)))
    (hΘ : C.HasHalfSquaredDiameterBound Θ)
    (h_stepsize :
      projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_oracle.L_tilde_f
        (finite_sum_stochastic_projected_subgradient_stepsize Θ L))
    (h_oracle_bound :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤
        δ * finite_sum_stochastic_subgradient_bound_constant L)
    {k : ℕ} (hk : 2 ≤ k) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤
      δ * finite_sum_stochastic_subgradient_bound_constant L *
        Real.sqrt (2 * Θ) / Real.sqrt ((k : ℝ) + 2) := by
  have h_rate :
      μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤
        (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f * Real.sqrt (2 * Θ) /
          Real.sqrt ((k : ℝ) + 2) :=
    stochastic_projected_subgradient_best_value_gap_le_of_half_squared_diameter_stepsize
      h_problem (fun n x ω ↦ g n x (i n ω))
      (finite_sum_stochastic_projected_subgradient_stepsize Θ L) x0
      h_oracle hΘ
      (projectedSubgradientUsesHalfSquaredDiameterStepsize_apply h_stepsize) hk
  have h_num :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f * Real.sqrt (2 * Θ) ≤
        δ * finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (2 * Θ) := by
    exact mul_le_mul_of_nonneg_right h_oracle_bound (Real.sqrt_nonneg _)
  have h_const :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f * Real.sqrt (2 * Θ) /
          Real.sqrt ((k : ℝ) + 2) ≤
        δ * finite_sum_stochastic_subgradient_bound_constant L * Real.sqrt (2 * Θ) /
          Real.sqrt ((k : ℝ) + 2) := by
    exact div_le_div_of_nonneg_right h_num (Real.sqrt_nonneg _)
  exact h_rate.trans h_const

-- Proof sketch: first apply
-- `finite_sum_stochastic_projected_subgradient_expected_best_value_gap_le` to obtain the
-- bound
-- `δ * finite_sum_stochastic_subgradient_bound_constant L * √(2 Θ) / √(k + 2)` on the expected
-- best objective gap. Then use the lower bound on `k` to rearrange this rate estimate into an
-- upper bound by `ε`.
/-- If the iteration index is at least the finite-sum complexity threshold from Proposition 8.8,
then the expected best objective gap is at most `ε`. -/
theorem
finite_sum_stochastic_projected_subgradient_expected_best_value_gap_le_epsilon_of_iteration_count
    (h_oracle :
      StochasticProjectedSubgradientOracle μ f
        (fun n ω ↦ (x[n] ω : E))
        (fun n ω ↦ g n (x[n] ω) (i n ω)))
    (hΘ : C.HasHalfSquaredDiameterBound Θ)
    (h_stepsize :
      projectedSubgradientUsesHalfSquaredDiameterStepsize Θ h_oracle.L_tilde_f
        (finite_sum_stochastic_projected_subgradient_stepsize Θ L))
    (h_oracle_bound :
      (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤
        δ * finite_sum_stochastic_subgradient_bound_constant L)
    {ε : ℝ} (hε : 0 < ε)
    (k : ℕ)
    (hk :
      max
          (δ ^ (2 : ℕ) * (2 * Θ) *
              (finite_sum_stochastic_subgradient_bound_constant L) ^ (2 : ℕ) /
              ε ^ (2 : ℕ) - 2)
          2 ≤
        (k : ℝ)) :
    μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤ ε := by
  let B : ℝ := finite_sum_stochastic_subgradient_bound_constant L
  have hB_nonneg : 0 ≤ B := by
    dsimp [B, finite_sum_stochastic_subgradient_bound_constant]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have h_oracle_bound' : (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f ≤ δ * B := by
    simpa [B] using h_oracle_bound
  have h_log3_pos : 0 < Real.log 3 := by
    exact Real.log_pos (by norm_num)
  have h_lhs_pos : 0 < (2 * (1 + Real.log 3)) * h_oracle.L_tilde_f := by
    nlinarith [h_log3_pos, h_oracle.L_tilde_f_pos]
  have hδ : 0 ≤ δ := by
    have h_rhs_pos : 0 < δ * B := lt_of_lt_of_le h_lhs_pos h_oracle_bound'
    by_contra hδ_neg
    have hδ_nonpos : δ ≤ 0 := le_of_lt (lt_of_not_ge hδ_neg)
    have h_rhs_nonpos : δ * B ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hδ_nonpos hB_nonneg
    linarith
  have hk_threshold :
      δ ^ (2 : ℕ) * (2 * Θ) * B ^ (2 : ℕ) / ε ^ (2 : ℕ) - 2 ≤ (k : ℝ) := by
    simpa [B] using le_trans (le_max_left _ _) hk
  have hk_two_real : (2 : ℝ) ≤ (k : ℝ) := le_trans (le_max_right _ _) hk
  have hk_two : 2 ≤ k := by
    exact_mod_cast hk_two_real
  have hΘ_nonneg : 0 ≤ Θ := by
    simpa using hΘ.bound x0.property x0.property
  have h_twoΘ_nonneg : 0 ≤ 2 * Θ := by
    nlinarith
  let M : ℝ := δ * B * Real.sqrt (2 * Θ)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    exact mul_nonneg (mul_nonneg hδ hB_nonneg) (Real.sqrt_nonneg _)
  have hM_sq : M ^ (2 : ℕ) = δ ^ (2 : ℕ) * (2 * Θ) * B ^ (2 : ℕ) := by
    dsimp [M]
    rw [pow_two]
    have hsqrt_sq : Real.sqrt (2 * Θ) * Real.sqrt (2 * Θ) = 2 * Θ := by
      nlinarith [Real.sq_sqrt h_twoΘ_nonneg]
    calc
      (δ * B * Real.sqrt (2 * Θ)) * (δ * B * Real.sqrt (2 * Θ))
          = (δ * δ) * (B * B) * (Real.sqrt (2 * Θ) * Real.sqrt (2 * Θ)) := by ring
      _ = (δ * δ) * (B * B) * (2 * Θ) := by rw [hsqrt_sq]
      _ = δ ^ (2 : ℕ) * (2 * Θ) * B ^ (2 : ℕ) := by ring
  have hk_iter : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (((k + 1 : ℕ) : ℝ)) := by
    have :
        δ ^ (2 : ℕ) * (2 * Θ) * B ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) + 1 := by
      nlinarith
    simpa [Nat.cast_add, hM_sq] using this
  have h_rate :
      μ[fun ω ↦ best_achieved_function_value f (fun n ↦ (x[n] ω : E)) k] - fOpt ≤
        M / Real.sqrt ((k : ℝ) + 2) := by
    simpa [M, B] using
      finite_sum_stochastic_projected_subgradient_expected_best_value_gap_le
        L h_problem i g x0 h_oracle hΘ h_stepsize h_oracle_bound hk_two
  have h_rate_to_epsilon' : M / Real.sqrt ((k : ℝ) + (1 + 1)) ≤ ε := by
    simpa [Nat.cast_add, add_assoc, add_left_comm, add_comm] using
      rate_bound_of_iteration_count_lb M ε (k + 1) hM_nonneg hε hk_iter
  have h_rate_to_epsilon : M / Real.sqrt ((k : ℝ) + 2) ≤ ε := by
    convert h_rate_to_epsilon' using 1
    ring_nf
  exact h_rate.trans h_rate_to_epsilon

end
