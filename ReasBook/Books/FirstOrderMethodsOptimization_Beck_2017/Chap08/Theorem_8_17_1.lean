/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [PseudoMetricSpace E]

/-- Helper for Theorem 8.17.1: the numerator in the rate bound is nonnegative whenever `L_f` is
nonnegative. -/
lemma rate_bound_numerator_nonneg
    (x0 : E) (XStar : Set E) (Lf : ℝ) (hLf : 0 ≤ Lf) :
    0 ≤ Lf * Metric.infDist x0 XStar := by
  -- The rate numerator is a product of two nonnegative factors.
  exact mul_nonneg hLf (Metric.infDist_nonneg)

/-- Helper for Theorem 8.17.1: a rate bound `M / √(k + 1) ≤ ε` with `ε > 0` yields the equivalent
iteration lower bound after multiplying by the positive square root and squaring. -/
lemma iteration_count_lb_of_rate_bound
    (M ε : ℝ) (k : ℕ) (hM : 0 ≤ M) (hε : 0 < ε)
    (h_bound : M / Real.sqrt ((k : ℝ) + 1) ≤ ε) :
    M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
  -- The square root denominator is positive because `k + 1 > 0`.
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 1) := le_of_lt hsqrt_pos
  -- Multiplying by the positive square root isolates the numerator `M`.
  have h_mul : M ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    rw [div_le_iff₀ hsqrt_pos] at h_bound
    simpa [mul_comm] using h_bound
  have h_right_nonneg : 0 ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    exact mul_nonneg (le_of_lt hε) hsqrt_nonneg
  -- Squaring preserves the inequality because both sides are nonnegative.
  have h_sq : M ^ (2 : ℕ) ≤ (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
    nlinarith [h_mul, hM, h_right_nonneg]
  have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity))
  have h_num : M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := by
    nlinarith [h_sq, hsqrt_sq]
  have h_div : M ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 1 := by
    rw [div_le_iff₀ (by positivity : 0 < ε ^ (2 : ℕ))]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_num
  nlinarith

/-- Helper for Theorem 8.17.1: the iteration lower bound implies the corresponding rate bound
after rewriting it as a squared inequality and taking square roots. -/
lemma rate_bound_of_iteration_count_lb
    (M ε : ℝ) (k : ℕ) (hM : 0 ≤ M) (hε : 0 < ε)
    (hk : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ)) :
    M / Real.sqrt ((k : ℝ) + 1) ≤ ε := by
  -- Rearranging the iteration threshold gives a bound on `M²`.
  have h_div : M ^ (2 : ℕ) / ε ^ (2 : ℕ) ≤ (k : ℝ) + 1 := by
    nlinarith
  have h_num : M ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * ε ^ (2 : ℕ) := by
    rw [div_le_iff₀ (by positivity : 0 < ε ^ (2 : ℕ))] at h_div
    simpa [mul_comm, mul_left_comm, mul_assoc] using h_div
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    apply Real.sqrt_pos.2
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt ((k : ℝ) + 1) := le_of_lt hsqrt_pos
  have h_right_nonneg : 0 ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    exact mul_nonneg (le_of_lt hε) hsqrt_nonneg
  have hsqrt_sq : Real.sqrt ((k : ℝ) + 1) ^ (2 : ℕ) = (k : ℝ) + 1 := by
    simpa [pow_two] using (Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity))
  -- Matching square bounds and nonnegativity recover the unsquared rate estimate.
  have h_sq : M ^ (2 : ℕ) ≤ (ε * Real.sqrt ((k : ℝ) + 1)) ^ (2 : ℕ) := by
    nlinarith [h_num, hsqrt_sq]
  have h_mul : M ≤ ε * Real.sqrt ((k : ℝ) + 1) := by
    nlinarith [h_sq, hM, h_right_nonneg]
  rw [div_le_iff₀ hsqrt_pos]
  simpa [mul_comm] using h_mul

/-- The numerical rate bound `L_f d_{X^*}(x^0) / √(k + 1) ≤ ε` is equivalent to the corresponding
lower bound on the iteration index `k`, after squaring both sides. -/
-- Proof sketch: use that `Metric.infDist` is nonnegative and that `ε > 0`, so multiplying by
-- `ε` and `Real.sqrt (k + 1)` preserves the inequality. Then square both sides and rearrange the
-- resulting real inequality.
theorem rate_bound_le_epsilon_iff_iteration_count_lb
    (x0 : E) (XStar : Set E) (Lf ε : ℝ) (k : ℕ)
    (hLf : 0 ≤ Lf) (hε : 0 < ε) :
    Lf * Metric.infDist x0 XStar / Real.sqrt (k + 1) ≤ ε ↔
      Lf ^ (2 : ℕ) * Metric.infDist x0 XStar ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
  let M : ℝ := Lf * Metric.infDist x0 XStar
  have hM : 0 ≤ M := by
    -- Package the numerator into a single nonnegative scalar.
    simpa [M] using rate_bound_numerator_nonneg x0 XStar Lf hLf
  have h_expand : M ^ (2 : ℕ) = Lf ^ (2 : ℕ) * Metric.infDist x0 XStar ^ (2 : ℕ) := by
    -- Expanding `M` matches the textbook numerator `L_f² d_{X^*}(x^0)²`.
    dsimp [M]
    ring
  constructor
  · intro h_bound
    -- Convert the displayed rate bound into the scalar form and square it.
    have h_iter_M :
        M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
      exact iteration_count_lb_of_rate_bound M ε k hM hε (by simpa [M] using h_bound)
    rw [h_expand] at h_iter_M
    exact h_iter_M
  · intro h_iter
    -- Rewrite the iteration threshold in terms of the scalar numerator `M`.
    have h_iter_M : M ^ (2 : ℕ) / ε ^ (2 : ℕ) - 1 ≤ (k : ℝ) := by
      simpa [h_expand] using h_iter
    -- Recover the displayed rate bound from the scalar iteration threshold.
    simpa [M] using rate_bound_of_iteration_count_lb M ε k hM hε h_iter_M

/-- Theorem 8.17.1: if the previously established projected-subgradient bound
`f_best - f_opt ≤ L_f d_{X^*}(x^0) / √(k + 1)` holds, then the sufficient condition
`L_f d_{X^*}(x^0) / √(k + 1) ≤ ε` implies `f_best - f_opt ≤ ε`. In particular, this yields the
usual `O(ε⁻²)` iteration estimate through the companion iteration-count inequality. -/
-- Proof sketch: combine the assumed bound on the best attained objective gap with the displayed
-- upper bound `L_f d_{X^*}(x^0) / √(k + 1) ≤ ε` by transitivity.
theorem best_function_value_gap_le_epsilon_of_rate_bound
    (x0 : E) (XStar : Set E) (fBest fOpt Lf ε : ℝ) (k : ℕ)
    (h_rate : fBest - fOpt ≤ Lf * Metric.infDist x0 XStar / Real.sqrt (k + 1))
    (h_bound : Lf * Metric.infDist x0 XStar / Real.sqrt (k + 1) ≤ ε) :
    fBest - fOpt ≤ ε := by
  -- The assumed rate estimate already bounds the objective gap by the displayed quantity.
  exact h_rate.trans h_bound

end
