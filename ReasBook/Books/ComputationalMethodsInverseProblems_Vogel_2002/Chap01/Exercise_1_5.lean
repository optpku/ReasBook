/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_5.Filters

public section

namespace SpectralFilter

/-- Helper for Exercise 1.5: a square bound on `s` yields the reciprocal
square-root bound needed in the TSVD branch where the filter equals `1`. -/
lemma one_div_le_one_div_sqrt_of_le_sq
    {α s : ℝ} (hα : 0 < α) (hs : 0 < s) (hαs : α ≤ s ^ 2) :
    1 / s ≤ 1 / Real.sqrt α := by
  -- Convert the square inequality into the direct comparison `√α ≤ s`.
  have hsqrt_le : Real.sqrt α ≤ s := by
    rw [Real.sqrt_le_left (le_of_lt hs)]
    simpa using hαs
  -- Reciprocal monotonicity gives the desired bound once positivity is known.
  exact one_div_le_one_div_of_le (Real.sqrt_pos_of_pos hα) hsqrt_le

/-- Helper for Exercise 1.5: evaluating the Tikhonov filter at `s ^ 2` and
then dividing by `s` simplifies to the stable ratio `s / (α + s ^ 2)`. -/
lemma tikhonovAtSquare_div_eq_ratio
    {α s : ℝ} (hs : s ≠ 0) :
    tikhonov α (s ^ 2) / s = s / (α + s ^ 2) := by
  -- Normalize the nested divisions once so the main theorem can stay in one spelling.
  rw [tikhonov, div_div, pow_two]
  simpa [pow_two] using (mul_div_mul_right s (α + s * s) hs)

/-- Helper for Exercise 1.5: the normalized Tikhonov ratio satisfies the source
bound from equation `(1.21)`. -/
lemma tikhonovRatio_le_one_div_sqrt
    {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    s / (α + s ^ 2) ≤ 1 / Real.sqrt α := by
  have hsqrt : 0 < Real.sqrt α := Real.sqrt_pos_of_pos hα
  have hden : 0 < α + s ^ 2 := by
    positivity
  -- The core comparison is the quadratic inequality coming from `(s - √α)^2 ≥ 0`.
  have hquad : s * Real.sqrt α ≤ α + s ^ 2 := by
    have hsq_nonneg : 0 ≤ (s - Real.sqrt α) ^ 2 := by
      positivity
    nlinarith [hsq_nonneg, Real.sq_sqrt (le_of_lt hα)]
  -- Cross-multiply through the positive denominators to finish in the ratio form.
  have hstep : s ≤ (α + s ^ 2) / Real.sqrt α := by
    exact (le_div_iff₀ hsqrt).2 hquad
  exact (div_le_iff₀ hden).2 (by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hstep)

/-- First bound for Exercise 1.5: the TSVD filter function from equation `(1.11)` satisfies
the source bound `w_α(s ^ 2) / s ≤ 1 / Real.sqrt α` from equation `(1.21)` when
`0 < α` and `0 < s`. -/
theorem tsvdInverseBound
    {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    tsvd α (s ^ 2) / s ≤ 1 / Real.sqrt α := by
  by_cases hcut : α ≤ s ^ 2
  · -- In the retained branch, `tsvd` is `1`, so only the reciprocal estimate remains.
    simp only [tsvd, hcut, if_true]
    exact one_div_le_one_div_sqrt_of_le_sq hα hs hcut
  · -- In the truncated branch, the left-hand side vanishes and positivity closes the goal.
    simp only [tsvd, hcut, if_false]
    rw [zero_div]
    positivity

/-- Second bound for Exercise 1.5: the Tikhonov filter function from equation `(1.13)`
satisfies the source bound `w_α(s ^ 2) / s ≤ 1 / Real.sqrt α` from equation
`(1.21)` when `0 < α` and `0 < s`. -/
theorem tikhonovInverseBound
    {α s : ℝ} (hα : 0 < α) (hs : 0 < s) :
    tikhonov α (s ^ 2) / s ≤ 1 / Real.sqrt α := by
  -- Rewrite once to the normalized ratio form and apply the scalar bound there.
  rw [tikhonovAtSquare_div_eq_ratio hs.ne']
  exact tikhonovRatio_le_one_div_sqrt hα hs

/-- Exercise 1.5. Either explicit spectral filter satisfies the source
bound `w_α(s ^ 2) / s ≤ 1 / Real.sqrt α` from equation `(1.21)` when
`0 < α` and `0 < s`. This is the reusable bridge for downstream arguments that
reason by cases on `w = tsvd ∨ w = tikhonov`. -/
theorem inverseBound_of_eq_tsvd_or_tikhonov
    {w : ℝ → ℝ → ℝ} {α s : ℝ}
    (h_filter : w = tsvd ∨ w = tikhonov) (hα : 0 < α) (hs : 0 < s) :
    w α (s ^ 2) / s ≤ 1 / Real.sqrt α := by
  rcases h_filter with rfl | rfl
  · exact tsvdInverseBound hα hs
  · exact tikhonovInverseBound hα hs

end SpectralFilter
