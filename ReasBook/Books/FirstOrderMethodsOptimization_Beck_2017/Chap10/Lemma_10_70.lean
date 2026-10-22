/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

/- `prompt_add/` is absent in this workspace, so the owner-abstraction review is done against
mathlib and the nearby Chapter 10/11 files.

Domain sampling for this scalar recurrence uses:
- `PosReal` from Definition 6.7 as the chapter's owner for genuinely positive scalar parameters;
- `non_euclidean_gradient_step_decrease_ge_sq_objective_gap` from Lemma 10.69 as the direct
  upstream source of the recurrence in Theorem 10.71; and
- `nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence` from
  Chapter 11 as the nearby same-domain sequence-rate lemma.

This item is therefore kept `source-facing`: the public owner is still the plain sequence
`a : ℕ → ℝ`, while the positive recurrence constant is refined to the existing owner `PosReal`
instead of a raw real together with a separate positivity proof. The reciprocal-step estimate
below is derived API, kept private. The chapter's textbook nonnegativity hypothesis is redundant
for this source-facing conclusion, so it is not kept as primitive theorem input. -/

private lemma reciprocal_step_of_quadratic_decrease
    {a b : ℝ} {γ : PosReal} (ha : 0 < a) (hb : 0 < b) (hba : b ≤ a)
    (hstep : a - b ≥ (1 / (γ : ℝ)) * a ^ (2 : ℕ)) :
    1 / b - 1 / a ≥ 1 / (γ : ℝ) := by
  have hden : 0 < a * b := mul_pos ha hb
  have hrecip : 1 / b - 1 / a = (a - b) / (a * b) := by
    field_simp [ha.ne', hb.ne']
  rw [hrecip]
  have hab_nonneg : 0 ≤ a - b := sub_nonneg.mpr hba
  have hmul : a * b ≤ a ^ (2 : ℕ) := by
    simpa [pow_two] using mul_le_mul_of_nonneg_left hba ha.le
  have hdiv : (a - b) / (a ^ (2 : ℕ)) ≤ (a - b) / (a * b) := by
    exact div_le_div_of_nonneg_left hab_nonneg hden hmul
  have hsq_pos : 0 < a ^ (2 : ℕ) := by positivity
  have hstep_div : 1 / γ ≤ (a - b) / (a ^ (2 : ℕ)) := by
    rw [le_div_iff₀ hsq_pos]
    simpa [mul_assoc] using hstep
  exact le_trans hstep_div hdiv

-- Proof sketch: the recurrence implies `a (k + 1) ≤ a k`, hence monotonicity. If `a k ≤ 0`,
-- then the bound is immediate because `γ / k > 0`. If `a k > 0`, monotonicity forces every
-- earlier term `a n` with `n ≤ k` to be positive, so dividing by `a k * a (k + 1)` gives
-- `1 / a (k + 1) - 1 / a k ≥ 1 / γ`. Summing this inequality from `0` to `k - 1` yields
-- `1 / a k ≥ k / γ`, hence `a k ≤ γ / k` for every `k ≥ 1`.
/-- Lemma 10.70: a real sequence satisfying
`a k - a (k + 1) ≥ (1 / γ) * (a k)^2` for every `k` obeys the sublinear bound
`a k ≤ γ / k` for every `k ≥ 1`. -/
lemma sequence_le_gamma_div_of_step_difference_ge_inv_mul_sq
    {a : ℕ → ℝ} {γ : PosReal}
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a k) ^ (2 : ℕ))
    {k : ℕ} (hk : 1 ≤ k) :
    a k ≤ (γ : ℝ) / (k : ℝ) := by
  have hsucc : ∀ n : ℕ, a (n + 1) ≤ a n := by
    intro n
    have hsq_nonneg : 0 ≤ (1 / (γ : ℝ)) * (a n) ^ (2 : ℕ) := by
      exact mul_nonneg (one_div_nonneg.mpr (PosReal.coe_pos γ).le) (sq_nonneg (a n))
    linarith [hstep n]
  have ha_anti : Antitone a := antitone_nat_of_succ_le hsucc
  have hk_nat_pos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hk_pos : 0 < (k : ℝ) := Nat.cast_pos.mpr hk_nat_pos
  have hkγ_pos : 0 < (γ : ℝ) / (k : ℝ) := div_pos (PosReal.coe_pos γ) hk_pos
  by_cases hak_nonpos : a k ≤ 0
  · exact le_trans hak_nonpos hkγ_pos.le
  · have hak_pos : 0 < a k := lt_of_not_ge hak_nonpos
    have hpos : ∀ n : ℕ, n ≤ k → 0 < a n := by
      intro n hnk
      exact lt_of_lt_of_le hak_pos (ha_anti hnk)
    have hstep_recip : ∀ n : ℕ, n < k → 1 / a (n + 1) - 1 / a n ≥ 1 / (γ : ℝ) := by
      intro n hnk
      exact reciprocal_step_of_quadratic_decrease
        (hpos n (Nat.le_of_lt hnk))
        (hpos (n + 1) (Nat.succ_le_of_lt hnk))
        (hsucc n)
        (hstep n)
    have hsum_lower :
        ∑ n ∈ Finset.range k, (1 / (γ : ℝ) : ℝ) ≤
          ∑ n ∈ Finset.range k, (1 / a (n + 1) - 1 / a n) := by
      exact Finset.sum_le_sum fun n hn ↦ hstep_recip n (Finset.mem_range.mp hn)
    have htelescoping :
        ∑ n ∈ Finset.range k, (1 / a (n + 1) - 1 / a n) = 1 / a k - 1 / a 0 := by
      simpa using (Finset.sum_range_sub (fun n ↦ (1 / a n : ℝ)) k)
    rw [htelescoping] at hsum_lower
    have hrecip_lower : (k : ℝ) * (1 / (γ : ℝ)) ≤ 1 / a k - 1 / a 0 := by
      simpa using hsum_lower
    have hrecip_nonneg : 0 ≤ 1 / a 0 := by
      exact one_div_nonneg.mpr (hpos 0 (Nat.zero_le _)).le
    have hrecip_bound : (k : ℝ) * (1 / (γ : ℝ)) ≤ 1 / a k := by
      linarith
    have htarget_recip : 1 / ((γ : ℝ) / (k : ℝ)) ≤ 1 / a k := by
      simpa [div_eq_mul_inv, one_div_div, mul_comm, mul_left_comm, mul_assoc] using hrecip_bound
    exact (one_div_le_one_div hkγ_pos hak_pos).1 htarget_recip

end
