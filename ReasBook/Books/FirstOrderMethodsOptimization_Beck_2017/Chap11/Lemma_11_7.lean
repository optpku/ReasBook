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
mathlib and nearby project files. Domain sampling against the closest project recurrences,
`Chap10/Lemma_10_70`, `Chap13/Lemma_13_13`, and the chapter-wide positive-parameter owner
`PosReal` from `Chap06/Definition_6_7` shows the intended split:
- the public source-facing owner remains the plain sequence `a : ℕ → ℝ`;
- the step inequality remains theorem-level input rather than being packaged into a wrapper; and
- genuinely positive scalar data such as the recurrence constant belongs in `PosReal`, not in a
  raw real parameter plus a separate positivity proof.
This item is therefore kept `source-facing`, with the two independent conclusions split into
atomic lemmas. -/

variable {a : ℕ → ℝ} {γ : PosReal}

variable (ha_nonneg : ∀ k : ℕ, 0 ≤ a k)
variable (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)

/-- Helper for Lemma 11.7: the number of halving steps among the first `m` transitions. -/
abbrev halvingCount (a : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k ↦ a (k + 1) ≤ a k / 2).card

/-- Helper for Lemma 11.7: the number of strict-half-ratio steps among the first `m`
transitions. -/
abbrev strictHalfRatioCount (a : ℕ → ℝ) (m : ℕ) : ℕ :=
  ((Finset.range m).filter fun k ↦ a k / 2 < a (k + 1)).card

/-- Helper for Lemma 11.7: the quadratic recurrence makes the sequence antitone. -/
lemma quadratic_step_recurrence_antitone
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2) :
    Antitone a := by
  -- Each step decreases because the quadratic term in the recurrence is nonnegative.
  have hsucc : ∀ k : ℕ, a (k + 1) ≤ a k := by
    intro k
    have hsq_nonneg : 0 ≤ (1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ) := by
      exact mul_nonneg (one_div_nonneg.mpr (PosReal.coe_pos γ).le) (sq_nonneg (a (k + 1)))
    linarith [hstep k]
  exact antitone_nat_of_succ_le hsucc

/-- Helper for Lemma 11.7: the halving-step count gains one exactly when the latest step halves. -/
private lemma halvingCount_succ (m : ℕ) :
    halvingCount a (m + 1) =
      halvingCount a m + if a (m + 1) ≤ a m / 2 then 1 else 0 := by
  classical
  by_cases hm : a (m + 1) ≤ a m / 2
  · rw [halvingCount, halvingCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]
  · rw [halvingCount, halvingCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]

/-- Helper for Lemma 11.7: the strict-half-ratio count gains one exactly when the latest step is
strictly above the half ratio. -/
private lemma strictHalfRatioCount_succ (m : ℕ) :
    strictHalfRatioCount a (m + 1) =
      strictHalfRatioCount a m + if a m / 2 < a (m + 1) then 1 else 0 := by
  classical
  by_cases hm : a m / 2 < a (m + 1)
  · rw [strictHalfRatioCount, strictHalfRatioCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]
  · rw [strictHalfRatioCount, strictHalfRatioCount, Finset.range_add_one, Finset.filter_insert]
    simp [hm]

/-- Helper for Lemma 11.7: each prefix step is either a halving step or a strict-half-ratio
step, so the two counts partition the prefix. -/
private lemma halvingCount_add_strictHalfRatioCount_eq (m : ℕ) :
    halvingCount a m + strictHalfRatioCount a m = m := by
  classical
  -- The two predicates are exact complements on `ℝ`.
  simpa [halvingCount, strictHalfRatioCount, not_le] using
    ((Finset.range m).card_filter_add_card_filter_not fun k ↦ a (k + 1) ≤ a k / 2)

/-- Helper for Lemma 11.7: a strict-half-ratio step yields a uniform reciprocal increment. -/
lemma reciprocal_increment_ge_one_div_two_gamma_of_strict_half_ratio
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)
    (k : ℕ)
    (hak : 0 < a k)
    (hak_succ : 0 < a (k + 1))
    (hhalf : a k / 2 < a (k + 1)) :
    1 / (2 * (γ : ℝ)) ≤ 1 / a (k + 1) - 1 / a k := by
  have hγ_ne : (γ : ℝ) ≠ 0 := (PosReal.coe_pos γ).ne'
  have hrecip :
      1 / a (k + 1) - 1 / a k = (a k - a (k + 1)) / (a k * a (k + 1)) := by
    field_simp [hak.ne', hak_succ.ne']
  rw [hrecip]
  -- Divide the quadratic decrease inequality by the positive denominator.
  have hden_pos : 0 < a k * a (k + 1) := mul_pos hak hak_succ
  have hstep_div :
      ((1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) / (a k * a (k + 1)) ≤
        (a k - a (k + 1)) / (a k * a (k + 1)) := by
    exact div_le_div_of_nonneg_right (hstep k) (le_of_lt hden_pos)
  have hsimpl :
      ((1 / (γ : ℝ)) * (a (k + 1)) ^ (2 : ℕ)) / (a k * a (k + 1)) =
        (1 / (γ : ℝ)) * (a (k + 1) / a k) := by
    field_simp [hak.ne', hak_succ.ne', hγ_ne]
  rw [hsimpl] at hstep_div
  have hratio : (1 / 2 : ℝ) < a (k + 1) / a k := by
    have hhalf' : (1 / 2 : ℝ) * a k < a (k + 1) := by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hhalf
    rw [lt_div_iff₀ hak]
    exact hhalf'
  have hleft :
      1 / (2 * (γ : ℝ)) = (1 / (γ : ℝ)) * (1 / 2 : ℝ) := by
    field_simp [hγ_ne]
  have hratio_mul :
      (1 / (γ : ℝ)) * (1 / 2 : ℝ) ≤ (1 / (γ : ℝ)) * (a (k + 1) / a k) := by
    exact mul_le_mul_of_nonneg_left hratio.le (one_div_nonneg.mpr (PosReal.coe_pos γ).le)
  calc
    1 / (2 * (γ : ℝ)) = (1 / (γ : ℝ)) * (1 / 2 : ℝ) := hleft
    _ ≤ (1 / (γ : ℝ)) * (a (k + 1) / a k) := hratio_mul
    _ ≤ (a k - a (k + 1)) / (a k * a (k + 1)) := hstep_div

/-- Helper for Lemma 11.7: every halving step contributes one factor `1 / 2` to the prefix
bound. -/
lemma geometric_prefix_bound_of_halving_count
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)
    (m : ℕ) :
    a m ≤ ((1 / 2 : ℝ) ^ halvingCount a m) * a 0 := by
  -- Induct on the prefix length and record whether the last step halves.
  induction m with
  | zero =>
      simp [halvingCount]
  | succ m ih =>
      have ha_anti := quadratic_step_recurrence_antitone hstep
      -- Make the section parameter explicit so the local count recursion elaborates stably.
      have hcount := halvingCount_succ (a := a) m
      by_cases hhalf : a (m + 1) ≤ a m / 2
      · -- A halving step adds one more factor `1 / 2`.
        rw [hcount, if_pos hhalf]
        calc
          a (m + 1) ≤ a m / 2 := hhalf
          _ ≤ (((1 / 2 : ℝ) ^ halvingCount a m) * a 0) / 2 := by
            exact div_le_div_of_nonneg_right ih (by norm_num)
          _ = ((1 / 2 : ℝ) ^ (halvingCount a m + 1)) * a 0 := by
            rw [div_eq_mul_inv, show (2 : ℝ)⁻¹ = (1 / 2 : ℝ) by norm_num, pow_succ]
            ring
      · -- Otherwise the halving count is unchanged, and monotonicity controls the last step.
        rw [hcount, if_neg hhalf]
        calc
          a (m + 1) ≤ a m := ha_anti (Nat.le_succ m)
          _ ≤ ((1 / 2 : ℝ) ^ halvingCount a m) * a 0 := ih

/-- Helper for Lemma 11.7: every strict-half-ratio step contributes one reciprocal increment of
size at least `1 / (2γ)`. -/
lemma reciprocal_prefix_bound_of_strict_half_ratio_count
    (hstep : ∀ k : ℕ, a k - a (k + 1) ≥ (1 / (γ : ℝ)) * (a (k + 1)) ^ 2)
    (m : ℕ) (hm_pos : 0 < a m) :
    (strictHalfRatioCount a m : ℝ) / (2 * (γ : ℝ)) ≤ 1 / a m - 1 / a 0 := by
  -- Induct on the prefix length and split according to the final step of the dichotomy.
  induction m with
  | zero =>
      simp [strictHalfRatioCount]
  | succ m ih =>
      have ha_anti := quadratic_step_recurrence_antitone hstep
      -- Make the section parameter explicit so the local count recursion elaborates stably.
      have hcount := strictHalfRatioCount_succ (a := a) m
      have hm_prev_pos : 0 < a m := lt_of_lt_of_le hm_pos (ha_anti (Nat.le_succ m))
      by_cases hstrict : a m / 2 < a (m + 1)
      · -- A strict-half-ratio step adds one more reciprocal increment.
        have hprefix := ih hm_prev_pos
        have hinc :=
          reciprocal_increment_ge_one_div_two_gamma_of_strict_half_ratio
            hstep m hm_prev_pos hm_pos hstrict
        rw [hcount, if_pos hstrict]
        have hcast :
            ((strictHalfRatioCount a m + 1 : ℕ) : ℝ) / (2 * (γ : ℝ)) =
              (strictHalfRatioCount a m : ℝ) / (2 * (γ : ℝ)) + 1 / (2 * (γ : ℝ)) := by
          rw [Nat.cast_add, Nat.cast_one, add_div]
        rw [hcast]
        linarith
      · -- Without a strict-half-ratio step, the count stays fixed and reciprocals still increase.
        rw [hcount, if_neg hstrict]
        have hprefix := ih hm_prev_pos
        have hrecip_mono : 1 / a m ≤ 1 / a (m + 1) := by
          exact one_div_le_one_div_of_le hm_pos (ha_anti (Nat.le_succ m))
        have htarget : 1 / a m - 1 / a 0 ≤ 1 / a (m + 1) - 1 / a 0 := by
          linarith
        exact le_trans hprefix htarget

/-- Helper for Lemma 11.7: if the halving and strict-half-ratio counts partition a prefix, then at
least one of the two counts is at least half of the prefix length. -/
private lemma half_count_dichotomy_of_partition {h r m : ℕ} (hsum : h + r = m) :
    ((m : ℝ) / 2 ≤ h) ∨ ((m : ℝ) / 2 ≤ r) := by
  -- Cast the exact partition identity to `ℝ` and split by whether the first count already
  -- reaches half of the prefix length.
  have hsum_real : (h : ℝ) + r = m := by
    exact_mod_cast hsum
  by_cases hh : ((m : ℝ) / 2 ≤ h)
  · exact Or.inl hh
  · right
    linarith

/-- Helper for Lemma 11.7: once at least half of the first `m` steps are halving steps, the
geometric prefix bound is at most the textbook target `((1 / 2) ^ (m / 2)) * a0`. -/
private lemma geometric_branch_le_target_of_halving_count
    {a0 : ℝ} (ha0 : 0 ≤ a0) {h m : ℕ}
    (hhalf : ((m : ℝ) / 2 ≤ h)) :
    ((1 / 2 : ℝ) ^ h) * a0 ≤ ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 := by
  -- Since `0 < 1 / 2 < 1`, increasing the exponent only decreases the real power.
  have hpow :
      ((1 / 2 : ℝ) ^ h) ≤ (1 / 2 : ℝ) ^ ((m : ℝ) / 2) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) h]
    exact Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) hhalf
  exact mul_le_mul_of_nonneg_right hpow ha0

/-- Helper for Lemma 11.7: once at least half of the first `m` steps are strict-half-ratio steps,
the reciprocal prefix bound inverts to the textbook sublinear target `4γ / m`. -/
private lemma sublinear_branch_le_target_of_strict_half_ratio_count
    {x : ℝ} (hx : 0 < x) {r m : ℕ} (hm : 1 ≤ m)
    (hhalf : ((m : ℝ) / 2 ≤ r))
    (hrecip : (r : ℝ) / (2 * (γ : ℝ)) ≤ 1 / x) :
    x ≤ 4 * (γ : ℝ) / (m : ℝ) := by
  -- First convert the count lower bound into the linear estimate `m ≤ 2r`.
  have hm_real_pos : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.succ_pos 0) hm)
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hγ_pos : 0 < (γ : ℝ) := PosReal.coe_pos γ
  have htwoγ_pos : 0 < 2 * (γ : ℝ) := by positivity
  have hm_le_two_r : (m : ℝ) ≤ 2 * (r : ℝ) := by
    linarith
  -- Next clear the reciprocal inequality to obtain a direct bound on `r * x`.
  have hr_le_div : (r : ℝ) ≤ (2 * (γ : ℝ)) / x := by
    have hdiv := (div_le_iff₀ htwoγ_pos).mp hrecip
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hrx_le : (r : ℝ) * x ≤ 2 * (γ : ℝ) := by
    calc
      (r : ℝ) * x ≤ ((2 * (γ : ℝ)) / x) * x := by
        exact mul_le_mul_of_nonneg_right hr_le_div hx_nonneg
      _ = 2 * (γ : ℝ) := by
        field_simp [hx.ne']
  -- Finally combine `m ≤ 2r` with the estimate on `r * x` and divide by the positive `m`.
  have hmx_le : (m : ℝ) * x ≤ 4 * (γ : ℝ) := by
    calc
      (m : ℝ) * x ≤ (2 * (r : ℝ)) * x := by
        exact mul_le_mul_of_nonneg_right hm_le_two_r hx_nonneg
      _ = 2 * ((r : ℝ) * x) := by ring
      _ ≤ 2 * (2 * (γ : ℝ)) := by gcongr
      _ = 4 * (γ : ℝ) := by ring
  exact (le_div_iff₀ hm_real_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmx_le)

/-- Helper for Lemma 11.7: the logarithmic lower bound on the iteration count forces the
geometric term below `ε`. -/
lemma geometric_term_le_epsilon_of_log_bound
    {a0 : ℝ} (ha0 : 0 < a0) (ε : PosReal) {m : ℕ}
    (hlog :
      (2 / Real.log 2) * (Real.log a0 + Real.log (1 / (ε : ℝ))) ≤ (m : ℝ)) :
    ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 ≤ ε := by
  -- Convert the threshold into a bound on the logarithm of `a0 * (1 / ε)`.
  have hε_pos : 0 < (ε : ℝ) := PosReal.coe_pos ε
  have hlog2_pos : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num)
  have hscaled :
      Real.log a0 + Real.log (1 / (ε : ℝ)) ≤ ((m : ℝ) / 2) * Real.log 2 := by
    have hquot :
        (2 * (Real.log a0 + Real.log (1 / (ε : ℝ)))) / Real.log 2 ≤ (m : ℝ) := by
      have hrewrite :
          (2 / Real.log 2) * (Real.log a0 + Real.log (1 / (ε : ℝ))) =
            (2 * (Real.log a0 + Real.log (1 / (ε : ℝ)))) / Real.log 2 := by
        ring
      rw [hrewrite] at hlog
      exact hlog
    have hmul :
        2 * (Real.log a0 + Real.log (1 / (ε : ℝ))) ≤ (m : ℝ) * Real.log 2 := by
      exact (div_le_iff₀ hlog2_pos).mp hquot
    calc
      Real.log a0 + Real.log (1 / (ε : ℝ)) =
          (2 * (Real.log a0 + Real.log (1 / (ε : ℝ)))) / 2 := by
        ring
      _ ≤ ((m : ℝ) * Real.log 2) / 2 := by
        exact div_le_div_of_nonneg_right hmul (by norm_num)
      _ = ((m : ℝ) / 2) * Real.log 2 := by
        ring
  -- Compare the logarithms of the concrete quantities appearing in the target inequality.
  have hlog_compare :
      Real.log (a0 * (1 / (ε : ℝ))) ≤ Real.log ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
    rw [show Real.log (a0 * (1 / (ε : ℝ))) = Real.log (a0 * ((ε : ℝ)⁻¹)) by simp [one_div]]
    rw [Real.log_mul ha0.ne' (inv_ne_zero ε.2.ne')]
    rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
    simpa [one_div] using hscaled
  have hmul_le :
      a0 * (1 / (ε : ℝ)) ≤ (2 : ℝ) ^ ((m : ℝ) / 2) := by
    exact (Real.log_le_log_iff (mul_pos ha0 (one_div_pos.mpr hε_pos))
      (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _)).mp hlog_compare
  -- Rewrite the target as a division by `2 ^ (m / 2)` and divide the previous inequality.
  have hpow_pos : 0 < (2 : ℝ) ^ ((m : ℝ) / 2) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hbound :
      a0 / ((2 : ℝ) ^ ((m : ℝ) / 2)) ≤ ε := by
    have hmul_eps : a0 ≤ ε * ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
      calc
        a0 = (a0 * (1 / (ε : ℝ))) * ε := by
          field_simp [hε_pos.ne']
        _ ≤ ((2 : ℝ) ^ ((m : ℝ) / 2)) * ε := by
          gcongr
        _ = ε * ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
          ring
    exact (div_le_iff₀ hpow_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul_eps)
  have hhalf :
      (1 / 2 : ℝ) ^ ((m : ℝ) / 2) = ((2 : ℝ) ^ ((m : ℝ) / 2))⁻¹ := by
    rw [show (1 / 2 : ℝ) = ((2 : ℝ)⁻¹) by norm_num, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    ((1 / 2 : ℝ) ^ ((m : ℝ) / 2)) * a0 = a0 / ((2 : ℝ) ^ ((m : ℝ) / 2)) := by
      rw [hhalf]
      ring
    _ ≤ ε := hbound

-- Proof sketch: follow the textbook dichotomy on each ratio `a (k + 1) / a k`. Either
-- `a (k + 1) ≤ a k / 2`, which contributes one geometric halving step, or
-- `a (k + 1) / a k > 1 / 2`, in which case dividing the recurrence by `a k * a (k + 1)` gives a
-- uniform increment lower bound for `1 / a (k + 1) - 1 / a k`. Counting how many times each case
-- occurs among the first `n - 1` indices yields the maximum of the geometric and sublinear bounds.
include ha_nonneg hstep

/-- Lemma 11.7 (1): if a nonnegative scalar sequence satisfies
`a k - a (k + 1) ≥ (1 / γ) * a (k + 1)^2` for every `k` and some positive `γ`, then for every
`n ≥ 2` one has
`a n ≤ max {((1 / 2)^((n - 1) / 2)) * a 0, 4γ / (n - 1)}`. -/
lemma nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
    {n : ℕ} (hn : 2 ≤ n) :
    a n ≤
      max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
        (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
  -- Route correction: keep the count-partition proof skeleton and isolate the cast-heavy closing
  -- steps into the dedicated branch lemmas above.
  by_cases han_zero : a n = 0
  · -- If the terminal value vanishes, the bound is immediate from the nonnegative sublinear term.
    have hm_nat : 1 ≤ n - 1 := by
      omega
    have hm_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
      exact_mod_cast hm_nat
    have hsub_nonneg : 0 ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) := by
      exact div_nonneg (mul_nonneg (by norm_num) (PosReal.coe_pos γ).le) hm_pos.le
    rw [han_zero]
    exact le_trans (by norm_num) (le_trans hsub_nonneg (le_max_right _ _))
  · -- Otherwise `a n > 0`, so the reciprocal branch can be evaluated at the prefix `n - 1`.
    have ha_anti := quadratic_step_recurrence_antitone hstep
    have han_pos : 0 < a n := lt_of_le_of_ne (ha_nonneg n) (Ne.symm han_zero)
    have hprev_pos : 0 < a (n - 1) := by
      exact lt_of_lt_of_le han_pos (ha_anti (Nat.sub_le n 1))
    have hprefix_mono : a n ≤ a (n - 1) := ha_anti (Nat.sub_le n 1)
    have hpartition :
        halvingCount a (n - 1) + strictHalfRatioCount a (n - 1) = n - 1 :=
      halvingCount_add_strictHalfRatioCount_eq (a := a) (n - 1)
    have hcount_split :
        ((((n - 1 : ℕ) : ℝ) / 2) ≤ halvingCount a (n - 1)) ∨
          ((((n - 1 : ℕ) : ℝ) / 2) ≤ strictHalfRatioCount a (n - 1)) :=
      half_count_dichotomy_of_partition
        (h := halvingCount a (n - 1))
        (r := strictHalfRatioCount a (n - 1))
        (m := n - 1)
        hpartition
    cases hcount_split with
    | inl hhalf =>
        -- Many halving steps immediately give the geometric target.
        have hgeo_prefix :
            a (n - 1) ≤ ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 :=
          geometric_prefix_bound_of_halving_count (a := a) (γ := γ) hstep (n - 1)
        have hgeo_target :
            ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 ≤
              ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 :=
          geometric_branch_le_target_of_halving_count (ha_nonneg 0) hhalf
        calc
          a n ≤ a (n - 1) := hprefix_mono
          _ ≤ ((1 / 2 : ℝ) ^ halvingCount a (n - 1)) * a 0 := hgeo_prefix
          _ ≤ ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 := hgeo_target
          _ ≤
              max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
                (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := le_max_left _ _
    | inr hstrict =>
        -- Otherwise at least half of the steps are strict-half-ratio steps, so reciprocals grow
        -- linearly and invert to the sublinear target.
        have hm : 1 ≤ n - 1 := by
          omega
        have hrecip_prefix :
            (strictHalfRatioCount a (n - 1) : ℝ) / (2 * (γ : ℝ)) ≤
              1 / a (n - 1) - 1 / a 0 :=
          reciprocal_prefix_bound_of_strict_half_ratio_count
            (a := a) (γ := γ) hstep (n - 1) hprev_pos
        have hrecip :
            (strictHalfRatioCount a (n - 1) : ℝ) / (2 * (γ : ℝ)) ≤ 1 / a (n - 1) := by
          have hrecip0_nonneg : 0 ≤ 1 / a 0 := one_div_nonneg.mpr (ha_nonneg 0)
          linarith
        have hsub_target :
            a (n - 1) ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) :=
          sublinear_branch_le_target_of_strict_half_ratio_count
            hprev_pos hm hstrict hrecip
        calc
          a n ≤ a (n - 1) := hprefix_mono
          _ ≤ 4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ) := hsub_target
          _ ≤
              max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
                (4 * (γ : ℝ) / ((n - 1 : ℕ) : ℝ)) := le_max_right _ _

-- Proof sketch: apply part (1) at the given index `n`, then force each of the two terms in the
-- maximum to be at most `ε`. The geometric term is controlled by rearranging
-- `((1 / 2)^((n - 1) / 2)) * a 0 ≤ ε` into the logarithmic lower bound on `n`, while the
-- sublinear term is controlled by `4γ / ε ≤ n - 1`.
/-- Lemma 11.7 (2): if `ε > 0` and
`n ≥ max {(2 / log 2) * (log (a 0) + log (1 / ε)), 4γ / ε} + 1`,
then the same recurrence implies `a n ≤ ε`. -/
lemma nonnegative_sequence_le_epsilon_of_quadratic_step_recurrence
    (ε : PosReal)
    {n : ℕ}
    (hn :
      max
          ((2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) +
        1 ≤
        (n : ℝ)) :
    a n ≤ ε := by
  -- First extract the natural-number lower bound needed for part (1).
  have hthreshold_pos : 0 < 4 * (γ : ℝ) / (ε : ℝ) := by
    exact div_pos (mul_pos (by norm_num) (PosReal.coe_pos γ)) (PosReal.coe_pos ε)
  have hone_lt_n : (1 : ℝ) < n := by
    have hmax_pos :
        0 < max
            ((2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))))
            (4 * (γ : ℝ) / (ε : ℝ)) := by
      exact lt_of_lt_of_le hthreshold_pos (le_max_right _ _)
    linarith
  have hn_nat_lt : (1 : ℕ) < n := by
    exact_mod_cast hone_lt_n
  have hn_nat : 2 ≤ n := Nat.succ_le_of_lt hn_nat_lt
  -- Apply the first part and reduce the `max` bound termwise to `ε`.
  have hmain :=
    nonnegative_sequence_le_max_geometric_or_sublinear_of_quadratic_step_recurrence
      (a := a) (γ := γ) ha_nonneg hstep hn_nat
  have hmax_le :
      max
          ((2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))))
          (4 * (γ : ℝ) / (ε : ℝ)) ≤
        (n : ℝ) - 1 := by
    linarith
  have hgeom_threshold :
      (2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))) ≤
        (((n - 1 : ℕ) : ℝ)) := by
    have hgeom_to_sub : (2 / Real.log 2) * (Real.log (a 0) + Real.log (1 / (ε : ℝ))) ≤
        (n : ℝ) - 1 := by
      exact le_trans (le_max_left _ _) hmax_le
    have hcast_sub : (n : ℝ) - 1 = (((n - 1 : ℕ) : ℝ)) := by
      have h1 : 1 ≤ n := by omega
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_sub h1]
    rw [hcast_sub] at hgeom_to_sub
    exact hgeom_to_sub
  have hsub_threshold :
      4 * (γ : ℝ) / (ε : ℝ) ≤ (((n - 1 : ℕ) : ℝ)) := by
    have hsub_to_sub : 4 * (γ : ℝ) / (ε : ℝ) ≤ (n : ℝ) - 1 := by
      exact le_trans (le_max_right _ _) hmax_le
    have hcast_sub : (n : ℝ) - 1 = (((n - 1 : ℕ) : ℝ)) := by
      have h1 : 1 ≤ n := by omega
      rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by norm_num, ← Nat.cast_sub h1]
    rw [hcast_sub] at hsub_to_sub
    exact hsub_to_sub
  have hgeom_le_eps :
      ((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0 ≤ ε := by
    by_cases ha0_zero : a 0 = 0
    · simpa [ha0_zero] using (show (0 : ℝ) ≤ ε by exact (PosReal.coe_pos ε).le)
    · have ha0_pos : 0 < a 0 := lt_of_le_of_ne (ha_nonneg 0) (Ne.symm ha0_zero)
      exact geometric_term_le_epsilon_of_log_bound ha0_pos ε hgeom_threshold
  have hsub_le_eps :
      4 * (γ : ℝ) / (((n - 1 : ℕ) : ℝ)) ≤ ε := by
    have hm_pos : 0 < (((n - 1 : ℕ) : ℝ)) := by
      have hm_nat : 1 ≤ n - 1 := by
        omega
      exact_mod_cast hm_nat
    have hmul :
        4 * (γ : ℝ) ≤ ε * (((n - 1 : ℕ) : ℝ)) := by
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (div_le_iff₀ (PosReal.coe_pos ε)).mp hsub_threshold
    exact (div_le_iff₀ hm_pos).mpr (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hmax_target :
      max (((1 / 2 : ℝ) ^ (((n - 1 : ℕ) : ℝ) / 2)) * a 0)
        (4 * (γ : ℝ) / (((n - 1 : ℕ) : ℝ))) ≤ ε := by
    exact max_le hgeom_le_eps hsub_le_eps
  exact le_trans hmain hmax_target

end
