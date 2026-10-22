/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

/- Lemma 8.27 is `source-facing`: it records two explicit bounds for ratios of finite sums of the
harmonic sequence and the inverse-square-root sequence that appear in the dynamic stepsize
analysis. The canonical owners here are `Finset.range` and `Finset.Icc` for the finite sums, with
`Real.log` and `Real.sqrt` for the analytic bounds. The four recurring finite sums are exposed
directly as named source-facing quantities so nearby Chapter 8 rate bounds can reuse them without
repeating the raw `Finset.sum` expressions. -/

/-- The prefix harmonic sum `∑_{n=0}^k 1 / (n + 1)` appearing in Lemma 8.27 (1). -/
def harmonicPrefixSum (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun n ↦ 1 / (n + 1 : ℝ)

/-- The prefix inverse-square-root sum `∑_{n=0}^k 1 / √(n + 1)` appearing in Lemma 8.27 (1). -/
def inverseSqrtPrefixSum (k : ℕ) : ℝ :=
  Finset.sum (Finset.range (k + 1)) fun n ↦ 1 / Real.sqrt (n + 1 : ℝ)

/-- The half-tail harmonic sum `∑_{n=⌊k/2⌋}^k 1 / (n + 1)` appearing in Lemma 8.27 (2). -/
def harmonicHalfTailSum (k : ℕ) : ℝ :=
  Finset.sum (Finset.Icc (k / 2) k) fun n ↦ 1 / (n + 1 : ℝ)

/-- The half-tail inverse-square-root sum `∑_{n=⌊k/2⌋}^k 1 / √(n + 1)` appearing in
Lemma 8.27 (2). -/
def inverseSqrtHalfTailSum (k : ℕ) : ℝ :=
  Finset.sum (Finset.Icc (k / 2) k) fun n ↦ 1 / Real.sqrt (n + 1 : ℝ)

@[simp] theorem harmonicPrefixSum_eq_sum (k : ℕ) :
    harmonicPrefixSum k =
      Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / (n + 1 : ℝ)) := rfl

@[simp] theorem inverseSqrtPrefixSum_eq_sum (k : ℕ) :
    inverseSqrtPrefixSum k =
      Finset.sum (Finset.range (k + 1)) (fun n ↦ 1 / Real.sqrt (n + 1 : ℝ)) := rfl

@[simp] theorem harmonicHalfTailSum_eq_sum (k : ℕ) :
    harmonicHalfTailSum k =
      Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / (n + 1 : ℝ)) := rfl

@[simp] theorem inverseSqrtHalfTailSum_eq_sum (k : ℕ) :
    inverseSqrtHalfTailSum k =
      Finset.sum (Finset.Icc (k / 2) k) (fun n ↦ 1 / Real.sqrt (n + 1 : ℝ)) := rfl

/-- Helper for Lemma 8.27: `log 3` is at least `2 / 3`, via the standard lower bound
`1 - x⁻¹ ≤ log x` at `x = 3`. -/
lemma two_thirds_le_log_three : (2 : ℝ) / 3 ≤ Real.log 3 := by
  -- The textbook constant `log 3` is uniformly positive, and this explicit lower bound is enough
  -- for the small-index cases in part (b).
  have hlog_aux := Real.one_sub_inv_le_log_of_pos (show 0 < (3 : ℝ) by norm_num)
  norm_num at hlog_aux
  exact hlog_aux

/-- Helper for Lemma 8.27: the named prefix harmonic sum is bounded by the standard harmonic-number
estimate `1 + log (k + 1)`. -/
lemma harmonicPrefixSum_le_one_add_log (k : ℕ) :
    harmonicPrefixSum k ≤ 1 + Real.log ((k : ℝ) + 1) := by
  -- Rewrite the source-facing owner as the usual harmonic number, then reuse mathlib's bound.
  simpa [harmonicPrefixSum, harmonic] using harmonic_le_one_add_log (k + 1)

/-- Helper for Lemma 8.27: every term in the prefix inverse-sqrt sum is at least the final term, so
the whole sum dominates `√(k + 1)`. -/
lemma sqrt_le_inverseSqrtPrefixSum (k : ℕ) :
    Real.sqrt ((k : ℝ) + 1) ≤ inverseSqrtPrefixSum k := by
  have hterm :
      ∀ n ∈ Finset.range (k + 1),
        1 / Real.sqrt ((k : ℝ) + 1) ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
    intro n hn
    have hn_le : (n : ℝ) + 1 ≤ (k : ℝ) + 1 := by
      exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hn)
    have hsqrt_le : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 1) := by
      exact Real.sqrt_le_sqrt hn_le
    exact one_div_le_one_div_of_le (by positivity) hsqrt_le
  have hsum :
      Finset.sum (Finset.range (k + 1)) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 1)) ≤
        inverseSqrtPrefixSum k := by
    -- Summing the pointwise comparison gives the global denominator lower bound.
    simpa [inverseSqrtPrefixSum] using Finset.sum_le_sum hterm
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    positivity
  calc
    Real.sqrt ((k : ℝ) + 1)
        = ((k + 1 : ℝ) / Real.sqrt ((k : ℝ) + 1)) := by
            have hsq : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := by
              nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) + 1 by positivity)]
            apply (eq_div_iff hsqrt_pos.ne').2
            nlinarith
    _ = Finset.sum (Finset.range (k + 1)) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 1)) := by
      simp [div_eq_mul_inv]
    _ ≤ inverseSqrtPrefixSum k := hsum

/-- Helper for Lemma 8.27: once `k ≥ 4`, the half-tail harmonic sum is controlled by the
integral-comparison bound `log 3`. -/
lemma harmonicHalfTailSum_le_logThree_of_four_le (k : ℕ) (hk : 4 ≤ k) :
    harmonicHalfTailSum k ≤ Real.log 3 := by
  have hab : k / 2 ≤ k + 1 := by omega
  have hkhalf_pos : 0 < (((k / 2 : ℕ) : ℝ)) := by
    have hkhalf_nat : 1 ≤ k / 2 := by omega
    have hkhalf_real : (1 : ℝ) ≤ (((k / 2 : ℕ) : ℝ)) := by
      norm_num
      exact_mod_cast hkhalf_nat
    linarith
  have hanti : AntitoneOn (fun x : ℝ ↦ 1 / x)
      (Set.Icc ((k / 2 : ℕ) : ℝ) (((k + 1 : ℕ) : ℝ))) := by
    -- The comparison runs on a positive interval, so `x ↦ 1 / x` is antitone there.
    simpa [one_div] using
      (inv_antitoneOn_Icc_right (a := ((k / 2 : ℕ) : ℝ)) (b := (((k + 1 : ℕ) : ℝ))) hkhalf_pos)
  have hsum :
      harmonicHalfTailSum k ≤ ∫ x in (((k / 2 : ℕ) : ℝ))..((k + 1 : ℕ) : ℝ), 1 / x := by
    -- Rewrite the textbook sum as an `Ico` sum so the standard antitone comparison applies.
    rw [harmonicHalfTailSum]
    rw [show Finset.Icc (k / 2) k = Finset.Ico (k / 2) (k + 1) by
      ext n
      simp]
    simpa using
      (AntitoneOn.sum_le_integral_Ico (a := k / 2) (b := k + 1) (f := fun x : ℝ ↦ 1 / x)
        hab hanti)
  have hratio_le : (((k + 1 : ℕ) : ℝ) / (((k / 2 : ℕ) : ℝ))) ≤ 3 := by
    have hkhalf_pos' : 0 < (((k / 2 : ℕ) : ℝ)) := hkhalf_pos
    rw [div_le_iff₀ hkhalf_pos']
    norm_num
    exact_mod_cast (show k + 1 ≤ 3 * (k / 2) by omega)
  calc
    harmonicHalfTailSum k
        ≤ ∫ x in (((k / 2 : ℕ) : ℝ))..((k + 1 : ℕ) : ℝ), 1 / x := hsum
    _ = Real.log ((((k + 1 : ℕ) : ℝ) / (((k / 2 : ℕ) : ℝ))) : ℝ) := by
        rw [integral_one_div_of_pos hkhalf_pos]
        positivity
    _ ≤ Real.log 3 := Real.log_le_log (by positivity) hratio_le

/-- Helper for Lemma 8.27: every term in the half-tail inverse-sqrt sum is at least
`1 / √(k + 2)`, and there are enough terms to obtain the textbook lower bound
`√(k + 2) / 4`. -/
lemma sqrt_div_four_le_inverseSqrtHalfTailSum (k : ℕ) :
    Real.sqrt ((k : ℝ) + 2) / 4 ≤ inverseSqrtHalfTailSum k := by
  have hterm :
      ∀ n ∈ Finset.Icc (k / 2) k,
        1 / Real.sqrt ((k : ℝ) + 2) ≤ 1 / Real.sqrt (n + 1 : ℝ) := by
    intro n hn
    have hn_le : (n : ℝ) + 1 ≤ (k : ℝ) + 2 := by
      have hn_nat : n ≤ k := (Finset.mem_Icc.mp hn).2
      have hn_real : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast hn_nat
      linarith
    have hsqrt_le : Real.sqrt (n + 1 : ℝ) ≤ Real.sqrt ((k : ℝ) + 2) := by
      exact Real.sqrt_le_sqrt hn_le
    exact one_div_le_one_div_of_le (by positivity) hsqrt_le
  have hsum :
      Finset.sum (Finset.Icc (k / 2) k) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 2)) ≤
        inverseSqrtHalfTailSum k := by
    -- Summing the constant lower bound over the whole tail gives the desired coarse estimate.
    simpa [inverseSqrtHalfTailSum] using Finset.sum_le_sum hterm
  have hcard_bound :
      Real.sqrt ((k : ℝ) + 2) / 4 ≤
        ((Finset.Icc (k / 2) k).card : ℝ) / Real.sqrt ((k : ℝ) + 2) := by
    have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 2) := by
      positivity
    have hcount :
        ((k : ℝ) + 2) ≤ 4 * ((Finset.Icc (k / 2) k).card : ℝ) := by
      have hcount_nat : k + 2 ≤ 4 * (Finset.Icc (k / 2) k).card := by
        simpa [Nat.card_Icc] using (show k + 2 ≤ 4 * (k + 1 - k / 2) by omega)
      exact_mod_cast hcount_nat
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 4) hsqrt_pos]
    nlinarith [Real.sq_sqrt (show 0 ≤ (k : ℝ) + 2 by positivity), hcount]
  calc
    Real.sqrt ((k : ℝ) + 2) / 4
        ≤ ((Finset.Icc (k / 2) k).card : ℝ) / Real.sqrt ((k : ℝ) + 2) := hcard_bound
    _ = Finset.sum (Finset.Icc (k / 2) k) (fun _ ↦ 1 / Real.sqrt ((k : ℝ) + 2)) := by
        simp [div_eq_mul_inv]
    _ ≤ inverseSqrtHalfTailSum k := hsum

/-- Helper for Lemma 8.27: the half-tail harmonic sum at `k = 1` is the two-term value
`1 + 1 / 2 = 3 / 2`. -/
lemma harmonicHalfTailSum_one : harmonicHalfTailSum 1 = (3 : ℝ) / 2 := by
  -- Expand the concrete `Icc` sum once so the small branch never has to normalize it again.
  rw [harmonicHalfTailSum]
  have hIcc : Finset.Icc (1 / 2) 1 = ({0, 1} : Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num

/-- Helper for Lemma 8.27: the half-tail harmonic sum at `k = 2` is `1 / 2 + 1 / 3 = 5 / 6`. -/
lemma harmonicHalfTailSum_two : harmonicHalfTailSum 2 = (5 : ℝ) / 6 := by
  -- This is the literal closed form of the `k = 2` half-tail.
  rw [harmonicHalfTailSum]
  have hIcc : Finset.Icc (2 / 2) 2 = ({1, 2} : Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num

/-- Helper for Lemma 8.27: the half-tail harmonic sum at `k = 3` is
`1 / 2 + 1 / 3 + 1 / 4 = 13 / 12`. -/
lemma harmonicHalfTailSum_three : harmonicHalfTailSum 3 = (13 : ℝ) / 12 := by
  -- The closed form isolates the last small numerator normalization needed in part (b).
  rw [harmonicHalfTailSum]
  have hIcc : Finset.Icc (3 / 2) 3 = ({1, 2, 3} : Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num

/-- Helper for Lemma 8.27: the `k = 1` half-tail inverse-square-root sum is
`1 + 1 / √2`. -/
lemma inverseSqrtHalfTailSum_one :
    inverseSqrtHalfTailSum 1 = 1 + 1 / Real.sqrt 2 := by
  -- Keep the radical form literal; only the index-set normalization matters here.
  rw [inverseSqrtHalfTailSum]
  have hIcc : Finset.Icc (1 / 2) 1 = ({0, 1} : Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num

/-- Helper for Lemma 8.27: the `k = 2` half-tail inverse-square-root sum is
`1 / √2 + 1 / √3`. -/
lemma inverseSqrtHalfTailSum_two :
    inverseSqrtHalfTailSum 2 = 1 / Real.sqrt 2 + 1 / Real.sqrt 3 := by
  -- This is the exact denominator shape used before passing to a coarse lower bound.
  rw [inverseSqrtHalfTailSum]
  have hIcc : Finset.Icc (2 / 2) 2 = ({1, 2} : Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num

/-- Helper for Lemma 8.27: the `k = 3` half-tail inverse-square-root sum is
`1 / √2 + 1 / √3 + 1 / 2`. -/
lemma inverseSqrtHalfTailSum_three :
    inverseSqrtHalfTailSum 3 = 1 / Real.sqrt 2 + 1 / Real.sqrt 3 + 1 / 2 := by
  -- The final term simplifies because `√4 = 2`.
  rw [inverseSqrtHalfTailSum]
  have hIcc : Finset.Icc (3 / 2) 3 = ({1, 2, 3} : Finset ℕ) := by
    decide
  rw [hIcc]
  norm_num
  simp [add_assoc]

/-- Helper for Lemma 8.27: the `k = 1` half-tail inverse-square-root sum is at least `3 / 2`. -/
lemma one_add_invSqrtTwo_le_inverseSqrtHalfTailSum_one :
    (3 : ℝ) / 2 ≤ inverseSqrtHalfTailSum 1 := by
  -- Rewrite the concrete denominator and lower-bound `1 / √2` by `1 / 2`.
  rw [inverseSqrtHalfTailSum_one]
  have hsqrt_two_le : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  have hhalf_le : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 := by
    simpa using
      (one_div_le_one_div_of_le (show 0 < Real.sqrt (2 : ℝ) by positivity) hsqrt_two_le)
  nlinarith

/-- Helper for Lemma 8.27: the `k = 2` half-tail inverse-square-root sum is at least `1`. -/
lemma one_le_inverseSqrtHalfTailSum_two :
    (1 : ℝ) ≤ inverseSqrtHalfTailSum 2 := by
  -- Rewrite the denominator and bound each reciprocal square root below by `1 / 2`.
  rw [inverseSqrtHalfTailSum_two]
  have hsqrt_two_le : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  have hsqrt_three_le : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by positivity)]
  have hhalf_two : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 := by
    simpa using
      (one_div_le_one_div_of_le (show 0 < Real.sqrt (2 : ℝ) by positivity) hsqrt_two_le)
  have hhalf_three : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 3 := by
    simpa using
      (one_div_le_one_div_of_le (show 0 < Real.sqrt (3 : ℝ) by positivity) hsqrt_three_le)
  nlinarith

/-- Helper for Lemma 8.27: the `k = 3` half-tail inverse-square-root sum is at least `3 / 2`. -/
lemma threeHalves_le_inverseSqrtHalfTailSum_three :
    (3 : ℝ) / 2 ≤ inverseSqrtHalfTailSum 3 := by
  -- Rewrite the denominator and reuse the same `1 / 2` lower bounds on the radical terms.
  rw [inverseSqrtHalfTailSum_three]
  have hsqrt_two_le : Real.sqrt (2 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
  have hsqrt_three_le : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by positivity)]
  have hhalf_two : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 2 := by
    simpa using
      (one_div_le_one_div_of_le (show 0 < Real.sqrt (2 : ℝ) by positivity) hsqrt_two_le)
  have hhalf_three : (1 : ℝ) / 2 ≤ 1 / Real.sqrt 3 := by
    simpa using
      (one_div_le_one_div_of_le (show 0 < Real.sqrt (3 : ℝ) by positivity) hsqrt_three_le)
  nlinarith

-- Proof sketch: bound the numerator by
-- `D + 1 + log (k + 1)` using the integral comparison from Lemma 8.26 for `x ↦ 1 / (x + 1)`,
-- and bound the denominator below by `sqrt (k + 1)` using the same comparison for
-- `x ↦ 1 / sqrt (x + 1)`. Dividing the two estimates gives the displayed ratio bound; at `k = 0`
-- the inequality is an equality.
/-- The prefix estimate in Lemma 8.27: for every nonnegative real `D` and every `k`, the
ratio of the prefix harmonic sum shifted by `D` to the corresponding prefix inverse-square-root
sum is bounded by `(D + 1 + log (k + 1)) / √(k + 1)` as in equation (8.30). -/
lemma harmonic_prefix_ratio_le_log_bound
    (D : ℝ) (hD : 0 ≤ D) (k : ℕ) :
    (D + harmonicPrefixSum k) / inverseSqrtPrefixSum k ≤
      (D + 1 + Real.log ((k : ℝ) + 1)) / Real.sqrt ((k : ℝ) + 1) := by
  -- The numerator is controlled by the harmonic-number estimate, and the denominator is bounded
  -- below by the constant final summand repeated `k + 1` times.
  have hnum :
      D + harmonicPrefixSum k ≤ D + 1 + Real.log ((k : ℝ) + 1) := by
    linarith [harmonicPrefixSum_le_one_add_log k]
  have hnum_nonneg : 0 ≤ D + harmonicPrefixSum k := by
    have hprefix_nonneg :
        0 ≤ Finset.sum (Finset.range (k + 1)) (fun x ↦ 1 / (x + 1 : ℝ)) := by
      positivity
    simpa [harmonicPrefixSum] using add_nonneg hD hprefix_nonneg
  have hden : Real.sqrt ((k : ℝ) + 1) ≤ inverseSqrtPrefixSum k := sqrt_le_inverseSqrtPrefixSum k
  have hsqrt_pos : 0 < Real.sqrt ((k : ℝ) + 1) := by
    positivity
  -- Shrink the denominator to the explicit square-root term, then enlarge the numerator.
  exact
    (div_le_div_iff₀ (lt_of_lt_of_le hsqrt_pos hden) hsqrt_pos).2 <|
      by nlinarith

-- Proof sketch: compare the numerator with the integral of `x ↦ 1 / (x + 1)` over
-- `[⌊k / 2⌋, k]` to get the upper bound `log 3`, then compare the denominator with the integral of
-- `x ↦ 1 / sqrt (x + 1)` over the same range to get the lower bound `sqrt (k + 2) / 4`. The
-- resulting quotient estimate is equation (8.31); the small cases `k = 0` and `k = 1` already
-- satisfy the same bound directly.
/-- Lemma 8.27 (2): for every nonnegative real `D` and every `k`, the ratio of the tail sums
from `⌊k / 2⌋` to `k` is bounded by `4 (D + log 3) / √(k + 2)` as in equation (8.31). -/
lemma harmonic_half_tail_ratio_le_log_three_bound
    (D : ℝ) (hD : 0 ≤ D) (k : ℕ) :
    (D + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k ≤
      (4 * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2) := by
  by_cases hk : k ≤ 3
  · interval_cases k
    · -- At `k = 0`, the tail has one term, so a coarse lower bound on `log 3` is enough.
      have hsmall : (1 : ℝ) ≤ 2 * Real.log 3 := by
        linarith [two_thirds_le_log_three]
      have hsqrt_two_le : Real.sqrt (2 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (2 : ℝ) by positivity)]
      have hcoeff : (2 : ℝ) ≤ 4 / Real.sqrt (2 : ℝ) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith [hsqrt_two_le]
      have hmain : D + 1 ≤ (4 / Real.sqrt (2 : ℝ)) * (D + Real.log 3) := by
        nlinarith [hD, hsmall, hcoeff]
      simpa [harmonicHalfTailSum, inverseSqrtHalfTailSum, div_eq_mul_inv, mul_assoc, mul_left_comm,
        mul_comm] using hmain
    · -- At `k = 1`, the denominator already exceeds `1`, and the coefficient `4 / √3` is large.
      -- Route correction: use the named `k = 1` closed forms and the coarse denominator lower
      -- bound, rather than re-expanding the `Finset.Icc` sum inside the branch.
      rw [harmonicHalfTailSum_one]
      have hDlog_nonneg : 0 ≤ D + Real.log 3 := by
        nlinarith [hD, two_thirds_le_log_three]
      have hnum_nonneg : 0 ≤ D + (3 : ℝ) / 2 := by
        nlinarith [hD]
      have hratio :
          (D + (3 : ℝ) / 2) / inverseSqrtHalfTailSum 1 ≤ (D + (3 : ℝ) / 2) / ((3 : ℝ) / 2) := by
        have hthree_halves_pos : 0 < (3 : ℝ) / 2 := by
          norm_num
        exact
          div_le_div_of_nonneg_left hnum_nonneg hthree_halves_pos
            one_add_invSqrtTwo_le_inverseSqrtHalfTailSum_one
      have hsqrt_three_le : Real.sqrt (3 : ℝ) ≤ 2 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (3 : ℝ) by positivity)]
      have hcoeff : (2 : ℝ) ≤ 4 / Real.sqrt (3 : ℝ) := by
        rw [le_div_iff₀ (show 0 < Real.sqrt (3 : ℝ) by positivity)]
        nlinarith [hsqrt_three_le]
      have hmain :
          (D + (3 : ℝ) / 2) / ((3 : ℝ) / 2) ≤
            (4 * (D + Real.log 3)) / Real.sqrt ((1 : ℝ) + 2) := by
        have hstep : (D + (3 : ℝ) / 2) / ((3 : ℝ) / 2) ≤ (2 : ℝ) * (D + Real.log 3) := by
          nlinarith [hD, two_thirds_le_log_three]
        have hcoeff' : (2 : ℝ) ≤ 4 / Real.sqrt ((1 : ℝ) + 2) := by
          rw [show ((1 : ℝ) + 2) = 3 by norm_num]
          exact hcoeff
        have hscale :
            (2 : ℝ) * (D + Real.log 3) ≤
              (4 / Real.sqrt ((1 : ℝ) + 2)) * (D + Real.log 3) := by
          nlinarith [hcoeff', hDlog_nonneg]
        calc
          (D + (3 : ℝ) / 2) / ((3 : ℝ) / 2) ≤ (2 : ℝ) * (D + Real.log 3) := hstep
          _ ≤ (4 / Real.sqrt ((1 : ℝ) + 2)) * (D + Real.log 3) := hscale
          _ = (4 * (D + Real.log 3)) / Real.sqrt ((1 : ℝ) + 2) := by
              ring
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio.trans hmain
    · -- At `k = 2`, the right-hand coefficient is exactly `2`, so `2 / 3 ≤ log 3` suffices.
      -- Route correction: reduce to the `k = 2` closed numerator and the denominator lower bound
      -- `1 ≤ inverseSqrtHalfTailSum 2`, then compare directly with `2 * (D + log 3)`.
      rw [harmonicHalfTailSum_two]
      have hnum_nonneg : 0 ≤ D + (5 : ℝ) / 6 := by
        nlinarith [hD]
      have hratio :
          (D + (5 : ℝ) / 6) / inverseSqrtHalfTailSum 2 ≤ D + (5 : ℝ) / 6 := by
        simpa using
          div_le_div_of_nonneg_left hnum_nonneg (show (0 : ℝ) < 1 by norm_num)
            one_le_inverseSqrtHalfTailSum_two
      have hmain :
          D + (5 : ℝ) / 6 ≤ (4 * (D + Real.log 3)) / Real.sqrt ((2 : ℝ) + 2) := by
        have hstep : D + (5 : ℝ) / 6 ≤ 2 * (D + Real.log 3) := by
          nlinarith [hD, two_thirds_le_log_three]
        have hrhs :
            2 * (D + Real.log 3) = (4 * (D + Real.log 3)) / Real.sqrt ((2 : ℝ) + 2) := by
          rw [show Real.sqrt ((2 : ℝ) + 2) = 2 by norm_num]
          ring
        calc
          D + (5 : ℝ) / 6 ≤ 2 * (D + Real.log 3) := hstep
          _ = (4 * (D + Real.log 3)) / Real.sqrt ((2 : ℝ) + 2) := hrhs
      simpa using hratio.trans hmain
    · -- At `k = 3`, the denominator still exceeds `1`, while the right-hand coefficient is
      -- already strong enough once combined with `2 / 3 ≤ log 3`.
      -- Route correction: use the named `k = 3` formulas and replace the denominator by the
      -- coarse bound `3 / 2` before comparing coefficients.
      rw [harmonicHalfTailSum_three]
      have hDlog_nonneg : 0 ≤ D + Real.log 3 := by
        nlinarith [hD, two_thirds_le_log_three]
      have hnum_nonneg : 0 ≤ D + (13 : ℝ) / 12 := by
        nlinarith [hD]
      have hratio :
          (D + (13 : ℝ) / 12) / inverseSqrtHalfTailSum 3 ≤ (D + (13 : ℝ) / 12) / ((3 : ℝ) / 2) := by
        have hthree_halves_pos : 0 < (3 : ℝ) / 2 := by
          norm_num
        exact
          div_le_div_of_nonneg_left hnum_nonneg hthree_halves_pos
            threeHalves_le_inverseSqrtHalfTailSum_three
      have hsqrt_five_le : Real.sqrt (5 : ℝ) ≤ 3 := by
        nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]
      have hcoeff : (4 : ℝ) / 3 ≤ 4 / Real.sqrt (5 : ℝ) := by
        rw [div_le_div_iff₀ (show 0 < (3 : ℝ) by norm_num)
          (show 0 < Real.sqrt (5 : ℝ) by positivity)]
        nlinarith [hsqrt_five_le]
      have hmain :
          (D + (13 : ℝ) / 12) / ((3 : ℝ) / 2) ≤
            (4 * (D + Real.log 3)) / Real.sqrt ((3 : ℝ) + 2) := by
        have hstep :
            (D + (13 : ℝ) / 12) / ((3 : ℝ) / 2) ≤ ((4 : ℝ) / 3) * (D + Real.log 3) := by
          nlinarith [hD, two_thirds_le_log_three]
        have hcoeff' : (4 : ℝ) / 3 ≤ 4 / Real.sqrt ((3 : ℝ) + 2) := by
          rw [show ((3 : ℝ) + 2) = 5 by norm_num]
          exact hcoeff
        have hscale :
            ((4 : ℝ) / 3) * (D + Real.log 3) ≤
              (4 / Real.sqrt ((3 : ℝ) + 2)) * (D + Real.log 3) := by
          nlinarith [hcoeff', hDlog_nonneg]
        calc
          (D + (13 : ℝ) / 12) / ((3 : ℝ) / 2) ≤ ((4 : ℝ) / 3) * (D + Real.log 3) := hstep
          _ ≤ (4 / Real.sqrt ((3 : ℝ) + 2)) * (D + Real.log 3) := hscale
          _ = (4 * (D + Real.log 3)) / Real.sqrt ((3 : ℝ) + 2) := by
              ring
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio.trans hmain
  · have hk4 : 4 ≤ k := by omega
    have hnum :
        D + harmonicHalfTailSum k ≤ D + Real.log 3 := by
      linarith [harmonicHalfTailSum_le_logThree_of_four_le k hk4]
    have hnum_nonneg : 0 ≤ D + harmonicHalfTailSum k := by
      have hhalf_nonneg :
          0 ≤ Finset.sum (Finset.Icc (k / 2) k) (fun x ↦ 1 / (x + 1 : ℝ)) := by
        positivity
      simpa [harmonicHalfTailSum] using add_nonneg hD hhalf_nonneg
    have hden : Real.sqrt ((k : ℝ) + 2) / 4 ≤ inverseSqrtHalfTailSum k :=
      sqrt_div_four_le_inverseSqrtHalfTailSum k
    have hden_pos : 0 < Real.sqrt ((k : ℝ) + 2) / 4 := by
      positivity
    have hratio :
        (D + harmonicHalfTailSum k) / inverseSqrtHalfTailSum k ≤
          (D + Real.log 3) / (Real.sqrt ((k : ℝ) + 2) / 4) := by
      exact (div_le_div_iff₀ (lt_of_lt_of_le hden_pos hden) hden_pos).2 <| by
        nlinarith
    have hrewrite :
        (D + Real.log 3) / (Real.sqrt ((k : ℝ) + 2) / 4) =
          (4 * (D + Real.log 3)) / Real.sqrt ((k : ℝ) + 2) := by
      field_simp [show Real.sqrt ((k : ℝ) + 2) ≠ 0 by positivity]
    simpa [hrewrite] using hratio

end
