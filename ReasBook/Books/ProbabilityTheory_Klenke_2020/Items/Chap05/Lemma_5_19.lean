/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open Finset

/-- Helper for Lemma 5.19: the shifted inverse-square summand is nonnegative. -/
private lemma shifted_inv_sq_nonneg (k n : ℕ) :
    0 ≤ (((n + (k + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
  positivity

/-- Helper for Lemma 5.19: reindexing the shifted finite tail produces the interval
sum needed for the canonical inverse-square estimate. -/
private lemma sum_range_shifted_inv_sq_eq_sum_Ioo_inv_sq (k n : ℕ) :
    (∑ i ∈ range n, (((i + (k + 1) : ℕ) : ℝ) ^ 2)⁻¹) =
      ∑ i ∈ Ioo k (k + n + 1), (((i : ℝ) ^ 2)⁻¹) := by
  -- Rewrite the shifted range as an interval translated by `k + 1`.
  rw [Finset.range_eq_Ico]
  rw [Finset.sum_Ico_add' (fun i : ℕ ↦ (((i : ℝ) ^ 2)⁻¹)) 0 n (k + 1)]
  rw [Nat.zero_add, Nat.add_assoc]
  -- The translated interval is exactly `Ioo k (k + n + 1)`.
  congr 1
  ext i
  simp only [mem_Ico, mem_Ioo]
  omega

/-- Helper for Lemma 5.19: the shifted inverse-square tail is bounded by
`2 / (k + 1)`. -/
private lemma tsum_shifted_inv_sq_le_two_div (k : ℕ) :
    (∑' n : ℕ, (((n + (k + 1) : ℕ) : ℝ) ^ 2)⁻¹) ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
  -- Compare every partial sum with the standard interval estimate from mathlib.
  refine Real.tsum_le_of_sum_range_le (shifted_inv_sq_nonneg k) ?_
  intro n
  calc
    ∑ i ∈ range n, (((i + (k + 1) : ℕ) : ℝ) ^ 2)⁻¹
      = ∑ i ∈ Ioo k (k + n + 1), (((i : ℝ) ^ 2)⁻¹) :=
        sum_range_shifted_inv_sq_eq_sum_Ioo_inv_sq k n
    _ ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
      simpa using (sum_Ioo_inv_sq_le k (k + n + 1) : _)

/-- Helper for Lemma 5.19: after shifting the tail to start at `⌊x⌋₊ + 1`, the
factor `2x` is still controlled by `4`. -/
private lemma two_mul_tsum_nat_add_floor_add_one_inv_sq_le_four (x : ℝ) :
    2 * x * (∑' n : ℕ, (((n + (⌊x⌋₊ + 1) : ℕ) : ℝ) ^ 2)⁻¹) ≤ 4 := by
  let k : ℕ := ⌊x⌋₊
  let tail : ℝ := ∑' n : ℕ, (((n + (k + 1) : ℕ) : ℝ) ^ 2)⁻¹
  -- First apply the canonical tail estimate with the shifted starting index.
  have htail : tail ≤ 2 / ((k + 1 : ℕ) : ℝ) := by
    simpa [tail] using tsum_shifted_inv_sq_le_two_div k
  have hk_pos : 0 < ((k + 1 : ℕ) : ℝ) := by
    positivity
  -- The floor inequality gives `x ≤ k + 1`.
  have hxk : x ≤ ((k + 1 : ℕ) : ℝ) := by
    simpa [k] using (Nat.lt_floor_add_one x).le
  have htail_nonneg : 0 ≤ tail := by
    exact tsum_nonneg (shifted_inv_sq_nonneg k)
  have hmul : tail * ((k + 1 : ℕ) : ℝ) ≤ 2 := by
    exact (le_div_iff₀ hk_pos).mp htail
  -- Monotonicity transfers the bound from `k + 1` down to `x`.
  have hxtail : x * tail ≤ 2 := by
    calc
      x * tail ≤ ((k + 1 : ℕ) : ℝ) * tail := by gcongr
      _ = tail * ((k + 1 : ℕ) : ℝ) := by ring
      _ ≤ 2 := hmul
  have htwo : 2 * x * tail ≤ 4 := by
    nlinarith
  simpa [k, tail, mul_assoc, mul_left_comm, mul_comm] using htwo

/-- Helper for Lemma 5.19: the subtype-indexed tail above `x` coincides with the
shifted natural-number tail starting at `⌊x⌋₊ + 1`. -/
private lemma nat_tail_subtype_tsum_eq_shifted_floor_tail {x : ℝ} (hx : 0 ≤ x) :
    (∑' n : {n : ℕ // x < (n : ℝ)}, ((n : ℝ) ^ 2)⁻¹) =
      ∑' n : ℕ, (((n + (⌊x⌋₊ + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
  let k : ℕ := ⌊x⌋₊
  have hset :
      {n : ℕ | x < (n : ℝ)} = {n : ℕ | n ∉ range (k + 1)} := by
    ext n
    simpa [k, Finset.mem_range, Nat.not_lt] using (Nat.floor_lt hx).symm
  let e : {n : ℕ // x < (n : ℝ)} ≃ {n : ℕ // n ∉ range (k + 1)} := Equiv.setCongr hset
  -- First replace the tail condition by the complement of `range (k + 1)`.
  calc
    (∑' n : {n : ℕ // x < (n : ℝ)}, ((n : ℝ) ^ 2)⁻¹) =
        ∑' n : {n : ℕ // n ∉ range (k + 1)}, ((n : ℝ) ^ 2)⁻¹ := by
          simpa using
            e.tsum_eq (fun n : {n : ℕ // n ∉ range (k + 1)} ↦ ((n : ℝ) ^ 2)⁻¹)
    -- Then use `notMemRangeEquiv` to identify that complement with a shifted copy of `ℕ`.
    _ = ∑' n : ℕ, ((((notMemRangeEquiv (k + 1)).symm n : ℕ) : ℝ) ^ 2)⁻¹ := by
          simpa using
            ((notMemRangeEquiv (k + 1)).symm.tsum_eq
              (fun n : {n : ℕ // n ∉ range (k + 1)} ↦ ((n : ℝ) ^ 2)⁻¹)).symm
    -- Finally, `notMemRangeEquiv` shifts the index by exactly `k + 1`.
    _ = ∑' n : ℕ, (((n + (k + 1) : ℕ) : ℝ) ^ 2)⁻¹ := by
          simp

-- Proof sketch: rewrite the tail `∑_{n > x} n⁻²` as the shifted inverse-square series starting at
-- `⌊x⌋₊ + 1`, apply the canonical shifted-tail estimate above, and use the equivalence
-- `x < n ↔ ⌊x⌋₊ < n` for `x ≥ 0`.
/-- Lemma 5.19: for every nonnegative real `x`, the inverse-square tail above `x` satisfies
`2x * ∑_{n > x} n⁻² ≤ 4`. -/
theorem two_mul_tsum_nat_tail_inv_sq_le_four {x : ℝ} (hx : 0 ≤ x) :
    2 * x * (∑' n : {n : ℕ // x < (n : ℝ)}, ((n : ℝ) ^ 2)⁻¹) ≤ 4 := by
  -- Rewrite the subtype-indexed tail as the shifted series starting at `⌊x⌋₊ + 1`.
  rw [nat_tail_subtype_tsum_eq_shifted_floor_tail hx]
  -- The remaining estimate is exactly the shifted-tail bound proved above.
  exact two_mul_tsum_nat_add_floor_add_one_inv_sq_le_four x
