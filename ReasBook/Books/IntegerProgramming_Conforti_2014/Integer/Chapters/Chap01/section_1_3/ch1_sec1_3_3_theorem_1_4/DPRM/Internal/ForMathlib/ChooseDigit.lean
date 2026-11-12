/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/

module

public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Binomial coefficients are base-`u` digits

The coefficient-extraction identity underlying #33: for a base large enough to hold every
coefficient, the binomial coefficients of `n` are literally the base-`u` digits of
`(u + 1) ^ n`.

```lean
n.choose k = ((2 ^ (n + 1) + 1) ^ n / (2 ^ (n + 1)) ^ k) % 2 ^ (n + 1)
```

Unconditional: for `k > n` the digit and the coefficient are both zero.

## Route

Mathlib's digits API does nearly all of it. The little-endian list `[n.choose 0, …, n.choose n]`
has base-`u` value `(u + 1) ^ n` by the binomial theorem; every entry is below `u` because
`n.choose k ≤ 2 ^ n < 2 ^ (n + 1)`; its last entry is `n.choose n = 1`, so `Nat.digits_ofDigits`
recovers the list on the nose; and `Nat.getD_digits` turns a list lookup into division and
modulus.

So no bespoke coefficient extraction is needed — the obstacle was already in mathlib.
-/

@[expose] public section

namespace Nat

/-- The base-`u` value of a list of the form `(range m).map f`. -/
theorem ofDigits_range_map (u : ℕ) :
    ∀ (m : ℕ) (f : ℕ → ℕ),
      Nat.ofDigits u ((List.range m).map f) = ∑ i ∈ Finset.range m, f i * u ^ i := by
  intro m
  induction m with
  | zero => intro f; simp
  | succ m ih =>
    intro f
    rw [List.range_succ_eq_map, List.map_cons, List.map_map, Nat.ofDigits_cons]
    simp only [Function.comp_def]
    rw [ih (fun i => f (i + 1)), Finset.sum_range_succ' (fun i => f i * u ^ i) m]
    simp only [pow_zero, mul_one, pow_succ, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- The digit list of `(u + 1) ^ n` in base `u`, when `u` is large enough. -/
theorem digits_add_one_pow {u n : ℕ} (hu : 2 ^ n < u) :
    Nat.digits u ((u + 1) ^ n) = (List.range (n + 1)).map (n.choose ·) := by
  have hu1 : 1 < u := lt_of_le_of_lt (Nat.one_le_two_pow) hu
  have hval : Nat.ofDigits u ((List.range (n + 1)).map (n.choose ·)) = (u + 1) ^ n := by
    rw [ofDigits_range_map]
    rw [add_pow u 1 n]
    exact (Finset.sum_congr rfl fun i _ => by push_cast; ring).symm
  rw [← hval]
  refine Nat.digits_ofDigits u hu1 _ (fun l hl => ?_) (fun h => ?_)
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hl
    exact lt_of_le_of_lt (Nat.choose_le_two_pow n i) hu
  · rw [List.getLast_map, List.getLast_range]
    simp

/-- **Binomial coefficients are base-`u` digits.** Unconditional in `k`. -/
theorem choose_eq_baseDigit (n k : ℕ) :
    n.choose k = ((2 ^ (n + 1) + 1) ^ n / (2 ^ (n + 1)) ^ k) % 2 ^ (n + 1) := by
  set u := 2 ^ (n + 1) with hu
  have hun : 2 ^ n < u := by
    rw [hu]
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hu2 : 2 ≤ u := by
    have : (2 : ℕ) ^ 1 ≤ 2 ^ (n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    simpa using this
  have hgetD := Nat.getD_digits ((u + 1) ^ n) k hu2
  rw [digits_add_one_pow hun] at hgetD
  rw [← hgetD]
  -- the list lookup is the coefficient, on both sides of `k ≤ n`
  by_cases hk : k < n + 1
  · rw [List.getD_eq_getElem _ _ (by simpa using hk)]
    simp
  · rw [List.getD_eq_default _ _ (by simpa using Nat.not_lt.mp hk)]
    exact Nat.choose_eq_zero_of_lt (show n < k by omega)

end Nat
