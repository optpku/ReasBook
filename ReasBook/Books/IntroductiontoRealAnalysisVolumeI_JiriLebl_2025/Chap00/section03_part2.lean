/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open scoped BigOperators

section Chap00
section Section03

universe u v w
variable {α : Type u} {β : Type v} {γ : Type w}

/-- Theorem 0.3.6 (principle of induction). Let `P : ℕ → Prop`. If (i) the basis
statement `P 1` holds and (ii) the induction step says `P n → P (n + 1)` for each `n`,
then `P (n + 1)` holds for every natural number `n`. -/
theorem principle_of_induction (P : ℕ → Prop) (h₁ : P 1)
    (hstep : ∀ n, P n → P (n + 1)) : ∀ n : ℕ, P (n + 1) := by
  intro n
  induction n with
  | zero =>
      simpa using h₁
  | succ n ih =>
      simpa [Nat.add_assoc] using hstep (n + 1) ih

/-- Example 0.3.7: For all natural numbers `n`, the inequality `2^(n - 1) ≤ n!` holds,
proved by induction on `n`. -/
-- A convenient inductive form: `2^n ≤ (n+1)!`.
lemma pow_two_le_factorial_succ : ∀ n : ℕ, 2 ^ n ≤ Nat.factorial (n + 1) := by
  intro n
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have h2 : 2 ≤ n + 2 := by
        exact Nat.succ_le_succ (Nat.succ_le_succ (Nat.zero_le n))
      calc
        2 ^ (n + 1) = 2 ^ n * 2 := by
          simp [pow_succ]
        _ ≤ Nat.factorial (n + 1) * (n + 2) := by
          exact Nat.mul_le_mul ih h2
        _ = Nat.factorial (n + 2) := by
          simp [Nat.factorial_succ, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]

theorem pow_two_pred_le_factorial : ∀ n : ℕ, 2 ^ (n - 1) ≤ Nat.factorial n := by
  intro n
  cases n with
  | zero =>
      simp
  | succ n =>
      simpa [Nat.succ_sub_one] using pow_two_le_factorial_succ n

/-- Example 0.3.8: For any real `c ≠ 1` and any natural number `n`, the finite geometric
sum satisfies `1 + c + c^2 + ⋯ + c^n = (1 - c^(n+1)) / (1 - c)`. -/
-- Helper lemma: flip signs in the standard geometric sum closed form.
lemma rewrite_neg_ratio (c : ℝ) (m : ℕ) :
    (c ^ m - 1) / (c - 1) = (1 - c ^ m) / (1 - c) := by
  by_cases hc : c = 1
  · subst hc
    simp
  · have h1 : c - 1 ≠ 0 := sub_ne_zero.mpr hc
    have h2 : 1 - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    field_simp [h1, h2]
    ring

theorem geometric_sum_closed_form {c : ℝ} (hc : c ≠ 1) (n : ℕ) :
    (Finset.sum (Finset.range (n + 1)) fun i => c ^ i) = (1 - c ^ (n + 1)) / (1 - c) := by
  calc
    (Finset.sum (Finset.range (n + 1)) fun i => c ^ i)
        = (c ^ (n + 1) - 1) / (c - 1) := by
            simpa using (geom_sum_eq (x := c) hc (n + 1))
    _ = (1 - c ^ (n + 1)) / (1 - c) := by
            simpa using rewrite_neg_ratio c (n + 1)

/-- Theorem 0.3.9 (principle of strong induction). Let `P : ℕ → Prop`. (i) The basis
statem/ent `P 1` is true. (ii) If `P k` holds for all `k = 1, 2, …, n`, then `P (n + 1)`
is true. Then `P n` holds for all natural numbers `n`. -/
theorem principle_of_strong_induction (P : ℕ → Prop) (h₁ : P 1)
    (hstep : ∀ n, (∀ k, 1 ≤ k → k ≤ n → P k) → P (n + 1)) :
    ∀ n : ℕ, P (n + 1) := by
  -- Auxiliary: build the strong induction hypothesis up to `n + 1`.
  have haux : ∀ n, (∀ k, 1 ≤ k → k ≤ n + 1 → P k) := by
    intro n
    induction n with
    | zero =>
        intro k hk1 hk_le
        have hk : k = 1 := by
          exact Nat.le_antisymm hk_le hk1
        simpa [hk] using h₁
    | succ n ih =>
        intro k hk1 hk_le
        have hlt_or_eq : k < n + 2 ∨ k = n + 2 := Nat.lt_or_eq_of_le hk_le
        cases hlt_or_eq with
        | inl hlt =>
            have hk_le' : k ≤ n + 1 := by
              omega
            exact ih k hk1 hk_le'
        | inr hk_eq =>
            have hnext : P (n + 2) := by
              exact hstep (n + 1) ih
            simpa [hk_eq] using hnext
  intro n
  have h' := haux n
  exact h' (n + 1) (Nat.succ_le_succ (Nat.zero_le n)) (Nat.le_refl _)

end Section03
end Chap00
