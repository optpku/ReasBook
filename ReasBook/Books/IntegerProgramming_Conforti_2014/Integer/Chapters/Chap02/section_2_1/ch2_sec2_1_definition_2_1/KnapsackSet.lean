module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic

open scoped BigOperators

public section

/-- The integer knapsack set `{x ∈ ℤ^n | x ≥ 0 ∧ ∑ i, a i * x i ≤ b}` for
the entry `remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_1/ch2_sec2_1_definition_2_1/KnapsackSet.lean`. -/
def knapsackSet
    {n : ℕ}
    (a : Fin n → ℝ)
    (b : ℝ) : Set (Fin n → ℤ) :=
  {x | (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, a i * (x i : ℝ) ≤ b}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_1/ch2_sec2_1_definition_2_1/KnapsackSet.lean:
A vector `x` belongs to `knapsackSet a b`
exactly when it is coordinatewise nonnegative and satisfies the weighted-sum capacity inequality. -/
theorem mem_knapsackSet_iff
    {n : ℕ}
    (a : Fin n → ℝ)
    (b : ℝ)
    (x : Fin n → ℤ) :
    x ∈ knapsackSet a b ↔
      (∀ i : Fin n, 0 ≤ x i) ∧ ∑ i : Fin n, a i * (x i : ℝ) ≤ b := by
  -- Unfolding the defining set makes membership exactly the displayed predicate.
  rfl
