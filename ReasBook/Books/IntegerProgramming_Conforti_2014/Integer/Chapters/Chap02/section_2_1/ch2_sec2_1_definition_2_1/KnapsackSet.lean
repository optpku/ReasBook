/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

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
