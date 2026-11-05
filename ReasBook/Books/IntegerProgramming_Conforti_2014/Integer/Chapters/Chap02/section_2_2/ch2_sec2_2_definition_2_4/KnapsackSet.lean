/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Real.Basic

public section

open scoped BigOperators

universe u

section KnapsackSet

variable {ι : Type u} [Fintype ι]

/-- The `0`--`1` knapsack set `{x ∈ {0,1}^n | ∑ i, a i * x i ≤ b}`. -/
def zero_one_knapsack_set (a : ι → ℝ) (b : ℝ) : Set (ι → ℝ) :=
  {x | (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, a i * x i ≤ b}

/-- A point belongs to `zero_one_knapsack_set a b` exactly when it is binary and satisfies the
knapsack inequality. -/
theorem mem_zero_one_knapsack_set_iff
    (a : ι → ℝ) (b : ℝ) (x : ι → ℝ) :
    x ∈ zero_one_knapsack_set a b ↔
      (∀ i, x i = 0 ∨ x i = 1) ∧ ∑ i, a i * x i ≤ b := by
  -- Unfold membership in the defining set comprehension.
  rfl

end KnapsackSet
