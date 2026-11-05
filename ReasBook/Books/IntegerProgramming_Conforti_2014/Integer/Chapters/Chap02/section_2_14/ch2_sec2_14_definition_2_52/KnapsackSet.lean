/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_2.ch2_sec2_2_definition_2_4.KnapsackSet

public section

namespace Knapsack252

/-- The coefficient vector `(90, 35, 26, 25)` from the exercise knapsack constraint. -/
def weights : Fin 4 → ℝ
  | ⟨0, _⟩ => 90
  | ⟨1, _⟩ => 35
  | ⟨2, _⟩ => 26
  | ⟨3, _⟩ => 25

/-- The knapsack capacity `138` from the exercise. -/
def capacity : ℝ := 138

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap02/section_2_14/ch2_sec2_14_definition_2_52/KnapsackSet.lean
Definition 2.52: the exercise `0`--`1` knapsack set
`{x ∈ {0,1}^4 | 90 * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138}`. -/
def set : Set (Fin 4 → ℝ) :=
  zero_one_knapsack_set weights capacity

/-- Unfolding equation for the concrete coefficient vector in Definition 2.52. -/
theorem weights_def :
    weights =
      fun i : Fin 4 ↦
        match i with
        | ⟨0, _⟩ => 90
        | ⟨1, _⟩ => 35
        | ⟨2, _⟩ => 26
        | ⟨3, _⟩ => 25 := by
  -- This is exactly the defining pattern match for `weights`.
  rfl

/-- Unfolding equation for the concrete capacity in Definition 2.52. -/
theorem capacity_eq : capacity = 138 := by
  -- The concrete capacity is definitionally `138`.
  rfl

/-- Membership in `Knapsack252.set` is exactly the binary coordinate condition together with the
exercise inequality `90 * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138`. -/
theorem mem_set_iff
    {x : Fin 4 → ℝ} :
    x ∈ set ↔
      (∀ i : Fin 4, x i = 0 ∨ x i = 1) ∧
        ((90 : ℝ) * x 0 + 35 * x 1 + 26 * x 2 + 25 * x 3 ≤ 138) := by
  -- Expand the specialized set to the generic knapsack membership criterion.
  rw [set, mem_zero_one_knapsack_set_iff]
  -- Normalize the finite sum and evaluate the concrete coefficients and capacity.
  simp [weights, capacity, Fin.sum_univ_succ, add_assoc]

end Knapsack252
