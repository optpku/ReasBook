/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1_3.ch5_sec5_1_3_definition_5_1_3_extra_1

open scoped Matrix

-- This exercise is source-facing, but its valid-inequality predicate is reused from the
-- Chapter 5 owner declaration `section_5_1_3/ch5_sec5_1_3_definition_5_1_3_extra_1`.
-- The nonnegative-orthant hypothesis is expressed with the project's canonical set-level owner
-- `Set.Ici (0 : Fin n → ℝ)`.

section Exercise51

variable {n : ℕ}

/-- Exercise 5.1. If `α¹ x ≤ α₀¹` is valid for `S₁ ⊆ ℝ_+^n` and `α² x ≤ α₀²` is valid for
`S₂ ⊆ ℝ_+^n`, then the coordinatewise minimum inequality
`∑ j, min (α¹ j) (α² j) * x j ≤ max α₀¹ α₀²` is valid for `S₁ ∪ S₂`. -/
theorem valid_inequality_union_of_coordinatewise_min
    {S1 S2 : Set (Fin n → ℝ)}
    {α1 α2 : Fin n → ℝ}
    {α0_1 α0_2 : ℝ}
    (hS1_nonneg : S1 ⊆ Set.Ici (0 : Fin n → ℝ))
    (hS2_nonneg : S2 ⊆ Set.Ici (0 : Fin n → ℝ))
    (hvalid1 : is_valid_inequality S1 α1 α0_1)
    (hvalid2 : is_valid_inequality S2 α2 α0_2) :
    is_valid_inequality (S1 ∪ S2) (fun j ↦ min (α1 j) (α2 j)) (max α0_1 α0_2) := by
  rw [is_valid_inequality_iff] at hvalid1 hvalid2 ⊢
  intro x hx
  rcases hx with hx1 | hx2
  · -- On the `S1` branch, the coordinatewise minimum is dominated by `α1`.
    have hx_nonneg : (0 : Fin n → ℝ) ≤ x := by
      simpa [Set.mem_Ici] using hS1_nonneg hx1
    have hmin_le_left : (fun j ↦ min (α1 j) (α2 j)) ≤ α1 := by
      intro j
      exact min_le_left (α1 j) (α2 j)
    -- Monotonicity on the nonnegative orthant transfers validity from `α1` to `min α1 α2`.
    calc
      (fun j ↦ min (α1 j) (α2 j)) ⬝ᵥ x ≤ α1 ⬝ᵥ x :=
        dotProduct_le_dotProduct_of_nonneg_right hmin_le_left hx_nonneg
      _ ≤ α0_1 := hvalid1 hx1
      _ ≤ max α0_1 α0_2 := le_max_left α0_1 α0_2
  · -- The `S2` branch is symmetric, using domination by `α2`.
    have hx_nonneg : (0 : Fin n → ℝ) ≤ x := by
      simpa [Set.mem_Ici] using hS2_nonneg hx2
    have hmin_le_right : (fun j ↦ min (α1 j) (α2 j)) ≤ α2 := by
      intro j
      exact min_le_right (α1 j) (α2 j)
    -- Monotonicity on the nonnegative orthant transfers validity from `α2` to `min α1 α2`.
    calc
      (fun j ↦ min (α1 j) (α2 j)) ⬝ᵥ x ≤ α2 ⬝ᵥ x :=
        dotProduct_le_dotProduct_of_nonneg_right hmin_le_right hx_nonneg
      _ ≤ α0_2 := hvalid2 hx2
      _ ≤ max α0_1 α0_2 := le_max_right α0_1 α0_2

end Exercise51
