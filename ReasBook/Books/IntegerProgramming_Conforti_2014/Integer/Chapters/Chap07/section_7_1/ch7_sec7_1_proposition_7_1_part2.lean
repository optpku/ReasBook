/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_example_3_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_2
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_definition_3_18_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_1.ch7_sec7_1_knapsack_cover

open scoped BigOperators

-- The real-weight knapsack polytope, equality-face owner, and facet predicate are reused from
-- Chapter 3, so this file keeps only the lifted-cover-specific source-facing data.

section CoverLifting

variable {n : ℕ}

/-- The coefficient vector of the lifted cover inequality determined by the cover `C` and the
lifting coefficients `α` on `N \ C`. -/
def lifted_cover_inequality_coeff
    (C : Finset (Fin n)) (α : Fin n → ℝ) : Fin n → ℝ :=
  fun j ↦ if j ∈ C then 1 else α j

/-- Evaluating `lifted_cover_inequality_coeff C α` recovers the usual piecewise formula with
coefficient `1` on `C` and coefficient `α j` off `C`. -/
theorem lifted_cover_inequality_coeff_apply
    (C : Finset (Fin n)) (α : Fin n → ℝ) (j : Fin n) :
    lifted_cover_inequality_coeff C α j = if j ∈ C then 1 else α j := by
  rfl

/-- On the cover `C`, the lifted cover coefficient equals `1`. -/
@[simp] theorem lifted_cover_inequality_coeff_of_mem
    {C : Finset (Fin n)} {α : Fin n → ℝ} {j : Fin n} (hj : j ∈ C) :
    lifted_cover_inequality_coeff C α j = 1 := by
  simp [lifted_cover_inequality_coeff, hj]

/-- Off the cover `C`, the lifted cover coefficient equals the lifting coefficient `α j`. -/
@[simp] theorem lifted_cover_inequality_coeff_of_not_mem
    {C : Finset (Fin n)} {α : Fin n → ℝ} {j : Fin n} (hj : j ∉ C) :
    lifted_cover_inequality_coeff C α j = α j := by
  simp [lifted_cover_inequality_coeff, hj]

/-- The face of the `0,1` knapsack polytope cut out by the lifted cover inequality determined by
the cover `C` and the lifting coefficients `α` on the complement of `C`. -/
def lifted_cover_face
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) (α : Fin n → ℝ) :
    Set (Fin n → ℝ) :=
  face_set
    (zero_one_knapsack_polytope a b)
    (lifted_cover_inequality_coeff C α)
    (cover_inequality_rhs C)

/-- Helper for Proposition 7.1: dotting the lifted cover coefficient vector with `x` recovers the
source split into the cover contribution and the lifted complement contribution. -/
theorem lifted_cover_inequality_coeff_dotProduct
    (C : Finset (Fin n)) (α x : Fin n → ℝ) :
    lifted_cover_inequality_coeff C α ⬝ᵥ x =
      Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ α j * x j) := by
  classical
  -- Expand the dot product into the universal sum of coordinate contributions.
  rw [dotProduct]
  calc
    ∑ j, lifted_cover_inequality_coeff C α j * x j
      = ∑ j, if j ∈ C then x j else α j * x j := by
          -- Rewrite each summand using the piecewise description of the coefficient vector.
          apply Finset.sum_congr rfl
          intro j hj
          by_cases hjC : j ∈ C
          · simp [lifted_cover_inequality_coeff, hjC]
          · simp [lifted_cover_inequality_coeff, hjC]
    _ =
        Finset.sum (Finset.univ.filter (fun j ↦ j ∈ C))
            (fun j ↦ if j ∈ C then x j else α j * x j) +
          Finset.sum (Finset.univ.filter (fun j ↦ ¬ j ∈ C))
            (fun j ↦ if j ∈ C then x j else α j * x j) := by
            -- Split the universal sum into the coordinates inside and outside the cover.
            symm
            exact
              Finset.sum_filter_add_sum_filter_not Finset.univ
                (fun j ↦ j ∈ C)
                (fun j ↦ if j ∈ C then x j else α j * x j)
    _ =
        Finset.sum C (fun j ↦ if j ∈ C then x j else α j * x j) +
          Finset.sum (Finset.univ \ C) (fun j ↦ if j ∈ C then x j else α j * x j) := by
            -- Rewrite the filtered pieces as the cover sum and the complementary sum.
            simp [Finset.sdiff_eq_filter]
    _ = Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ α j * x j) := by
          -- Evaluate the piecewise summands on each side of the partition.
          congr 1
          · apply Finset.sum_congr rfl
            intro j hj
            simp [hj]
          · apply Finset.sum_congr rfl
            intro j hj
            simp at hj
            simp [hj]

/-- Proposition 7.1. Membership in `lifted_cover_face a b C α` means satisfying the
knapsack-polytope constraints and meeting the lifted cover inequality at equality with
right-hand side `|C| - 1`. -/
theorem mem_lifted_cover_face_iff
    {a : Fin n → ℝ} {b : ℝ} {C : Finset (Fin n)} {α x : Fin n → ℝ} :
    x ∈ lifted_cover_face a b C α ↔
      x ∈ zero_one_knapsack_polytope a b ∧
        Finset.sum C x + Finset.sum (Finset.univ \ C) (fun j ↦ α j * x j) =
          cover_inequality_rhs C := by
  -- Unfold the equality face to separate polytope membership from the defining hyperplane.
  rw [lifted_cover_face, mem_face_set_iff]
  -- Rewrite the hyperplane equation into the source-facing lifted cover formula.
  rw [lifted_cover_inequality_coeff_dotProduct]

/-- Motivated by Proposition 7.1, this is the set of coefficient vectors `α` on `N \ C` for
which the lifted cover inequality
`∑ j in C, x j + ∑ j in Finset.univ \ C, α j * x j ≤ |C| - 1` cuts out a facet of `conv(K)`. -/
def facet_defining_liftings_of_cover_inequality
    (a : Fin n → ℝ) (b : ℝ) (C : Finset (Fin n)) :
    Set (Fin n → ℝ) :=
  {α : Fin n → ℝ |
    IsFacetOf (zero_one_knapsack_polytope a b) (lifted_cover_face a b C α)}

/-- A coefficient vector belongs to `facet_defining_liftings_of_cover_inequality a b C` exactly
when the corresponding lifted cover face is a facet of the `0,1` knapsack polytope. -/
theorem mem_facet_defining_liftings_of_cover_inequality_iff
    {a : Fin n → ℝ} {b : ℝ} {C : Finset (Fin n)} {α : Fin n → ℝ} :
    α ∈ facet_defining_liftings_of_cover_inequality a b C ↔
      IsFacetOf (zero_one_knapsack_polytope a b) (lifted_cover_face a b C α) :=
  Iff.rfl

end CoverLifting
