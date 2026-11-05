/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_7.ch3_sec3_7_definition_3_7_extra_1

open scoped Matrix

-- This exercise is stated directly on the Chapter 3 feasible-region owner `polyhedron_le_set`.

/-- A system `A *ᵥ x ≤ b` is contained in a system `C *ᵥ x ≤ d` exactly when each row inequality of
`C *ᵥ x ≤ d` is valid on the feasible region of `A *ᵥ x ≤ b`. -/
theorem linear_inequality_solution_set_subset_iff_rowwise_validity
    {m p n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (d : Fin p → ℝ) :
    polyhedron_le_set A b ⊆ polyhedron_le_set C d ↔
      ∀ i : Fin p, ∀ ⦃x : Fin n → ℝ⦄, x ∈ polyhedron_le_set A b →
        (C *ᵥ x) i ≤ d i := by
  constructor
  · intro hsubset i x hx
    exact (hsubset hx) i
  · intro hrowwise x hx i
    exact hrowwise i hx

/-- Exercise 3.24. Equality of the feasible regions of two systems `A *ᵥ x ≤ b` and
`C *ᵥ x ≤ d` reduces to checking that every row inequality of each system is valid on the feasible
region of the other system. -/
theorem linear_inequality_solution_set_eq_iff_mutual_rowwise_validity
    {m p n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (C : Matrix (Fin p) (Fin n) ℝ) (d : Fin p → ℝ) :
    polyhedron_le_set A b = polyhedron_le_set C d ↔
      (∀ i : Fin p, ∀ ⦃x : Fin n → ℝ⦄, x ∈ polyhedron_le_set A b →
        (C *ᵥ x) i ≤ d i) ∧
      (∀ i : Fin m, ∀ ⦃x : Fin n → ℝ⦄, x ∈ polyhedron_le_set C d →
        (A *ᵥ x) i ≤ b i) := by
  constructor
  · intro hEq
    constructor
    · exact (linear_inequality_solution_set_subset_iff_rowwise_validity A b C d).mp hEq.subset
    · exact (linear_inequality_solution_set_subset_iff_rowwise_validity C d A b).mp hEq.symm.subset
  · rintro ⟨hCrows, hArows⟩
    apply Set.Subset.antisymm
    · exact (linear_inequality_solution_set_subset_iff_rowwise_validity A b C d).mpr hCrows
    · exact (linear_inequality_solution_set_subset_iff_rowwise_validity C d A b).mpr hArows
