/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1.MatrixPolyhedron

open scoped Matrix

section Definition110FeasibleRegion

variable {m n : ℕ}

/-- The nonnegative linear polyhedron `{x | A *ᵥ x ≤ b, x ≥ 0}` attached to real data `(A, b)`. -/
def nonnegative_linear_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  polyhedron_le_set A b ∩ Set.Ici (0 : Fin n → ℝ)

/-- Membership in `nonnegative_linear_polyhedron A b` is exactly the conjunction of the linear
inequalities `A *ᵥ x ≤ b` and coordinatewise nonnegativity `0 ≤ x`. -/
theorem mem_nonnegative_linear_polyhedron_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {x : Fin n → ℝ} :
    x ∈ nonnegative_linear_polyhedron A b ↔ A *ᵥ x ≤ b ∧ 0 ≤ x := by
  rw [nonnegative_linear_polyhedron, Set.mem_inter_iff, mem_polyhedron_le_set_iff]
  rfl

/-- Definition 1.10. The feasible region of the standard-form linear program
`max {c ⬝ᵥ x | A *ᵥ x ≤ b, x ≥ 0}`. -/
abbrev linear_programming_feasible_set
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) : Set (Fin n → ℝ) :=
  nonnegative_linear_polyhedron A b

/-- `linear_programming_feasible_set A b` is definitionally the canonical nonnegative linear
polyhedron cut out by `(A, b)`. -/
theorem linear_programming_feasible_set_eq_nonnegative_linear_polyhedron
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    linear_programming_feasible_set A b = nonnegative_linear_polyhedron A b :=
  rfl

/-- Membership in `linear_programming_feasible_set A b` means satisfying `A *ᵥ x ≤ b` together
with the coordinatewise nonnegativity constraint `0 ≤ x`. -/
theorem mem_linear_programming_feasible_set_iff
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {x : Fin n → ℝ} :
    x ∈ linear_programming_feasible_set A b ↔ A *ᵥ x ≤ b ∧ 0 ≤ x :=
  mem_nonnegative_linear_polyhedron_iff

end Definition110FeasibleRegion
