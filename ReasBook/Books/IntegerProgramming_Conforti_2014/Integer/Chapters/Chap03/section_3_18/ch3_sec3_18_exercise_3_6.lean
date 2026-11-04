/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_4_1.ch3_sec3_4_1_definition_3_4_1_extra_1

open scoped Matrix

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain sampling for this exercise:
-- * primary domain: linear-algebraic kernels of matrix maps on `Fin n → ℝ`
-- * source-facing owner in this chapter: `set_is_linear_space_iff_eq_matrix_kernel`
-- * core mathlib owner abstraction: `LinearMap.ker A.mulVecLin`
-- * derived source-facing API: the zero locus `{x | A *ᵥ x = 0}`

/- Exercise 3.6 (1): this is already the chapter owner theorem
`set_is_linear_space_iff_eq_matrix_kernel`. -/
recall set_is_linear_space_iff_eq_matrix_kernel

/-- Exercise 3.6 (2): if a linear space is given as the zero locus of a matrix, then its
dimension is the ambient dimension minus the rank of that matrix. -/
theorem finrank_eq_ambient_sub_matrix_rank_of_eq_zero_set
    {m n : ℕ} (L : Submodule ℝ (Fin n → ℝ)) (A : Matrix (Fin m) (Fin n) ℝ)
    (hL : (L : Set (Fin n → ℝ)) = {x : Fin n → ℝ | A *ᵥ x = 0}) :
    Module.finrank ℝ L = n - A.rank := by
  have hker : L = LinearMap.ker A.mulVecLin := by
    ext x
    change x ∈ (L : Set (Fin n → ℝ)) ↔ A.mulVecLin x = 0
    rw [hL]
    simp
  rw [hker]
  simpa using finrank_matrix_kernel_eq_ambient_sub_rank A
