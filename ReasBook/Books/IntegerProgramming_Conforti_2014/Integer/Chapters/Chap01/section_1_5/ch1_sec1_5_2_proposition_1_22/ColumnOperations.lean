module

public import Mathlib.LinearAlgebra.Matrix.RowCol
public import Mathlib.LinearAlgebra.Matrix.Swap
public import Mathlib.LinearAlgebra.Matrix.Transvection
public import Mathlib.RingTheory.Int.Basic

@[expose] public section

open scoped Matrix

namespace Matrix

section ColumnOperations

variable {n : ℕ}

/-- The elementary integer column-swap matrix exchanging columns `i` and `j`. -/
abbrev columnSwapMatrix (i j : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.swap ℤ i j

/-- The elementary integer column-sign matrix negating column `i`. -/
def columnNegMatrix (i : Fin n) : Matrix (Fin n) (Fin n) ℤ :=
  fun r c ↦ if r = c then if r = i then (-1 : ℤ) else 1 else 0

/-- The elementary integer column-addition matrix adding `c` times column `source` to column
`target`. -/
abbrev columnAddMatrix (source target : Fin n) (c : ℤ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.transvection source target c

/-- A square integer matrix is elementary unimodular if it is a column swap, a column sign change,
or an integer column addition matrix. -/
def IsElementaryUnimodularColumnMatrix (M : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∃ i j : Fin n, i ≠ j ∧ M = columnSwapMatrix i j) ∨
    (∃ i : Fin n, M = columnNegMatrix i) ∨
      ∃ source target : Fin n, ∃ c : ℤ, source ≠ target ∧ M = columnAddMatrix source target c

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_proposition_1_22/ColumnOperations.lean`:
the column-sign matrix is the diagonal matrix with one negative diagonal entry. -/
lemma columnNegMatrix_eq_diagonal (i : Fin n) :
    columnNegMatrix i = diagonal (fun j => if j = i then (-1 : ℤ) else 1) := by
  -- Compare the defining formulas entry by entry.
  ext r c
  rfl

/-- Helper for remote integer-programming sorry cleanup
`Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_proposition_1_22/ColumnOperations.lean`:
the column-sign matrix is its own multiplicative inverse. -/
lemma columnNegMatrix_mul_self (i : Fin n) :
    columnNegMatrix i * columnNegMatrix i = (1 : Matrix (Fin n) (Fin n) ℤ) := by
  -- Normalize both factors to diagonal matrices so multiplication is pointwise.
  rw [columnNegMatrix_eq_diagonal, diagonal_mul_diagonal]
  ext r c
  by_cases hrc : r = c
  · subst c
    by_cases hri : r = i
    · simp [hri]
    · simp [hri]
  · simp [hrc]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_proposition_1_22/ColumnOperations.lean.
The determinant of a column-swap matrix is a unit in `ℤ`. -/
theorem isUnit_det_columnSwapMatrix (i j : Fin n) :
    IsUnit (columnSwapMatrix i j).det := by
  -- Push the self-inverse identity for a swap matrix through the determinant.
  have hmatrix : columnSwapMatrix i j * columnSwapMatrix i j = 1 :=
    swap_mul_self i j
  have hdet : (columnSwapMatrix i j).det * (columnSwapMatrix i j).det = 1 := by
    simpa only [det_mul, det_one] using congrArg det hmatrix
  -- A determinant possessing this explicit inverse is a unit.
  exact IsUnit.of_mul_eq_one _ hdet

/-- The determinant of a column-sign matrix is a unit in `ℤ`. -/
theorem isUnit_det_columnNegMatrix (i : Fin n) :
    IsUnit (columnNegMatrix i).det := by
  -- Push the sign matrix's self-inverse identity through the determinant.
  have hdet : (columnNegMatrix i).det * (columnNegMatrix i).det = 1 := by
    simpa only [det_mul, det_one] using congrArg det (columnNegMatrix_mul_self i)
  -- The second determinant factor supplies an explicit inverse.
  exact IsUnit.of_mul_eq_one _ hdet

/-- The determinant of a column-addition matrix is a unit in `ℤ`. -/
theorem isUnit_det_columnAddMatrix (source target : Fin n) (c : ℤ) (h : source ≠ target) :
    IsUnit (columnAddMatrix source target c).det := by
  -- A transvection between distinct indices has determinant one.
  have hdet : (columnAddMatrix source target c).det = 1 :=
    det_transvection_of_ne source target h c
  rw [hdet]
  exact isUnit_one

end ColumnOperations

end Matrix

#print axioms Matrix.isUnit_det_columnSwapMatrix
