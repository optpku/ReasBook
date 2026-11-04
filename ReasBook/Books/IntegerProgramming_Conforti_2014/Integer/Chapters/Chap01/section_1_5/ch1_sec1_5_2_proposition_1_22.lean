/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_proposition_1_22.ColumnOperations

@[expose] public section

open scoped Matrix

namespace Matrix

section Proposition122

variable {m n : ℕ}

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_5/ch1_sec1_5_2_proposition_1_22.lean.
Proposition 1.22 (1): swapping two distinct columns of `A` is right multiplication by the
elementary column-swap matrix obtained from `1` by the same column interchange. -/
theorem swappedColumns_eq_mul_columnSwapMatrix
    (A : Matrix (Fin m) (Fin n) ℤ)
    (i j : Fin n)
    (hij : i ≠ j) :
    A.submatrix id (Equiv.swap i j) = A * Matrix.columnSwapMatrix i j := by
  by_cases hEq : i = j
  · exact (hij hEq).elim
  · -- Compare the matrices row by row, where right multiplication is vector multiplication.
    ext r k
    simpa only [Matrix.submatrix_apply, Matrix.mul_apply_eq_vecMul] using
      congrFun (Matrix.vecMul_swap i j (A r)).symm k

/-- Proposition 1.22 (2): negating column `i` of `A` is right multiplication by the elementary
column-sign matrix obtained from `1` by negating the same column. -/
theorem negatedColumn_eq_mul_columnNegMatrix
    (A : Matrix (Fin m) (Fin n) ℤ)
    (i : Fin n) :
    A.updateCol i (-A.col i) = A * Matrix.columnNegMatrix i := by
  -- Entrywise, the sign matrix contributes only its diagonal term.
  ext r k
  by_cases hki : k = i
  · subst k
    simp [Matrix.columnNegMatrix, Matrix.mul_apply]
  · simp [Matrix.columnNegMatrix, Matrix.mul_apply, hki]

/-- Proposition 1.22 (3): adding `c` times column `source` to a different column `target` of `A`
is right multiplication by the corresponding elementary column-addition matrix. -/
theorem columnAdd_eq_mul_columnAddMatrix
    (A : Matrix (Fin m) (Fin n) ℤ)
    (source target : Fin n)
    (c : ℤ)
    (h : source ≠ target) :
    A.updateCol target (A.col target + c • A.col source) =
      A * Matrix.columnAddMatrix source target c := by
  by_cases hEq : source = target
  · exact (h hEq).elim
  · -- Expand the transvection into the identity and its single off-diagonal entry.
    unfold Matrix.columnAddMatrix Matrix.transvection
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_single_eq_updateCol_zero]
    -- The updated column agrees entrywise; the affected entry uses commutativity in `ℤ`.
    ext r k
    by_cases hkt : k = target
    · subst k
      simp [mul_comm]
    · simp [hkt]

end Proposition122

end Matrix
