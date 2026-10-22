/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap04.Exercise_4_19.ColumnNormalization

public section

open scoped BigOperators

/-- Exercise 4.19. Replacing each entry `K i j` by `K i j / ∑ i', K i' j` yields a matrix `S`
whose matrix-vector product preserves total mass. -/
theorem normalizedMatrix_preserves_totalMass
    {m n : ℕ} (K : Matrix (Fin m) (Fin n) ℝ) (hcol : ∀ j, ∑ i, K i j ≠ 0) (f : Fin n → ℝ) :
    ∑ j, f j = ∑ i, Matrix.mulVec (Matrix.columnNormalized K) f i := by
  simpa using (Matrix.columnNormalized_sum_mulVec_eq_sum K hcol f).symm
