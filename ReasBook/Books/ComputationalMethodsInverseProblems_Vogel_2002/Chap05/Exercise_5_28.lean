/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Exercise_5_28.Permutation
public import Mathlib.Data.Complex.Basic

public section
namespace Matrix

/-- Helper for Exercise 5.28: the entries of `Matrix.columnToRowPermMatrix`
are the Kronecker-delta values determined by `Matrix.columnToRowPerm`. -/
theorem columnToRowPermMatrix_apply
    (n_x n_y : ℕ) (i j : Fin (n_y * n_x)) :
    Matrix.columnToRowPermMatrix ℂ n_x n_y i j =
      if j = Matrix.columnToRowPerm n_x n_y i then 1 else 0 := by
  -- Unfold the permutation matrix once and read off its unique nonzero entry.
  simp [Matrix.columnToRowPermMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

end Matrix
