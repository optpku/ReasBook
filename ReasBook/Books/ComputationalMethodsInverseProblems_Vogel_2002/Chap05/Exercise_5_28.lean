/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Complex.Basic

public section

universe u

namespace Matrix

/-- Helper for Exercise 5.28: `Matrix.columnToRowPerm` swaps the two coordinates
obtained by unflattening an index in `Fin (n_y * n_x)`. -/
def columnToRowPerm (n_x n_y : ℕ) : Equiv.Perm (Fin (n_y * n_x)) :=
  (((finProdFinEquiv : Fin n_y × Fin n_x ≃ Fin (n_y * n_x)).symm).trans
      (Equiv.prodComm (Fin n_y) (Fin n_x))).trans
    ((finProdFinEquiv : Fin n_x × Fin n_y ≃ Fin (n_x * n_y)).trans
      (finCongr (Nat.mul_comm n_x n_y)))

/-- Exercise 5.28. Under the chapter's column-stacking `Matrix.vec`
convention, the column-to-row permutation matrix `P` from equation `(5.79)` is
the permutation matrix attached to `Matrix.columnToRowPerm n_x n_y`. -/
abbrev columnToRowPermMatrix (R : Type u) [Zero R] [One R] (n_x n_y : ℕ) :
    Matrix (Fin (n_y * n_x)) (Fin (n_y * n_x)) R :=
  (Matrix.columnToRowPerm n_x n_y).permMatrix R

/-- Helper for Exercise 5.28: the entries of `Matrix.columnToRowPermMatrix`
are the Kronecker-delta values determined by `Matrix.columnToRowPerm`. -/
theorem columnToRowPermMatrix_apply
    (n_x n_y : ℕ) (i j : Fin (n_y * n_x)) :
    Matrix.columnToRowPermMatrix ℂ n_x n_y i j =
      if j = Matrix.columnToRowPerm n_x n_y i then 1 else 0 := by
  -- Unfold the permutation matrix once and read off its unique nonzero entry.
  simp [Matrix.columnToRowPermMatrix, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, eq_comm]

end Matrix
