/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.Logic.Equiv.Fin.Basic

public section

universe u

namespace Matrix

/-- The column-to-row reindexing permutation on `Fin (n_y * n_x)` obtained by
unflattening with `finProdFinEquiv.symm`, swapping the two coordinates, and
flattening again after identifying `n_x * n_y = n_y * n_x`. -/
def columnToRowPerm (n_x n_y : ℕ) : Equiv.Perm (Fin (n_y * n_x)) :=
  (((finProdFinEquiv : Fin n_y × Fin n_x ≃ Fin (n_y * n_x)).symm).trans
      (Equiv.prodComm (Fin n_y) (Fin n_x))).trans
    ((finProdFinEquiv : Fin n_x × Fin n_y ≃ Fin (n_x * n_y)).trans
      (finCongr (Nat.mul_comm n_x n_y)))

/-- The column-to-row permutation matrix from Exercise 5.28, under the chapter's
column-stacking `Matrix.vec` convention. -/
abbrev columnToRowPermMatrix (R : Type u) [Zero R] [One R] (n_x n_y : ℕ) :
    Matrix (Fin (n_y * n_x)) (Fin (n_y * n_x)) R :=
  (Matrix.columnToRowPerm n_x n_y).permMatrix R

/-- Multiplying a vector by the column-to-row permutation matrix composes it with
the underlying column-to-row permutation. -/
theorem columnToRowPermMatrix_mulVec
    (R : Type u) [CommRing R] (n_x n_y : ℕ) (v : Fin (n_y * n_x) → R) :
    Matrix.columnToRowPermMatrix R n_x n_y *ᵥ v = v ∘ Matrix.columnToRowPerm n_x n_y := by
  have h :
      (Matrix.columnToRowPerm n_x n_y).permMatrix R *ᵥ v =
        v ∘ Matrix.columnToRowPerm n_x n_y :=
    Matrix.permMatrix_mulVec (Matrix.columnToRowPerm n_x n_y)
  simpa [Matrix.columnToRowPermMatrix] using h

/-- Right-multiplying by the column-to-row permutation matrix composes a row vector
with the inverse column-to-row permutation. -/
theorem vecMul_columnToRowPermMatrix
    (R : Type u) [CommRing R] (n_x n_y : ℕ) (v : Fin (n_y * n_x) → R) :
    v ᵥ* Matrix.columnToRowPermMatrix R n_x n_y =
      v ∘ (Matrix.columnToRowPerm n_x n_y).symm := by
  -- Reuse the generic row-vector action of a permutation matrix.
  have h :
      v ᵥ* (Matrix.columnToRowPerm n_x n_y).permMatrix R =
        v ∘ (Matrix.columnToRowPerm n_x n_y).symm :=
    Matrix.vecMul_permMatrix (σ := Matrix.columnToRowPerm n_x n_y)
  -- The item-specific matrix is just this permutation matrix by definition.
  simpa [Matrix.columnToRowPermMatrix] using h

end Matrix
