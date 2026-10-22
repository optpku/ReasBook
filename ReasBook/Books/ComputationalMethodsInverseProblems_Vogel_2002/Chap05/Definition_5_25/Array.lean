/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Vec

public section

universe u

namespace Matrix

variable {α : Type u}

/-- Reconstructing a matrix from its vectorization is the canonical `Matrix.of`
constructor applied to the swapped product indices. -/
theorem of_vec {n_x n_y : ℕ} (c : Matrix (Fin n_x) (Fin n_y) α) :
    Matrix.of (fun i j ↦ c.vec (j, i)) = c := by
  ext i j
  rfl

/-- Vectorizing the canonical reconstruction from a column-stacked array
indexed by `Fin n_y × Fin n_x` recovers that array. -/
theorem vec_of_swap {n_x n_y : ℕ} (v : Fin n_y × Fin n_x → α) :
    Matrix.vec (Matrix.of fun i j ↦ v (j, i)) = v := by
  funext ij
  cases ij
  rfl

end Matrix
