/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.BTTB

public section

universe u

namespace Matrix

variable {α : Type u}

/-- Compatibility alias for the block Toeplitz with Toeplitz blocks owner `Matrix.bttb`. -/
abbrev httb (n_x n_y : ℕ) (t : ℤ → ℤ → α) :
    Matrix (Fin n_y × Fin n_x) (Fin n_y × Fin n_x) α :=
  Matrix.bttb n_x n_y t

/-- Compatibility entrywise formula for `Matrix.httb`. -/
theorem httb_apply {n_x n_y : ℕ} (t : ℤ → ℤ → α)
    (j l : Fin n_y) (i k : Fin n_x) :
    Matrix.httb n_x n_y t (j, i) (l, k) =
      t (((i : ℕ) : ℤ) - ((k : ℕ) : ℤ)) (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)) := by
  simpa [Matrix.httb] using Matrix.bttb_apply t j l i k

/-- Each `(j, l)` block of `Matrix.httb n_x n_y t` is the Toeplitz matrix
`Matrix.toeplitzByDiag n_x (fun d ↦ t d (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ)))`. -/
theorem httb_block_eq_toeplitzByDiag {n_x n_y : ℕ} (t : ℤ → ℤ → α) (j l : Fin n_y) :
    (Matrix.httb n_x n_y t).submatrix (fun i ↦ (j, i)) (fun k ↦ (l, k)) =
      Matrix.toeplitzByDiag n_x (fun d : ℤ ↦ t d (((j : ℕ) : ℤ) - ((l : ℕ) : ℤ))) := by
  simpa [Matrix.httb] using Matrix.bttb_block_eq_toeplitzByDiag t j l

end Matrix
