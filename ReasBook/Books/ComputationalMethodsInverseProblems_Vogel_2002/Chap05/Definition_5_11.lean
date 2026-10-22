/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Matrix.Basic

public section

universe u

namespace Matrix

variable {α : Type u}

/-- The `n × n` Toeplitz matrix whose `k`th diagonal coefficient is `t k`. -/
@[expose]
def toeplitzByDiag (n : ℕ) (t : ℤ → α) : Matrix (Fin n) (Fin n) α :=
  fun i j ↦ t (((i : ℕ) : ℤ) - (j : ℕ))

/-- Definition 5.11. The entries of `Matrix.toeplitzByDiag n t` are constant along
diagonals and are given by the diagonal coefficient `t (i - j)`. The associated
matrix-vector convolution formulas are recorded separately as
`Matrix.discreteConvolution_def` and `Matrix.discreteConvolution_apply`. -/
theorem toeplitzByDiag_apply (n : ℕ) (t : ℤ → α) (i j : Fin n) :
    toeplitzByDiag n t i j = t (((i : ℕ) : ℤ) - (j : ℕ)) := by
  -- Read the matrix entry directly from the defining lambda of `toeplitzByDiag`.
  rfl

end Matrix
