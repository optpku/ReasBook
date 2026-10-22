/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1.FourierMatrix
public import Mathlib.LinearAlgebra.Matrix.Kronecker

public section

open scoped Kronecker

namespace Matrix

/-- Exercise 5.23. The Kronecker product of the Chapter 5 normalized Fourier matrices is
unitary. -/
theorem fourierKronecker_mem_unitaryGroup (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] :
    Matrix.fourierMatrix n_y ⊗ₖ Matrix.fourierMatrix n_x ∈
      Matrix.unitaryGroup (Fin n_y × Fin n_x) ℂ := by
  simpa using
    (Matrix.kronecker_mem_unitary
      (Matrix.fourierMatrix_mem_unitaryGroup n_y)
      (Matrix.fourierMatrix_mem_unitaryGroup n_x))

/-- The conjugate-transpose cancellation form of the Fourier Kronecker unitarity statement. -/
theorem fourierKronecker_conjTranspose_mul (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] :
    (Matrix.fourierMatrix n_y ⊗ₖ Matrix.fourierMatrix n_x)ᴴ *
        (Matrix.fourierMatrix n_y ⊗ₖ Matrix.fourierMatrix n_x) =
      1 :=
  Matrix.mem_unitaryGroup_iff'.mp <| fourierKronecker_mem_unitaryGroup n_x n_y

end Matrix
