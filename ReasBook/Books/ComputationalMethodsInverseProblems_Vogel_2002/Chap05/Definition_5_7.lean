/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_7.Fourier2D

public section

open scoped BigOperators

noncomputable section

namespace Matrix

/-- Helper for Definition 5.7: `Matrix.dft2D` is the concrete matrix product
`Matrix.fourierMatrix n_x * f * (Matrix.fourierMatrix n_y)ᵀ`. -/
lemma dft2DEqFourierMatrixMulTranspose (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    Matrix.dft2D n_x n_y f =
      Matrix.fourierMatrix n_x * f * (Matrix.fourierMatrix n_y)ᵀ := by
  -- Expand the linear map abbreviation and reassociate the matrix product.
  simp [Matrix.dft2D, Matrix.mul_assoc]

/-- Helper for Definition 5.7: `Matrix.invDFT2D` is the concrete matrix product
`(Matrix.fourierMatrix n_x)ᴴ * g * ((Matrix.fourierMatrix n_y)ᴴ)ᵀ`. -/
lemma invDFT2DEqConjTransposeMulTranspose (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : Matrix (Fin n_x) (Fin n_y) ℂ) :
    Matrix.invDFT2D n_x n_y g =
      (Matrix.fourierMatrix n_x)ᴴ * g * ((Matrix.fourierMatrix n_y)ᴴ)ᵀ := by
  -- Expand the linear map abbreviation and reassociate the matrix product.
  simp [Matrix.invDFT2D, Matrix.mul_assoc]

/-- Definition 5.7: the two-dimensional DFT on `Matrix (Fin n_x) (Fin n_y) ℂ`
has the entrywise formula from `(5.24)`, written as the product of the normalized
one-dimensional Fourier kernels in the `x`- and `y`-coordinates. -/
theorem _root_.Matrix.dft2D_apply (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) (i : Fin n_x) (j : Fin n_y) :
    Matrix.dft2D n_x n_y f i j =
      ∑ i' : Fin n_x, ∑ j' : Fin n_y,
        Matrix.fourierMatrix n_x i i' * f i' j' * Matrix.fourierMatrix n_y j j' := by
  -- Rewrite the transform to the concrete left-right Fourier-matrix product.
  rw [Matrix.dft2DEqFourierMatrixMulTranspose]
  -- Expand both matrix multiplications to expose the textbook double sum.
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_assoc]
  -- Swap the finite sums so the indices follow the source statement.
  rw [Finset.sum_comm]

/-- Definition 5.7: the inverse two-dimensional DFT is obtained from `(5.24)`
by replacing `-Complex.I` with `Complex.I`, equivalently by conjugating the normalized
one-dimensional Fourier kernels in the `x`- and `y`-coordinates. -/
theorem _root_.Matrix.invDFT2D_apply (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : Matrix (Fin n_x) (Fin n_y) ℂ) (i : Fin n_x) (j : Fin n_y) :
    Matrix.invDFT2D n_x n_y g i j =
      ∑ i' : Fin n_x, ∑ j' : Fin n_y,
        ((Matrix.fourierMatrix n_x)ᴴ) i i' * g i' j' * ((Matrix.fourierMatrix n_y)ᴴ) j j' := by
  -- Rewrite the inverse transform to the concrete left-right Fourier-matrix product.
  rw [Matrix.invDFT2DEqConjTransposeMulTranspose]
  -- Expand both matrix multiplications to expose the textbook double sum.
  simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_assoc]
  -- Swap the finite sums so the indices follow the source statement.
  rw [Finset.sum_comm]

end Matrix
