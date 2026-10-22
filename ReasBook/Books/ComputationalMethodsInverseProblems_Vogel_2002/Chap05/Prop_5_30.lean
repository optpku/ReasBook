/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_7.Fourier2D
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_25.Array

public section

open scoped Kronecker Matrix

namespace Matrix

/-- Vectorizing `Matrix.dft2D` turns the two-sided Fourier-matrix action into the
Kronecker-product Fourier matrix acting on `f.vec`. -/
theorem vec_dft2D_eq_kronFourier_mulVec (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    (dft2D n_x n_y f).vec = (fourierMatrix n_y ⊗ₖ fourierMatrix n_x) *ᵥ f.vec := by
  rw [dft2D_def]
  rw [← kronecker_mulVec_vec]

/-- Proposition 5.30. The two-dimensional Fourier transform is reconstructed by
the canonical `Matrix.of` from the Kronecker-product Fourier matrix applied to
`f.vec`. -/
theorem dft2D_eq_of_kronFourier_mulVec (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    dft2D n_x n_y f = of fun i j ↦ ((fourierMatrix n_y ⊗ₖ fourierMatrix n_x) *ᵥ f.vec) (j, i) := by
  rw [← of_vec (dft2D n_x n_y f)]
  congr
  funext i
  funext j
  exact congrFun (vec_dft2D_eq_kronFourier_mulVec n_x n_y f) (j, i)

end Matrix
