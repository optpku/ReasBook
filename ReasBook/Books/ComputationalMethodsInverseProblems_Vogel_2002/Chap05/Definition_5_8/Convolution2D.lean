/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Complex.Basic
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_24.HTTB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_25.Array

public section

open scoped Matrix

namespace Matrix

/-- The two-dimensional discrete convolution of an integer-indexed complex kernel
with a finite complex array, implemented through the HTTB backend. -/
def discreteConvolution2D {n_x n_y : ℕ} (t : ℤ → ℤ → ℂ)
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) : Matrix (Fin n_x) (Fin n_y) ℂ :=
  Matrix.of fun i j ↦ (Matrix.httb n_x n_y t *ᵥ f.vec) (j, i)

/-- The HTTB-array backend for `Matrix.discreteConvolution2D`. -/
theorem discreteConvolution2D_def {n_x n_y : ℕ} (t : ℤ → ℤ → ℂ)
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    Matrix.discreteConvolution2D t f =
      Matrix.of fun i j ↦ (Matrix.httb n_x n_y t *ᵥ f.vec) (j, i) := by
  -- `Matrix.discreteConvolution2D` is defined as this HTTB-array reconstruction.
  rfl

/-- Vectorizing `Matrix.discreteConvolution2D` recovers the HTTB matrix-vector action. -/
theorem vec_discreteConvolution2D {n_x n_y : ℕ} (t : ℤ → ℤ → ℂ)
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    (Matrix.discreteConvolution2D t f).vec = Matrix.httb n_x n_y t *ᵥ f.vec := by
  -- After unfolding the definition, `Matrix.vec_of_swap` removes the reconstruction.
  rw [Matrix.discreteConvolution2D_def, Matrix.vec_of_swap]

end Matrix
