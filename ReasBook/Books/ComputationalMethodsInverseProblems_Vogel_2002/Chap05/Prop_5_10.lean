/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_2

public section

namespace Matrix

/-- Proposition 5.10. In the normalized two-dimensional Fourier conventions,
convolving `f` with the periodic extension `t^ext` of `t` is the inverse
normalized transform of the Hadamard product of the normalized transforms, with
the explicit source factor `(1 / √(n_x * n_y))`. This is the source-facing
rephrasing of
`Matrix.periodicExtension_discreteConvolution2D_eq_ifft2_hadamard_fft2`
through the normalized owners `Matrix.dft2D` and `Matrix.invDFT2D`. -/
theorem periodicExtension_discreteConvolution2D_eq_invDFT2D_hadamard_dft2D
    (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (t f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) •
        Matrix.discreteConvolution2D
          (Matrix.periodicExtensionOfNeZero t) f =
      Matrix.invDFT2D n_x n_y
        (Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f)) := by
  let α : ℂ := (Real.sqrt n_x : ℂ) * Real.sqrt n_y
  have hα : α ≠ 0 := by
    dsimp [α]
    exact mul_ne_zero
      (by
        simpa using
          (Real.sqrt_ne_zero'.2
            (show (0 : ℝ) < n_x by exact_mod_cast Nat.pos_of_neZero n_x)))
      (by
        simpa using
          (Real.sqrt_ne_zero'.2
            (show (0 : ℝ) < n_y by exact_mod_cast Nat.pos_of_neZero n_y)))
  have hconv :
      Matrix.discreteConvolution2D
          (Matrix.periodicExtensionOfNeZero t) f =
        α • Matrix.invDFT2D n_x n_y
          (Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f)) := by
    calc
      Matrix.discreteConvolution2D
          (Matrix.periodicExtensionOfNeZero t) f =
        Matrix.ifft2 n_x n_y
          (Matrix.hadamard (Matrix.fft2 n_x n_y t) (Matrix.fft2 n_x n_y f)) := by
            simpa [Matrix.periodicExtensionOfNeZero] using
              Matrix.periodicExtension_discreteConvolution2D_eq_ifft2_hadamard_fft2 n_x n_y t f
      _ = α⁻¹ • Matrix.invDFT2D n_x n_y
            (Matrix.hadamard (α • Matrix.dft2D n_x n_y t) (α • Matrix.dft2D n_x n_y f)) := by
              simp [α, Matrix.fft2, Matrix.ifft2]
      _ = α⁻¹ • Matrix.invDFT2D n_x n_y
            (α • (α • Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f))) := by
              rw [Matrix.smul_hadamard, Matrix.hadamard_smul]
      _ = α⁻¹ • (α • (α • Matrix.invDFT2D n_x n_y
            (Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f)))) := by
              rw [map_smul, map_smul]
      _ = α • Matrix.invDFT2D n_x n_y
            (Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f)) := by
              simp [smul_smul, hα]
  calc
    α⁻¹ •
        Matrix.discreteConvolution2D
          (Matrix.periodicExtensionOfNeZero t) f =
      α⁻¹ •
        (α • Matrix.invDFT2D n_x n_y
          (Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f))) := by
            rw [hconv]
    _ = Matrix.invDFT2D n_x n_y
          (Matrix.hadamard (Matrix.dft2D n_x n_y t) (Matrix.dft2D n_x n_y f)) := by
            simp [smul_smul, hα]

end Matrix
