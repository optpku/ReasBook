/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Algorithm_5_2_1.DoubledGrid
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_2

public section

open scoped Complex.FiniteDimensional

noncomputable section

namespace Matrix

/-!
This directly importable foundation module owns the reusable doubled-grid
Fourier product on an already assembled block-circulant-extension array.
-/

/-- The doubled-grid Fourier product used by Algorithm 5.2.1 once the
block-circulant-extension array `cExt` has already been assembled from the
source kernel by `(5.61)`-`(5.63)`. -/
@[expose] def blockCirculantExtensionAssembledProduct
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (cExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (f : ℂ^[n_x, n_y]) :
    ℂ^[n_x, n_y] :=
  let fExt := Matrix.blockCirculantExtensionZeroPad f
  Matrix.blockCirculantExtensionLeadingBlock
    (Matrix.ifft2 (2 * n_x) (2 * n_y)
      (Matrix.hadamard
        (Matrix.fft2 (2 * n_x) (2 * n_y) cExt)
        (Matrix.fft2 (2 * n_x) (2 * n_y) fExt)))

/-- The defining doubled-grid Fourier formula for
`Matrix.blockCirculantExtensionAssembledProduct`. -/
theorem blockCirculantExtensionAssembledProduct_def
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (cExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (f : ℂ^[n_x, n_y]) :
    Matrix.blockCirculantExtensionAssembledProduct cExt f =
      let fExt := Matrix.blockCirculantExtensionZeroPad f
      Matrix.blockCirculantExtensionLeadingBlock
        (Matrix.ifft2 (2 * n_x) (2 * n_y)
          (Matrix.hadamard
            (Matrix.fft2 (2 * n_x) (2 * n_y) cExt)
            (Matrix.fft2 (2 * n_x) (2 * n_y) fExt))) := rfl

/-- The vectorized output of `Matrix.blockCirculantExtensionAssembledProduct`. -/
abbrev blockCirculantExtensionAssembledProductVec
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (cExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (f : ℂ^[n_x, n_y]) :
    Fin n_y × Fin n_x → ℂ :=
  Matrix.vec (Matrix.blockCirculantExtensionAssembledProduct cExt f)

/-- The defining formula for `Matrix.blockCirculantExtensionAssembledProductVec`. -/
theorem blockCirculantExtensionAssembledProductVec_def
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (cExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (f : ℂ^[n_x, n_y]) :
    Matrix.blockCirculantExtensionAssembledProductVec cExt f =
      Matrix.vec (Matrix.blockCirculantExtensionAssembledProduct cExt f) := rfl

/-- Evaluating the vectorized assembled doubled-grid product at `(j, i)`
returns the `(i, j)` entry of the extracted array. -/
theorem blockCirculantExtensionAssembledProductVec_apply
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (cExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (f : ℂ^[n_x, n_y])
    (q : Fin n_y × Fin n_x) :
    Matrix.blockCirculantExtensionAssembledProductVec cExt f q =
      Matrix.blockCirculantExtensionAssembledProduct cExt f q.2 q.1 := by
  rcases q with ⟨j, i⟩
  rfl

end Matrix
