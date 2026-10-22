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
Fourier solve on already assembled block-circulant-extension arrays.
-/

/-- The doubled-grid Fourier solve used by Algorithm 5.3.2 once the
block-circulant-extension arrays `c_t` and `c_ℓ` have already been assembled
from the source kernels by `(5.61)`-`(5.63)`. -/
@[expose] def blockCirculantExtensionAssembledTikhonovRegularization
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (c_t c_ℓ : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (r : ℂ^[n_x, n_y]) :
    ℂ^[n_x, n_y] :=
  let c_tHat := Matrix.fft2 (2 * n_x) (2 * n_y) c_t
  let c_ℓHat := Matrix.fft2 (2 * n_x) (2 * n_y) c_ℓ
  let rHatExt := Matrix.fft2 (2 * n_x) (2 * n_y)
    (Matrix.blockCirculantExtensionZeroPad r)
  let denom := Matrix.hadamard (fun i j ↦ star (c_tHat i j)) c_tHat + (α : ℂ) • c_ℓHat
  let sHatExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ :=
    fun i j ↦ rHatExt i j / denom i j
  Matrix.blockCirculantExtensionLeadingBlock
    (Matrix.ifft2 (2 * n_x) (2 * n_y) sHatExt)

/-- The defining formula for
`Matrix.blockCirculantExtensionAssembledTikhonovRegularization`. -/
theorem blockCirculantExtensionAssembledTikhonovRegularization_def
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (c_t c_ℓ : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (r : ℂ^[n_x, n_y]) :
    Matrix.blockCirculantExtensionAssembledTikhonovRegularization α c_t c_ℓ r =
      let c_tHat := Matrix.fft2 (2 * n_x) (2 * n_y) c_t
      let c_ℓHat := Matrix.fft2 (2 * n_x) (2 * n_y) c_ℓ
      let rHatExt := Matrix.fft2 (2 * n_x) (2 * n_y)
        (Matrix.blockCirculantExtensionZeroPad r)
      let denom := Matrix.hadamard (fun i j ↦ star (c_tHat i j)) c_tHat + (α : ℂ) • c_ℓHat
      let sHatExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ :=
        fun i j ↦ rHatExt i j / denom i j
      Matrix.blockCirculantExtensionLeadingBlock
        (Matrix.ifft2 (2 * n_x) (2 * n_y) sHatExt) := rfl

/-- The vectorized output of
`Matrix.blockCirculantExtensionAssembledTikhonovRegularization`. -/
abbrev blockCirculantExtensionAssembledTikhonovRegularizationVec
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (c_t c_ℓ : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (r : ℂ^[n_x, n_y]) :
    Fin n_y × Fin n_x → ℂ :=
  Matrix.vec (Matrix.blockCirculantExtensionAssembledTikhonovRegularization α c_t c_ℓ r)

/-- The defining formula for
`Matrix.blockCirculantExtensionAssembledTikhonovRegularizationVec`. -/
theorem blockCirculantExtensionAssembledTikhonovRegularizationVec_def
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (c_t c_ℓ : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (r : ℂ^[n_x, n_y]) :
    Matrix.blockCirculantExtensionAssembledTikhonovRegularizationVec α c_t c_ℓ r =
      Matrix.vec (Matrix.blockCirculantExtensionAssembledTikhonovRegularization α c_t c_ℓ r) := rfl

/-- Evaluating the vectorized doubled-grid Tikhonov output at `(j, i)` returns
the `(i, j)` entry of the assembled-array solution. -/
theorem blockCirculantExtensionAssembledTikhonovRegularizationVec_apply
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (c_t c_ℓ : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ)
    (r : ℂ^[n_x, n_y])
    (q : Fin n_y × Fin n_x) :
    Matrix.blockCirculantExtensionAssembledTikhonovRegularizationVec α c_t c_ℓ r q =
      Matrix.blockCirculantExtensionAssembledTikhonovRegularization α c_t c_ℓ r q.2 q.1 := by
  rcases q with ⟨j, i⟩
  rfl

end Matrix
