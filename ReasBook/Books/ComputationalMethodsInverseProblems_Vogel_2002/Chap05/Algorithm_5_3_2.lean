/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Algorithm_5_2_1.CirculantExtension
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Algorithm_5_3_2.Assembled

public section

open scoped Complex.FiniteDimensional

noncomputable section

namespace Matrix

/-!
Algorithm 5.3.2 is source-facing in the odd-grid kernels `t` and `ℓ`. The
reusable doubled-grid Fourier solve on already assembled extension arrays
`c_t` and `c_ℓ` is owned by `Book.Ch5.Algorithm_5_3_2.Assembled`.
-/

/-- Source-facing wrapper for Algorithm 5.3.2: assemble the doubled
block-circulant-extension arrays from the odd-grid kernels `t` and `ℓ` by
`(5.61)`-`(5.63)`, zero-pad `r`, perform the doubled-grid Fourier-domain solve,
and extract the leading `n_x × n_y` block. -/
@[expose] def blockCirculantExtensionTikhonovRegularization
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    ℂ^[n_x, n_y] :=
  blockCirculantExtensionAssembledTikhonovRegularization α
    (blockCirculantExtension t)
    (blockCirculantExtension ℓ)
    r

/-- The defining source-facing doubled-grid Fourier formula for
`blockCirculantExtensionTikhonovRegularization`. -/
theorem blockCirculantExtensionTikhonovRegularization_def
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    blockCirculantExtensionTikhonovRegularization α t ℓ r =
      let c_t := blockCirculantExtension t
      let c_ℓ := blockCirculantExtension ℓ
      let c_tHat := fft2 (2 * n_x) (2 * n_y) c_t
      let c_ℓHat := fft2 (2 * n_x) (2 * n_y) c_ℓ
      let rHatExt := fft2 (2 * n_x) (2 * n_y) (blockCirculantExtensionZeroPad r)
      let denom := hadamard (fun i j ↦ star (c_tHat i j)) c_tHat + (α : ℂ) • c_ℓHat
      let sHatExt : Matrix (Fin (2 * n_x)) (Fin (2 * n_y)) ℂ :=
        fun i j ↦ rHatExt i j / denom i j
      blockCirculantExtensionLeadingBlock (ifft2 (2 * n_x) (2 * n_y) sHatExt) := by
  simp [blockCirculantExtensionTikhonovRegularization,
    blockCirculantExtensionAssembledTikhonovRegularization]

/-- The source-kernel owner is the assembled doubled-grid owner specialized to
`blockCirculantExtension t` and `blockCirculantExtension ℓ`. -/
theorem blockCirculantExtensionTikhonovRegularization_assembled
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    blockCirculantExtensionTikhonovRegularization α t ℓ r =
      blockCirculantExtensionAssembledTikhonovRegularization α
        (blockCirculantExtension t)
        (blockCirculantExtension ℓ)
        r := rfl

/-- Helper for Algorithm 5.3.2: vectorizing the source-facing solve agrees with
the assembled doubled-grid vector API after assembling `t` and `ℓ`. -/
theorem vec_blockCirculantExtensionTikhonovRegularization_assembled
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    vec (blockCirculantExtensionTikhonovRegularization α t ℓ r) =
      blockCirculantExtensionAssembledTikhonovRegularizationVec α
        (blockCirculantExtension t)
        (blockCirculantExtension ℓ)
        r := by
  -- Rewriting the source-facing solve through the assembled owner exposes the
  -- already packaged vectorized doubled-grid API directly.
  rw [blockCirculantExtensionTikhonovRegularization_assembled]

/-- The vectorized output of `blockCirculantExtensionTikhonovRegularization`,
matching the final source assignment `mathbf s = Matrix.vec s`. -/
abbrev blockCirculantExtensionTikhonovRegularizationVec
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    Fin n_y × Fin n_x → ℂ :=
  vec (blockCirculantExtensionTikhonovRegularization α t ℓ r)

/-- The defining formula for
`blockCirculantExtensionTikhonovRegularizationVec`. -/
theorem blockCirculantExtensionTikhonovRegularizationVec_def
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    blockCirculantExtensionTikhonovRegularizationVec α t ℓ r =
      vec (blockCirculantExtensionTikhonovRegularization α t ℓ r) := rfl

/-- Evaluating `blockCirculantExtensionTikhonovRegularizationVec` at `(j, i)`
returns the `(i, j)` entry of the source-kernel solution array. -/
theorem blockCirculantExtensionTikhonovRegularizationVec_apply
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y])
    (q : Fin n_y × Fin n_x) :
    blockCirculantExtensionTikhonovRegularizationVec α t ℓ r q =
      blockCirculantExtensionTikhonovRegularization α t ℓ r q.2 q.1 := by
  rcases q with ⟨j, i⟩
  rfl

/-- The source-kernel vectorization agrees with the assembled-array bridge
after assembling `t` and `ℓ` via `blockCirculantExtension`. -/
theorem blockCirculantExtensionTikhonovRegularizationVec_assembled
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    blockCirculantExtensionTikhonovRegularizationVec α t ℓ r =
      blockCirculantExtensionAssembledTikhonovRegularizationVec α
        (blockCirculantExtension t)
        (blockCirculantExtension ℓ)
        r := by
  -- The public vector abbreviation is just `Matrix.vec` of the source-facing
  -- solve, so the assembled bridge reduces to the vectorization helper above.
  simpa [blockCirculantExtensionTikhonovRegularizationVec] using
    vec_blockCirculantExtensionTikhonovRegularization_assembled α t ℓ r

/-- Algorithm 5.3.2. The final source vector
`mathbf s` is the vectorization of the extracted leading block `s` produced by
the source-facing block-circulant-extension Tikhonov solve. -/
theorem blockCirculantExtensionTikhonovRegularizationVec_spec
    {n_x n_y : ℕ} [NeZero (2 * n_x)] [NeZero (2 * n_y)]
    (α : ℝ)
    (t ℓ : ℂ^[2 * n_x - 1, 2 * n_y - 1])
    (r : ℂ^[n_x, n_y]) :
    blockCirculantExtensionTikhonovRegularizationVec α t ℓ r =
      vec (blockCirculantExtensionTikhonovRegularization α t ℓ r) := rfl

end Matrix
