/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Remark_5_17
public import Mathlib.LinearAlgebra.Eigenspace.Matrix

public section

open Module.End

namespace Matrix

/- Corollary 5.16 (1). A circulant matrix is diagonalized by the Chapter 5
Fourier matrix, with diagonal entries given by `Matrix.fft n c`.

This clause is already formalized exactly as
`Matrix.circulant_eq_fourierDiagonal_fft`. -/
#check circulant_eq_fourierDiagonal_fft

/-- Helper for Corollary 5.16: the spectrum of a circulant matrix agrees with the
spectrum of the diagonal matrix whose entries are `Matrix.fft n c`. -/
lemma circulantSpectrum_eq_diagonalFftSpectrum {n : ℕ} [NeZero n] (c : Fin n → ℂ) :
    spectrum ℂ (circulant c) = spectrum ℂ (diagonal (fft n c)) := by
  let F : Matrix (Fin n) (Fin n) ℂ := fourierMatrix n
  have hFhF : Fᴴ * F = 1 := by
    -- The Fourier matrix is unitary, so its conjugate transpose is a left inverse.
    simpa [F] using Matrix.fourierMatrix_conjTranspose_mul n
  have hFFh : F * Fᴴ = 1 := by
    -- The same unitary identity gives the right inverse needed for conjugation.
    exact Matrix.mem_unitaryGroup_iff.mp <| Matrix.fourierMatrix_mem_unitaryGroup n
  let u : (Matrix (Fin n) (Fin n) ℂ)ˣ := ⟨F, Fᴴ, hFFh, hFhF⟩
  have hconj :
      spectrum ℂ (u⁻¹ * diagonal (fft n c) * u) = spectrum ℂ (diagonal (fft n c)) :=
    spectrum.units_conjugate'
  -- Replace the circulant matrix by its Fourier diagonalization, then forget the unitary conjugacy.
  calc
    spectrum ℂ (circulant c) = spectrum ℂ (Fᴴ * diagonal (fft n c) * F) := by
      rw [circulant_eq_fourierDiagonal_fft n c]
    _ = spectrum ℂ (u⁻¹ * diagonal (fft n c) * u) := by
      simp [u, F]
    _ = spectrum ℂ (diagonal (fft n c)) := hconj

/-- Corollary 5.16 (2). The eigenvalues of `Matrix.circulant c` are exactly the
components of `Matrix.fft n c`. -/
theorem circulant_hasEigenvalue_iff {n : ℕ} [NeZero n] (c : Fin n → ℂ) (μ : ℂ) :
    HasEigenvalue (toLin' (circulant c)) μ ↔ ∃ i : Fin n, fft n c i = μ := by
  -- Rewrite eigenvalues as spectrum membership, then move to the diagonal Fourier model.
  rw [hasEigenvalue_iff_mem_spectrum, Matrix.spectrum_toLin']
  calc
    μ ∈ spectrum ℂ (circulant c) ↔ μ ∈ spectrum ℂ (diagonal (fft n c)) := by
      simpa using congrArg (fun s ↦ μ ∈ s) (circulantSpectrum_eq_diagonalFftSpectrum c)
    _ ↔ HasEigenvalue (toLin' (diagonal (fft n c))) μ := by
      rw [← Matrix.spectrum_toLin', hasEigenvalue_iff_mem_spectrum]
    _ ↔ ∃ i : Fin n, fft n c i = μ := by
      simpa using hasEigenvalue_toLin'_diagonal_iff (fft n c)

/-- Canonical range form of `Matrix.circulant_hasEigenvalue_iff`. -/
theorem circulant_hasEigenvalue_iff_mem_range_fft {n : ℕ} [NeZero n]
    (c : Fin n → ℂ) (μ : ℂ) :
    HasEigenvalue (toLin' (circulant c)) μ ↔ μ ∈ Set.range (fft n c) := by
  -- The set-theoretic range is exactly the existential form from the previous theorem.
  simpa [Set.mem_range] using circulant_hasEigenvalue_iff c μ

/-- Helper for Corollary 5.16: the `i`th column of `(Matrix.fourierMatrix n)ᴴ`
is an eigenvector candidate for `Matrix.circulant c` with eigenvalue
`Matrix.fft n c i`. -/
lemma circulant_mul_fourierConjTranspose_col_eq_smul {n : ℕ} [NeZero n] (c : Fin n → ℂ)
    (i : Fin n) :
    circulant c *ᵥ (((fourierMatrix n)ᴴ).col i) =
      (fft n c i) • (((fourierMatrix n)ᴴ).col i) := by
  let F : Matrix (Fin n) (Fin n) ℂ := fourierMatrix n
  let d : Fin n → ℂ := fft n c
  have hFFh : F * Fᴴ = 1 := by
    -- The Fourier matrix is unitary, so the middle `F * Fᴴ` collapses to the identity.
    exact Matrix.mem_unitaryGroup_iff.mp <| Matrix.fourierMatrix_mem_unitaryGroup n
  have hsingle :
      Pi.single i (d i * 1 : ℂ) = (d i) • Pi.single i (1 : ℂ) := by
    simpa [smul_eq_mul] using (Pi.single_smul' i (d i) (1 : ℂ))
  -- Rewrite the chosen column as a standard basis vector pushed through `Fᴴ`.
  calc
    circulant c *ᵥ (((fourierMatrix n)ᴴ).col i)
        = circulant c *ᵥ (Fᴴ *ᵥ Pi.single i (1 : ℂ)) := by
            simp [F]
    _ = (circulant c * Fᴴ) *ᵥ Pi.single i (1 : ℂ) := by
          rw [← Matrix.mulVec_mulVec]
    _ = ((Fᴴ * diagonal d * F) * Fᴴ) *ᵥ Pi.single i (1 : ℂ) := by
          rw [circulant_eq_fourierDiagonal_fft n c]
    _ = (Fᴴ * diagonal d) *ᵥ Pi.single i (1 : ℂ) := by
          simp [Matrix.mul_assoc, hFFh]
    _ = Fᴴ *ᵥ (diagonal d *ᵥ Pi.single i (1 : ℂ)) := by
          rw [← Matrix.mulVec_mulVec]
    _ = Fᴴ *ᵥ Pi.single i (d i * 1) := by
          rw [Matrix.diagonal_mulVec_single]
    _ = Fᴴ *ᵥ ((d i) • Pi.single i (1 : ℂ)) := by
          rw [hsingle]
    _ = (d i) • (Fᴴ *ᵥ Pi.single i (1 : ℂ)) := by
          rw [Matrix.mulVec_smul]
    _ = (fft n c i) • (((fourierMatrix n)ᴴ).col i) := by
          simp [F, d]

/-- Helper for Corollary 5.16: the `i`th column of `(Matrix.fourierMatrix n)ᴴ`
is nonzero. -/
lemma fourierConjTranspose_col_ne_zero {n : ℕ} [NeZero n] (i : Fin n) :
    (((fourierMatrix n)ᴴ).col i : Fin n → ℂ) ≠ 0 := by
  let F : Matrix (Fin n) (Fin n) ℂ := fourierMatrix n
  have hFFh : F * Fᴴ = 1 := by
    -- Applying `F` to a Fourier column recovers the corresponding standard basis vector.
    exact Matrix.mem_unitaryGroup_iff.mp <| Matrix.fourierMatrix_mem_unitaryGroup n
  have hcol :
      (((fourierMatrix n)ᴴ).col i : Fin n → ℂ) = Fᴴ *ᵥ Pi.single i (1 : ℂ) := by
    simpa [F] using (Matrix.mulVec_single_one (Fᴴ) i).symm
  have himage :
      F *ᵥ ((((fourierMatrix n)ᴴ).col i : Fin n → ℂ)) = Pi.single i (1 : ℂ) := by
    calc
      F *ᵥ ((((fourierMatrix n)ᴴ).col i : Fin n → ℂ))
          = F *ᵥ (Fᴴ *ᵥ Pi.single i (1 : ℂ)) := by
              rw [hcol]
      _ = Pi.single i (1 : ℂ) := by
            rw [Matrix.mulVec_mulVec, hFFh, Matrix.one_mulVec]
  intro hcol_zero
  -- A zero Fourier column would map to the zero vector, contradicting the recovered basis vector.
  have hzero : F *ᵥ ((((fourierMatrix n)ᴴ).col i : Fin n → ℂ)) = 0 := by
    simp [hcol_zero]
  have hsingle_zero : (Pi.single i (1 : ℂ) : Fin n → ℂ) = 0 := by
    exact himage.symm.trans hzero
  have hsingle_nonzero : (Pi.single i (1 : ℂ) : Fin n → ℂ) ≠ 0 :=
    Pi.single_ne_zero_iff.2 one_ne_zero
  exact hsingle_nonzero hsingle_zero

/-- Corollary 5.16 (3). The `i`th column of `(Matrix.fourierMatrix n)ᴴ` is an
eigenvector of `Matrix.circulant c` for the eigenvalue `Matrix.fft n c i`. -/
theorem circulant_hasEigenvector_fourierColumn {n : ℕ} [NeZero n] (c : Fin n → ℂ)
    (i : Fin n) :
    HasEigenvector
      (toLin' (circulant c))
      (fft n c i)
      (((fourierMatrix n)ᴴ).col i) := by
  refine ⟨?_, fourierConjTranspose_col_ne_zero (n := n) i⟩
  -- The helper computes the eigenspace relation for the chosen Fourier column.
  rw [mem_eigenspace_iff]
  simpa using circulant_mul_fourierConjTranspose_col_eq_smul (n := n) c i

end Matrix
