/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Notation_5_2_1
public import Mathlib.LinearAlgebra.Matrix.Circulant
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6.Comparison
import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_6.Diagonalization
import Mathlib.Algebra.Group.Pi.Units

public section

/- Remark 5.17 records the algebraic FFT/ifft identities for circulant
matrix-vector products and nonsingular circulant inverses. The source
`O(n log n)` cost claim is kept informal here because the current repo does not
provide a checked asymptotic-cost API. -/

open scoped Matrix

noncomputable section

namespace Matrix

/-- Rewriting the normalized Fourier diagonalization of a circulant matrix
through the source-facing transform `Matrix.fft`. -/
theorem circulant_eq_fourierDiagonal_fft
    (n : ℕ) [NeZero n] (c : Fin n → ℂ) :
    circulant c =
      (fourierMatrix n)ᴴ * diagonal (fft n c) * fourierMatrix n := by
  have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
    exact_mod_cast Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_neZero n)
  calc
    circulant c = (Real.sqrt n : ℂ) • ((1 / Real.sqrt n : ℂ) • circulant c) := by
      rw [one_div, smul_smul, mul_inv_cancel₀ hsqrt, one_smul]
    _ = (Real.sqrt n : ℂ) • ((fourierMatrix n)ᴴ * diagonal (dft n c) * fourierMatrix n) := by
      rw [smul_circulant_eq_fourierDiagonalization]
    _ = (fourierMatrix n)ᴴ * diagonal ((Real.sqrt n : ℂ) • dft n c) * fourierMatrix n := by
      simp [Matrix.diagonal_smul, Matrix.mul_assoc]
    _ = (fourierMatrix n)ᴴ * diagonal (fft n c) * fourierMatrix n := by
      rfl

/-- Remark 5.17 (1). A circulant matrix-vector product can be written as an
`ifft` of the pointwise product of the Fourier transforms of its generator and
input vector. -/
theorem circulant_mulVec_eq_ifft_mul_fft
    (n : ℕ) [NeZero n] (c f : Fin n → ℂ) :
    circulant c *ᵥ f = ifft n (fft n c * fft n f) := by
  simpa [discreteConvolution_def, toeplitzByDiag_periodicExtension_eq_circulant] using
    (periodicExtension_discreteConvolution_eq_ifft_mul_fft n
      (WithLp.toLp 2 c) (WithLp.toLp 2 f))

/-- A circulant matrix is nonsingular exactly when its `fft` spectrum has no
zero entries. -/
theorem isUnit_circulant_iff_fft_ne_zero
    (n : ℕ) [NeZero n] (c : Fin n → ℂ) :
    IsUnit (circulant c) ↔ ∀ i : Fin n, fft n c i ≠ 0 := by
  rw [circulant_eq_fourierDiagonal_fft]
  have h_fourier : IsUnit (fourierMatrix n) := by
    exact IsUnit.of_mul_eq_one _ (fourierMatrix_mul_conjTranspose n)
  have h_fourierH : IsUnit ((fourierMatrix n)ᴴ) := by
    exact IsUnit.of_mul_eq_one _ (fourierMatrix_conjTranspose_mul n)
  simpa [h_fourier.unit_spec, h_fourierH.unit_spec] using
    (show IsUnit
        (((h_fourierH.unit : Matrix (Fin n) (Fin n) ℂ) * diagonal (fft n c)) * h_fourier.unit) ↔
          ∀ i : Fin n, fft n c i ≠ 0 from by
      rw [Units.isUnit_mul_units, Units.isUnit_units_mul, Matrix.isUnit_diagonal, Pi.isUnit_iff]
      simp [isUnit_iff_ne_zero])

/-- Remark 5.17 (2). The inverse of a nonsingular circulant matrix is obtained
by taking reciprocal Fourier coefficients inside the diagonal Fourier form. -/
theorem circulant_inv_eq_fourierDiagonal_inv_fft
    (n : ℕ) [NeZero n] (c : Fin n → ℂ) (h_nonsingular : IsUnit (circulant c)) :
    (circulant c)⁻¹ =
      (fourierMatrix n)ᴴ *
        diagonal (fun i ↦ (fft n c i)⁻¹) *
        fourierMatrix n := by
  have h_fft : ∀ i : Fin n, fft n c i ≠ 0 :=
    (isUnit_circulant_iff_fft_ne_zero n c).mp h_nonsingular
  have hdiag :
      diagonal (fft n c) * diagonal (fun i ↦ (fft n c i)⁻¹) =
        (1 : Matrix (Fin n) (Fin n) ℂ) := by
    rw [Matrix.diagonal_mul_diagonal]
    ext i j
    rw [Matrix.diagonal_apply, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      exact mul_inv_cancel₀ (h_fft i)
    · simp [hij]
  apply Matrix.inv_eq_right_inv
  calc
    circulant c *
        ((fourierMatrix n)ᴴ * diagonal (fun i ↦ (fft n c i)⁻¹) * fourierMatrix n)
        =
          ((fourierMatrix n)ᴴ * diagonal (fft n c) * fourierMatrix n) *
            ((fourierMatrix n)ᴴ * diagonal (fun i ↦ (fft n c i)⁻¹) * fourierMatrix n) := by
          rw [circulant_eq_fourierDiagonal_fft]
    _ =
        (fourierMatrix n)ᴴ *
          (diagonal (fft n c) * diagonal (fun i ↦ (fft n c i)⁻¹)) *
          fourierMatrix n := by
          calc
            ((fourierMatrix n)ᴴ * diagonal (fft n c) * fourierMatrix n) *
                ((fourierMatrix n)ᴴ * diagonal (fun i ↦ (fft n c i)⁻¹) * fourierMatrix n)
                =
                  (fourierMatrix n)ᴴ * diagonal (fft n c) *
                    (fourierMatrix n * (fourierMatrix n)ᴴ) *
                    diagonal (fun i ↦ (fft n c i)⁻¹) *
                    fourierMatrix n := by
                      simp [Matrix.mul_assoc]
            _ =
                  (fourierMatrix n)ᴴ * diagonal (fft n c) * 1 *
                    diagonal (fun i ↦ (fft n c i)⁻¹) *
                    fourierMatrix n := by
                      rw [fourierMatrix_mul_conjTranspose]
            _ =
                  (fourierMatrix n)ᴴ *
                    (diagonal (fft n c) * diagonal (fun i ↦ (fft n c i)⁻¹)) *
                    fourierMatrix n := by
                      simp [Matrix.mul_assoc]
    _ = 1 := by
          rw [hdiag]
          simp [fourierMatrix_conjTranspose_mul]

end Matrix
