/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1.FourierMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.Fourier.ZMod
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.UnitaryGroup

public section

open scoped Matrix BigOperators

noncomputable section

namespace Matrix

/-- The normalized discrete Fourier transform on `Fin n → ℂ` as a linear map. -/
abbrev dft (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.mulVecLin (Matrix.fourierMatrix n)

/-- Helper for Definition 5.1: the normalized discrete Fourier transform has the coordinate
formula `(Matrix.dft n f) i = ∑ j, Matrix.fourierMatrix n i j * f j`. -/
theorem dft_apply (n : ℕ) [NeZero n] (f : Fin n → ℂ) (i : Fin n) :
    Matrix.dft n f i = ∑ j : Fin n, Matrix.fourierMatrix n i j * f j := by
  simpa [Matrix.dft] using Matrix.mulVec_apply_eq_sum (Matrix.fourierMatrix n) f i

/- Definition 5.1 (2): the Chapter 5 normalized Fourier matrix is the existing owner
`Matrix.fourierMatrix`, with entrywise formula `Matrix.fourierMatrix_apply` and source
exponential description `Matrix.fourierRoot_eq_exp`. -/

/-- Helper for Definition 5.1: the DFT coordinates satisfy the textbook exponential sum formula. -/
theorem dft_apply_exp (n : ℕ) [NeZero n] (f : Fin n → ℂ) (i : Fin n) :
    Matrix.dft n f i =
      ∑ j : Fin n,
        (Complex.exp (-Complex.I * 2 * Real.pi / n)) ^ ((i : ℕ) * (j : ℕ)) / Real.sqrt n * f j := by
  -- Rewrite the Fourier-matrix entries using the imported exponential formula for the root.
  simpa [Matrix.fourierMatrix_apply, Matrix.fourierRoot_eq_exp] using Matrix.dft_apply n f i

/-- The inverse discrete Fourier transform on `Fin n → ℂ` as a linear map. -/
abbrev invDFT (n : ℕ) [NeZero n] : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
  Matrix.mulVecLin ((Matrix.fourierMatrix n)ᴴ)

/-- Helper for Definition 5.1: the inverse discrete Fourier transform has the coordinate
formula `(Matrix.invDFT n g) i = ∑ j, ((Matrix.fourierMatrix n)ᴴ) i j * g j`. -/
theorem invDFT_apply (n : ℕ) [NeZero n] (g : Fin n → ℂ) (i : Fin n) :
    Matrix.invDFT n g i = ∑ j : Fin n, ((Matrix.fourierMatrix n)ᴴ) i j * g j := by
  simpa [Matrix.invDFT] using Matrix.mulVec_apply_eq_sum ((Matrix.fourierMatrix n)ᴴ) g i

/-- Helper for Definition 5.1: after expanding the conjugated Fourier kernel
and collecting the normalization factors, the inverse DFT phase is the
textbook positive-sign exponential. -/
lemma invDFTKernel_mul_eq_exp (n : ℕ) [NeZero n] (i j : Fin n) (z : ℂ) :
    ((Real.sqrt n : ℂ)⁻¹) * (((Matrix.fourierMatrix n)ᴴ i j) * z) =
      (n : ℂ)⁻¹ *
        (z * Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n))) := by
  have hn : (n : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n).ne'
  have hsqrt : (Real.sqrt n : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n by exact_mod_cast Nat.pos_of_neZero n))
  have hsqrt_sq : ((Real.sqrt n : ℂ) * Real.sqrt n) = n := by
    exact_mod_cast (Real.mul_self_sqrt (show (0 : ℝ) ≤ n by exact_mod_cast Nat.zero_le n))
  have hexp :
      (((i : ℕ) * (j : ℕ) : ℂ)) * (Complex.I * 2 * Real.pi / n) =
        Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n) := by
    field_simp [hn]
  have hstar_exp (x : ℂ) :
      (starRingEnd ℂ) (Complex.exp x) = Complex.exp ((starRingEnd ℂ) x) := by
    exact (Complex.exp_conj (x := x)).symm
  have htwo : ((starRingEnd ℂ) 2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  calc
    ((Real.sqrt n : ℂ)⁻¹) * (((Matrix.fourierMatrix n)ᴴ i j) * z)
      = (((Real.sqrt n : ℂ) * Real.sqrt n)⁻¹) *
          (Complex.exp ((((i : ℕ) * (j : ℕ) : ℂ)) * (Complex.I * 2 * Real.pi / n)) * z) := by
            simp only [conjTranspose_apply, RCLike.star_def]
            rw [Matrix.fourierMatrix_apply, Matrix.fourierRoot_eq_exp, map_div₀]
            simp only [map_pow]
            rw [hstar_exp]
            simp only [_root_.mul_inv_rev, neg_mul, map_div₀, map_neg, map_mul, Complex.conj_I,
              Complex.conj_ofReal, neg_neg, map_natCast]
            rw [div_eq_mul_inv, ← Complex.exp_nat_mul]
            field_simp [hsqrt]
            simp [htwo, mul_assoc, mul_left_comm, mul_comm]
    _ = (n : ℂ)⁻¹ *
          (Complex.exp ((((i : ℕ) * (j : ℕ) : ℂ)) * (Complex.I * 2 * Real.pi / n)) * z) := by
            rw [hsqrt_sq]
    _ = (n : ℂ)⁻¹ *
          (Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) * z) := by
            rw [hexp]
    _ = (n : ℂ)⁻¹ *
          (z * Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n))) := by
            simp [mul_left_comm, mul_comm]

/-- Helper for Definition 5.1: the normalized inverse DFT has the textbook
positive-sign exponential coordinate formula. -/
theorem invDFT_apply_exp (n : ℕ) [NeZero n] (g : Fin n → ℂ) (i : Fin n) :
    ((Real.sqrt n : ℂ)⁻¹) * Matrix.invDFT n g i =
      (n : ℂ)⁻¹ *
        ∑ j : Fin n, g j *
          Complex.exp (Complex.I * 2 * Real.pi * (((i : ℕ) * (j : ℕ) : ℂ) / n)) := by
  rw [Matrix.invDFT_apply]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using invDFTKernel_mul_eq_exp n i j (g j)

/-- Definition 5.1 (4): the Chapter 5 Fourier matrix satisfies the unitary identity
`(Matrix.fourierMatrix n)ᴴ * Matrix.fourierMatrix n = 1`. -/
theorem fourierMatrix_conjTranspose_mul (n : ℕ) [NeZero n] :
    (Matrix.fourierMatrix n)ᴴ * Matrix.fourierMatrix n = 1 :=
  Matrix.mem_unitaryGroup_iff'.mp <| Matrix.fourierMatrix_mem_unitaryGroup n

end Matrix
