/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_1_1
public import Mathlib.LinearAlgebra.Matrix.Bilinear

public section

open scoped BigOperators

noncomputable section

namespace Matrix

/-- The normalized two-dimensional discrete Fourier transform on
`Matrix (Fin n_x) (Fin n_y) ℂ` as a `ℂ`-linear map. -/
abbrev dft2D (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] :
    Matrix (Fin n_x) (Fin n_y) ℂ →ₗ[ℂ] Matrix (Fin n_x) (Fin n_y) ℂ :=
  (mulLeftLinearMap (Fin n_y) ℂ (Matrix.fourierMatrix n_x)).comp
    (mulRightLinearMap (Fin n_x) ℂ ((Matrix.fourierMatrix n_y)ᵀ))

/-- The forward two-dimensional Fourier transform is left multiplication by
`Matrix.fourierMatrix n_x` and right multiplication by `(Matrix.fourierMatrix n_y)ᵀ`. -/
theorem dft2D_def (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) :
    Matrix.dft2D n_x n_y f =
      Matrix.fourierMatrix n_x * f * (Matrix.fourierMatrix n_y)ᵀ := by
  -- Expand the linear map and reassociate the matrix product.
  simp [Matrix.dft2D, Matrix.mul_assoc]

/-- Helper for Definition 5.7: after canceling the normalization factors in the
two forward Fourier kernels, the remaining phase is the textbook exponential
from `(5.24)`. -/
lemma dft2DKernel_mul_eq_exp (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (i i' : Fin n_x) (j j' : Fin n_y) (z : ℂ) :
    ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) *
        (Matrix.fourierMatrix n_x i i' * z * Matrix.fourierMatrix n_y j j') =
      z *
        Complex.exp
          (-Complex.I * 2 * Real.pi *
            ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
              (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
  have hnx : (n_x : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n_x).ne'
  have hny : (n_y : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n_y).ne'
  have hsx : (Real.sqrt n_x : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_x by exact_mod_cast Nat.pos_of_neZero n_x))
  have hsy : (Real.sqrt n_y : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_y by exact_mod_cast Nat.pos_of_neZero n_y))
  have hexp :
      ((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x) +
          ((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y) =
        -Complex.I * 2 * Real.pi *
          ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y)) := by
    field_simp [hnx, hny]
    ring
  have hphase :
      Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x)) *
          Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y)) =
        Complex.exp
          (-Complex.I * 2 * Real.pi *
            ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
    rw [← Complex.exp_add, hexp]
  calc
    ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) *
        (Matrix.fourierMatrix n_x i i' * z * Matrix.fourierMatrix n_y j j')
      =
        z *
          (Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_x)) *
            Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (-Complex.I * 2 * Real.pi / n_y))) := by
          rw [Matrix.fourierMatrix_apply, Matrix.fourierMatrix_apply]
          rw [Matrix.fourierRoot_eq_exp, Matrix.fourierRoot_eq_exp]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
          field_simp [hsx, hsy]
          have hx :
              Complex.exp
                  (-(((i : ℕ) * (i' : ℕ) : ℂ) * Complex.I * Real.pi * (n_x : ℂ)⁻¹ * 2)) =
                Complex.exp
                  (-(Complex.I * Real.pi * (n_x : ℂ)⁻¹ * ((i : ℕ) * (i' : ℕ) : ℂ) * 2)) := by
            congr 1
            ring
          have hy :
              Complex.exp
                  (-(((j : ℕ) * (j' : ℕ) : ℂ) * Complex.I * Real.pi * (n_y : ℂ)⁻¹ * 2)) =
                Complex.exp
                  (-(Complex.I * Real.pi * (n_y : ℂ)⁻¹ * ((j : ℕ) * (j' : ℕ) : ℂ) * 2)) := by
            congr 1
            ring
          have hxy := congrArg₂ (fun u v : ℂ => z * (u * v)) hx hy
          simp [mul_assoc, mul_left_comm, mul_comm]
    _ =
        z *
          Complex.exp
            (-Complex.I * 2 * Real.pi *
              ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
          exact congrArg (fun w : ℂ => z * w) hphase

/-- The normalized forward two-dimensional Fourier transform has the textbook
double-sum exponential coordinate formula after expanding the normalized
Fourier-matrix kernels. -/
theorem dft2D_apply_exp (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (f : Matrix (Fin n_x) (Fin n_y) ℂ) (i : Fin n_x) (j : Fin n_y) :
    ((Real.sqrt n_x : ℂ) * Real.sqrt n_y) * Matrix.dft2D n_x n_y f i j =
      ∑ i' : Fin n_x, ∑ j' : Fin n_y,
        f i' j' *
          Complex.exp
            (-Complex.I * 2 * Real.pi *
              ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
  have hentries :
      Matrix.dft2D n_x n_y f i j =
        ∑ i' : Fin n_x, ∑ j' : Fin n_y,
          Matrix.fourierMatrix n_x i i' * f i' j' * Matrix.fourierMatrix n_y j j' := by
    rw [dft2D_def]
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  -- Expand the two-sided matrix product into the source double sum.
  rw [hentries]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  -- Each summand is exactly the normalized forward kernel from `(5.24)`.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    dft2DKernel_mul_eq_exp n_x n_y i i' j j' (f i' j')

/-- The inverse normalized two-dimensional discrete Fourier transform on
`Matrix (Fin n_x) (Fin n_y) ℂ` as a `ℂ`-linear map. -/
abbrev invDFT2D (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y] :
    Matrix (Fin n_x) (Fin n_y) ℂ →ₗ[ℂ] Matrix (Fin n_x) (Fin n_y) ℂ :=
  (mulLeftLinearMap (Fin n_y) ℂ ((Matrix.fourierMatrix n_x)ᴴ)).comp
    (mulRightLinearMap (Fin n_x) ℂ (((Matrix.fourierMatrix n_y)ᴴ)ᵀ))

/-- The inverse two-dimensional Fourier transform is left multiplication by
`(Matrix.fourierMatrix n_x)ᴴ` and right multiplication by `((Matrix.fourierMatrix n_y)ᴴ)ᵀ`. -/
theorem invDFT2D_def (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : Matrix (Fin n_x) (Fin n_y) ℂ) :
    Matrix.invDFT2D n_x n_y g =
      (Matrix.fourierMatrix n_x)ᴴ * g * ((Matrix.fourierMatrix n_y)ᴴ)ᵀ := by
  -- Expand the linear map and reassociate the matrix product.
  simp [Matrix.invDFT2D, Matrix.mul_assoc]

/-- Helper for Definition 5.7: after expanding the conjugated Fourier kernels
and collecting the normalization factors, the inverse 2D phase is the textbook
positive-sign exponential. -/
lemma invDFT2DKernel_mul_eq_exp (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (i i' : Fin n_x) (j j' : Fin n_y) (z : ℂ) :
    (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) *
        (((Matrix.fourierMatrix n_x)ᴴ i i') * z * ((Matrix.fourierMatrix n_y)ᴴ j j')) =
      (n_x * n_y : ℂ)⁻¹ *
        (z *
          Complex.exp
            (Complex.I * 2 * Real.pi *
              ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                (((j : ℕ) * (j' : ℕ) : ℂ) / n_y)))) := by
  have hnx : (n_x : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n_x).ne'
  have hny : (n_y : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.pos_of_neZero n_y).ne'
  have hsx : (Real.sqrt n_x : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_x by exact_mod_cast Nat.pos_of_neZero n_x))
  have hsy : (Real.sqrt n_y : ℂ) ≠ 0 := by
    simpa using
      (Real.sqrt_ne_zero'.2 (show (0 : ℝ) < n_y by exact_mod_cast Nat.pos_of_neZero n_y))
  have hsx_sq : ((Real.sqrt n_x : ℂ) * Real.sqrt n_x) = n_x := by
    exact_mod_cast (Real.mul_self_sqrt (show (0 : ℝ) ≤ n_x by exact_mod_cast Nat.zero_le n_x))
  have hsy_sq : ((Real.sqrt n_y : ℂ) * Real.sqrt n_y) = n_y := by
    exact_mod_cast (Real.mul_self_sqrt (show (0 : ℝ) ≤ n_y by exact_mod_cast Nat.zero_le n_y))
  have hexp :
      ((i : ℕ) * (i' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_x) +
          ((j : ℕ) * (j' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_y) =
        Complex.I * 2 * Real.pi *
          ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y)) := by
    field_simp [hnx, hny]
  have hphase :
      Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_x)) *
          Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_y)) =
        Complex.exp
          (Complex.I * 2 * Real.pi *
            ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
    rw [← Complex.exp_add, hexp]
  have hstar_exp (x : ℂ) :
      (starRingEnd ℂ) (Complex.exp x) = Complex.exp ((starRingEnd ℂ) x) := by
    exact (Complex.exp_conj x).symm
  have htwo : ((starRingEnd ℂ) 2 : ℂ) = 2 := by
    change star (2 : ℂ) = 2
    simp
  calc
    (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) *
        (((Matrix.fourierMatrix n_x)ᴴ i i') * z * ((Matrix.fourierMatrix n_y)ᴴ j j'))
      =
        (((Real.sqrt n_x : ℂ) * Real.sqrt n_x) *
          ((Real.sqrt n_y : ℂ) * Real.sqrt n_y))⁻¹ *
          (z *
            (Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_x)) *
              Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_y)))) := by
          simp only [conjTranspose_apply, RCLike.star_def]
          rw [Matrix.fourierMatrix_apply, Matrix.fourierMatrix_apply]
          rw [Matrix.fourierRoot_eq_exp, Matrix.fourierRoot_eq_exp]
          rw [map_div₀, map_div₀]
          simp only [map_pow]
          rw [hstar_exp, hstar_exp]
          simp only [_root_.mul_inv_rev, neg_mul, map_div₀, map_neg, map_mul, Complex.conj_I,
            Complex.conj_ofReal, neg_neg, map_natCast]
          rw [div_eq_mul_inv, div_eq_mul_inv]
          rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
          field_simp [hsx, hsy]
          simp [htwo]
          ring_nf
    _ =
        (n_x * n_y : ℂ)⁻¹ *
          (z *
            (Complex.exp (((i : ℕ) * (i' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_x)) *
              Complex.exp (((j : ℕ) * (j' : ℕ) : ℂ) * (Complex.I * 2 * Real.pi / n_y)))) := by
          rw [hsx_sq, hsy_sq]
    _ =
        (n_x * n_y : ℂ)⁻¹ *
          (z *
            Complex.exp
              (Complex.I * 2 * Real.pi *
                ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) + (((j : ℕ) * (j' : ℕ) : ℂ) / n_y)))) := by
          exact congrArg (fun w : ℂ => (n_x * n_y : ℂ)⁻¹ * (z * w)) hphase

/-- The normalized inverse two-dimensional Fourier transform has the textbook
double-sum exponential coordinate formula after expanding the conjugated
Fourier-matrix kernels. -/
theorem invDFT2D_apply_exp (n_x n_y : ℕ) [NeZero n_x] [NeZero n_y]
    (g : Matrix (Fin n_x) (Fin n_y) ℂ) (i : Fin n_x) (j : Fin n_y) :
    (((Real.sqrt n_x : ℂ) * Real.sqrt n_y)⁻¹) * Matrix.invDFT2D n_x n_y g i j =
      (n_x * n_y : ℂ)⁻¹ *
        ∑ i' : Fin n_x, ∑ j' : Fin n_y,
          g i' j' *
            Complex.exp
              (Complex.I * 2 * Real.pi *
                ((((i : ℕ) * (i' : ℕ) : ℂ) / n_x) +
                  (((j : ℕ) * (j' : ℕ) : ℂ) / n_y))) := by
  have hentries :
      Matrix.invDFT2D n_x n_y g i j =
        ∑ i' : Fin n_x, ∑ j' : Fin n_y,
          ((Matrix.fourierMatrix n_x)ᴴ) i i' * g i' j' * ((Matrix.fourierMatrix n_y)ᴴ) j j' := by
    rw [invDFT2D_def]
    simp_rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
  -- Expand the two-sided matrix product into the source double sum.
  rw [hentries]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i' _ ↦ ?_
  refine Finset.sum_congr rfl fun j' _ ↦ ?_
  -- Each summand is exactly the normalized inverse kernel with positive phase.
  simpa [mul_assoc, mul_left_comm, mul_comm] using
    invDFT2DKernel_mul_eq_exp n_x n_y i i' j j' (g i' j')

end Matrix
