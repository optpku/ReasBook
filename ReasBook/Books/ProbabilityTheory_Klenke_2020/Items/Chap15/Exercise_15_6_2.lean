/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Exercise_15_6_1
import Mathlib.Analysis.Matrix.LDL

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} {d : ℕ}
variable {W : Ω → EuclideanSpace ℝ (Fin d)}
variable {μ : EuclideanSpace ℝ (Fin d)}
variable {A C : Matrix (Fin d) (Fin d) ℝ}

/-- Helper for Exercise 15.6.2: the inverse-LDL factor is lower triangular, hence block
triangular for the lower-triangular order on `Fin d`. -/
lemma ldlLowerInv_blockTriangular (hC : C.PosDef) :
    (LDL.lowerInv hC).BlockTriangular OrderDual.toDual := by
  -- Reinterpret the triangularity statement from the LDL API in block-triangular form.
  intro i j hij
  simpa using LDL.lowerInv_triangular (hS := hC) hij

/-- Helper for Exercise 15.6.2: the LDL factor `Matrix.LDL.lower hC` is lower triangular. -/
lemma ldlLower_blockTriangular (hC : C.PosDef) :
    (LDL.lower hC).BlockTriangular OrderDual.toDual := by
  -- Invert the already-triangular inverse factor to recover triangularity of `LDL.lower`.
  simpa [LDL.lower] using
    Matrix.blockTriangular_inv_of_blockTriangular
      (M := LDL.lowerInv hC) (b := OrderDual.toDual)
      (ldlLowerInv_blockTriangular hC)

/-- Helper for Exercise 15.6.2: the diagonal factor in the LDL decomposition of a positive
definite matrix is itself positive definite. -/
lemma ldlDiag_posDef (hC : C.PosDef) :
    (LDL.diag hC).PosDef := by
  -- Conjugating a positive definite matrix by an invertible matrix preserves positive definiteness.
  simpa [LDL.diag_eq_lowerInv_conj (hS := hC)] using
    hC.mul_mul_conjTranspose_same (B := LDL.lowerInv hC)
      (Matrix.vecMul_injective_of_invertible (LDL.lowerInv hC))

/-- Helper for Exercise 15.6.2: the square root of the LDL diagonal factor squares back to that
diagonal matrix. -/
lemma sqrtLdlDiag_mul_transpose_eq (hC : C.PosDef) :
    let Dsqrt : Matrix (Fin d) (Fin d) ℝ :=
      Matrix.diagonal (fun i ↦ Real.sqrt ((LDL.diag hC) i i))
    Dsqrt * Dsqrt.transpose = LDL.diag hC := by
  -- Reduce the matrix identity to diagonal entries and use positivity of the LDL diagonal.
  let Dsqrt : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt ((LDL.diag hC) i i))
  have hDiagPos : (LDL.diag hC).PosDef := ldlDiag_posDef hC
  change Dsqrt * Dsqrt.transpose = LDL.diag hC
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    exact Real.mul_self_sqrt (le_of_lt (hDiagPos.diag_pos (i := i)))
  · rw [Matrix.diagonal_apply_ne _ hij, LDL.diag, Matrix.diagonal_apply_ne _ hij]

-- Proof sketch: translating a centered multivariate Gaussian only shifts its mean.
/-- Helper for Exercise 15.6.2: adding a constant vector to a centered multivariate Gaussian
changes only the mean. -/
lemma constAdd_hasLaw_multivariateGaussian_zero
    {X : Ω → EuclideanSpace ℝ (Fin d)}
    (hX : HasLaw X (multivariateGaussian 0 C) P) :
    HasLaw (fun ω ↦ μ + X ω) (multivariateGaussian μ C) P := by
  -- Compose the centered Gaussian law with the constant-addition map.
  refine HasLaw.comp ?_ hX
  let f : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun x ↦ 0 + (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (CFC.sqrt C)) x
  refine ⟨by fun_prop, ?_⟩
  -- Unfold the measure definition once and transport by `Measure.map_map`.
  simpa [ProbabilityTheory.multivariateGaussian, f, Function.comp] using
    (Measure.map_map (μ := stdGaussian (EuclideanSpace ℝ (Fin d)))
      (g := HAdd.hAdd μ) (f := f) (measurable_const_add μ) (by fun_prop))

-- Proof sketch: apply the real-matrix Cholesky/LDL factorization to the positive definite matrix
-- `C`; over `ℝ`, positive definiteness already gives the required symmetry, and the factor can be
-- chosen lower triangular.
/-- A positive definite real matrix admits a lower triangular factor whose product with its
transpose is the matrix itself. -/
theorem exists_lowerTriangular_mul_transpose_eq_of_posDef (hC : C.PosDef) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ, A.BlockTriangular OrderDual.toDual ∧ A * A.transpose = C :=
  by
  let Dsqrt : Matrix (Fin d) (Fin d) ℝ :=
    Matrix.diagonal (fun i ↦ Real.sqrt ((LDL.diag hC) i i))
  refine ⟨LDL.lower hC * Dsqrt, ?_, ?_⟩
  · -- The product of two lower-triangular matrices is lower triangular.
    simpa [Dsqrt] using
      (ldlLower_blockTriangular hC).mul
        (Matrix.blockTriangular_diagonal
          (b := OrderDual.toDual)
          (d := fun i ↦ Real.sqrt ((LDL.diag hC) i i)))
  · -- Multiply the LDL lower factor by the square root of the diagonal factor.
    let L : Matrix (Fin d) (Fin d) ℝ := LDL.lower hC
    calc
      (L * Dsqrt) * (L * Dsqrt).transpose
          = L * (Dsqrt * Dsqrt.transpose) * L.transpose := by
              rw [Matrix.transpose_mul]
              simp [Matrix.mul_assoc]
      _ = L * LDL.diag hC * L.transpose := by
            rw [sqrtLdlDiag_mul_transpose_eq (C := C) hC]
      _ = C := by
            simpa [L] using LDL.lower_conj_diag (hS := hC)

-- Proof sketch: first choose a lower triangular factor `A` with `A Aᵀ = C` from
-- `exists_lowerTriangular_mul_transpose_eq_of_posDef`. Since
-- `multivariateGaussian 0 1 = stdGaussian (EuclideanSpace ℝ (Fin d))`, the Gaussian-law part is
-- the `C = 1` instance of `hasLaw_matrix_image_of_hasLaw_multivariateGaussian` from
-- Exercise 15.6.1.
/-- Exercise 15.6.2: a positive definite real covariance matrix `C` admits a lower triangular factor
`A`, and for a standard Gaussian vector `W` the affine transform `ω ↦ μ + A (W ω)` has law
`N_{μ,C}`. -/
theorem exists_lowerTriangular_factor_hasLaw_multivariateGaussian_of_hasLaw_stdGaussian
    (hC : C.PosDef) (hW : HasLaw W (stdGaussian (EuclideanSpace ℝ (Fin d))) P) :
    ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.BlockTriangular OrderDual.toDual ∧
      A * A.transpose = C ∧
      HasLaw (fun ω ↦ μ + Matrix.toEuclideanLin A (W ω))
        (multivariateGaussian μ C) P :=
  by
  obtain ⟨A, hAtri, hACov⟩ := exists_lowerTriangular_mul_transpose_eq_of_posDef (C := C) hC
  have hW' : HasLaw W (multivariateGaussian 0 (1 : Matrix (Fin d) (Fin d) ℝ)) P := by
    simpa [ProbabilityTheory.multivariateGaussian_zero_one] using hW
  have hOne : (1 : Matrix (Fin d) (Fin d) ℝ).PosSemidef := by
    simpa using Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix (Fin d) (Fin d) ℝ)
  have hLinear :
      HasLaw (fun ω ↦ Matrix.toEuclideanLin A (W ω)) (multivariateGaussian 0 C) P := by
    -- Exercise 15.6.1 gives the law of the centered linear image `A W`.
    simpa [hACov, Matrix.mul_assoc] using
      hasLaw_matrix_image_of_hasLaw_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ (Fin d)))
        (C := (1 : Matrix (Fin d) (Fin d) ℝ))
        (hC := hOne) (A := A) hW'
  refine ⟨A, hAtri, hACov, ?_⟩
  -- Translate the centered Gaussian law by `μ` to obtain the required affine law.
  simpa using (constAdd_hasLaw_multivariateGaussian_zero (P := P) (μ := μ) (C := C) hLinear)
