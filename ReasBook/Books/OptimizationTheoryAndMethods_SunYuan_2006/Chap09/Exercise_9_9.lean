/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

noncomputable section

-- Semantic recall: `lean_leansearch` did not surface a repo-local owner for the QR null-space
-- block `Q₂` from `(9.3.40)`. Since this exercise only asks for two specializations of the
-- generic null-space correction formula, the file keeps that correction explicit and states the
-- two resulting choices directly.

variable {m k : ℕ}

local notation "Ambient" => Sum (Fin m) (Fin k)
local notation "ConstraintMatrix" => Matrix Ambient (Fin m) ℝ
local notation "ChoiceMatrix" => Matrix Ambient (Fin k) ℝ

/-- The generic null-space correction from `(9.3.42)`, sending a seed matrix `V` to
`(I - U Aᵀ) V`. -/
def nullSpaceCorrection (U : Matrix Ambient (Fin m) ℝ) (A : ConstraintMatrix)
    (V : ChoiceMatrix) : ChoiceMatrix :=
  (1 - U * A.transpose) * V

#print axioms nullSpaceCorrection

/-- Unfolding `nullSpaceCorrection U A V` gives the source matrix formula
`(I - U Aᵀ) V`. -/
theorem nullSpaceCorrection_eq (U : Matrix Ambient (Fin m) ℝ) (A : ConstraintMatrix)
    (V : ChoiceMatrix) :
    nullSpaceCorrection U A V = (1 - U * A.transpose) * V := rfl

/-- Chapter09 Exercise 9.9 (1): for the block partition `Aᵀ = [B  N]`, inserting the seed
matrix `[[0], [I_(n-m)]]` into the generic construction `(9.3.42)` recovers the standard choice
`V = [[-B⁻¹ N], [I_(n-m)]]` from `(9.3.37)`-`(9.3.38)`. -/
theorem chapter09Exercise99_blockSeed_recovers_standardChoice
    (B : Matrix (Fin m) (Fin m) ℝ) (N : Matrix (Fin m) (Fin k) ℝ) :
    nullSpaceCorrection
        (Matrix.fromRows B⁻¹ (0 : Matrix (Fin k) (Fin m) ℝ))
        (Matrix.fromCols B N)ᵀ
        (Matrix.fromRows (0 : Matrix (Fin m) (Fin k) ℝ) (1 : Matrix (Fin k) (Fin k) ℝ)) =
      Matrix.fromRows (-(B⁻¹ * N)) (1 : Matrix (Fin k) (Fin k) ℝ) := by
  -- Unfold the generic correction and remove the double transpose on the block matrix.
  rw [nullSpaceCorrection_eq]
  simp_rw [Matrix.transpose_transpose]
  -- Compute the correction factor `U * Aᵀ` in block form.
  have hProduct :
      Matrix.fromRows B⁻¹ (0 : Matrix (Fin k) (Fin m) ℝ) * Matrix.fromCols B N =
        Matrix.fromBlocks (B⁻¹ * B) (B⁻¹ * N) 0 0 := by
    simpa [Matrix.zero_mul] using
      (Matrix.fromRows_mul_fromCols B⁻¹ (0 : Matrix (Fin k) (Fin m) ℝ) B N)
  -- Rewrite `I - U * Aᵀ` in the same block normal form as the correction term.
  have hCorrection :
      (1 : Matrix Ambient Ambient ℝ) -
          Matrix.fromRows B⁻¹ (0 : Matrix (Fin k) (Fin m) ℝ) * Matrix.fromCols B N =
        Matrix.fromBlocks (1 - B⁻¹ * B) (-(B⁻¹ * N)) 0
          (1 : Matrix (Fin k) (Fin k) ℝ) := by
    rw [sub_eq_add_neg, hProduct, ← Matrix.fromBlocks_one, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add]
    simp [sub_eq_add_neg]
  -- Multiply the block correction by the seed `[[0], [I]]`; the zero top block kills
  -- the unwanted `1 - B⁻¹ * B` factor, leaving the standard choice.
  calc
    ((1 : Matrix Ambient Ambient ℝ) -
        Matrix.fromRows B⁻¹ (0 : Matrix (Fin k) (Fin m) ℝ) * Matrix.fromCols B N) *
        Matrix.fromRows (0 : Matrix (Fin m) (Fin k) ℝ) (1 : Matrix (Fin k) (Fin k) ℝ) =
      Matrix.fromBlocks (1 - B⁻¹ * B) (-(B⁻¹ * N)) 0
          (1 : Matrix (Fin k) (Fin k) ℝ) *
        Matrix.fromRows (0 : Matrix (Fin m) (Fin k) ℝ) (1 : Matrix (Fin k) (Fin k) ℝ) := by
          rw [hCorrection]
    _ =
      Matrix.fromRows
        (((1 - B⁻¹ * B) * (0 : Matrix (Fin m) (Fin k) ℝ)) +
          (-(B⁻¹ * N)) * (1 : Matrix (Fin k) (Fin k) ℝ))
        (((0 : Matrix (Fin k) (Fin m) ℝ) * (0 : Matrix (Fin m) (Fin k) ℝ)) +
          (1 : Matrix (Fin k) (Fin k) ℝ) * (1 : Matrix (Fin k) (Fin k) ℝ)) := by
            simpa using
              (Matrix.fromBlocks_mul_fromRows
                (0 : Matrix (Fin m) (Fin k) ℝ)
                (1 : Matrix (Fin k) (Fin k) ℝ)
                (1 - B⁻¹ * B)
                (-(B⁻¹ * N))
                (0 : Matrix (Fin k) (Fin m) ℝ)
                (1 : Matrix (Fin k) (Fin k) ℝ))
    _ = Matrix.fromRows (-(B⁻¹ * N)) (1 : Matrix (Fin k) (Fin k) ℝ) := by
      simp

/-- Chapter09 Exercise 9.9 (2): for the QR-based choice `(9.3.40)`, let `U9340` and `Q₂9340`
be the specific matrices from that setup. Then substituting `V = Q₂9340` into the generic
construction `(9.3.42)` recovers the concrete `(9.3.40)` choice directly, namely `Q₂9340`;
this fixed-point identity uses exactly the null-block relation `A9340ᵀ Q₂9340 = 0`. -/
theorem chapter09Exercise99_q2_recovers_qrChoice
    (A9340 : ConstraintMatrix) (U9340 : Matrix Ambient (Fin m) ℝ)
    (Q₂9340 : ChoiceMatrix)
    (hQ₂NullBlock9340 : A9340.transpose * Q₂9340 = 0) :
    nullSpaceCorrection U9340 A9340 Q₂9340 = Q₂9340 := by
  rw [nullSpaceCorrection_eq]
  have hCorrectionTerm : (U9340 * A9340.transpose) * Q₂9340 = 0 := by
    rw [Matrix.mul_assoc, hQ₂NullBlock9340, Matrix.mul_zero]
  calc
    ((1 : Matrix Ambient Ambient ℝ) - U9340 * A9340.transpose) * Q₂9340 =
        (1 : Matrix Ambient Ambient ℝ) * Q₂9340 - (U9340 * A9340.transpose) * Q₂9340 := by
          simpa using
            Matrix.sub_mul (1 : Matrix Ambient Ambient ℝ) (U9340 * A9340.transpose) Q₂9340
    _ = ((1 : Matrix Ambient Ambient ℝ) * Q₂9340) - 0 := by
      rw [hCorrectionTerm]
    _ = Q₂9340 := by
      rw [Matrix.one_mul, sub_zero]
