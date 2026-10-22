/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_2_2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

open Matrix

-- This exercise reuses the chapter's matrix-norm owners from `Definition_1_2_2` rather than
-- duplicating local norm wrappers.

/-- A consistency-only companion to Exercise 1.1: if `A` is a nonsingular real square matrix, then
every `x : Fin n → ℝ` satisfies `v x / N A⁻¹ ≤ v (A *ᵥ x)` for every vector norm `v` and every
matrix bound `N` consistent with `v`. Without a matrix-norm hypothesis on `N`, the lower bound may
be vacuous when `N A⁻¹ = 0`. -/
theorem div_matrixBound_inv_le_vectorNorm_mulVec
    {n : ℕ} (v : (Fin n → ℝ) → ℝ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hv : IsVectorNorm v) (hCons : MatrixNormConsistent v v N)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) (x : Fin n → ℝ) :
    v x / N A⁻¹ ≤ v (A *ᵥ x) := by
  letI := hA.invertible
  have hAx : v x ≤ N A⁻¹ * v (A *ᵥ x) := by
    simpa [mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] using
      hCons.mulVec_le A⁻¹ (A *ᵥ x)
  by_cases hpos : 0 < N A⁻¹
  · exact (div_le_iff₀ hpos).2 <| by
      simpa [mul_comm] using hAx
  · have hdiv : v x / N A⁻¹ ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (hv.nonneg _) (not_lt.1 hpos)
    exact hdiv.trans (hv.nonneg _)

/-- Chapter01 Exercise 1.1: if `A` is a nonsingular real square matrix, then every
`x : Fin n → ℝ` satisfies `v x / N A⁻¹ ≤ v (A *ᵥ x)` for every vector norm `v` and every
compatible matrix norm `N`. This keeps the labeled exercise at the source-facing matrix-norm
layer, while `div_matrixBound_inv_le_vectorNorm_mulVec` records the weaker consistency-only
generalization. -/
theorem div_invMatrixNorm_le_vectorNorm_mulVec
    {n : ℕ} (v : (Fin n → ℝ) → ℝ) (N : Matrix (Fin n) (Fin n) ℝ → ℝ)
    (hv : IsVectorNorm v) (hNorm : IsMatrixNorm N) (hCons : MatrixNormConsistent v v N)
    (A : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A) (x : Fin n → ℝ) :
    v x / N A⁻¹ ≤ v (A *ᵥ x) := by
  rcases isEmpty_or_nonempty (Fin n) with hEmpty | hNonempty
  · letI := hEmpty
    exact div_matrixBound_inv_le_vectorNorm_mulVec v N hv hCons A hA x
  · letI := hNonempty
    letI := hA.invertible
    have hAx : v x ≤ N A⁻¹ * v (A *ᵥ x) := by
      simpa [mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec] using
        hCons.mulVec_le A⁻¹ (A *ᵥ x)
    have hAinv_ne_zero : A⁻¹ ≠ 0 := by
      intro hAinv_zero
      have hzero_ne_one : (0 : Matrix (Fin n) (Fin n) ℝ) ≠ 1 := by
        intro hzero_eq_one
        obtain ⟨i⟩ := hNonempty
        have : (0 : ℝ) = 1 := by
          simpa using congrFun (congrFun hzero_eq_one i) i
        norm_num at this
      apply hzero_ne_one
      calc
        (0 : Matrix (Fin n) (Fin n) ℝ) = A⁻¹ * A := by simp [hAinv_zero]
        _ = 1 := Matrix.inv_mul_of_invertible A
    have hNinv_ne_zero : N A⁻¹ ≠ 0 := by
      intro hNinv_zero
      exact hAinv_ne_zero <| (hNorm.eq_zero_iff A⁻¹).1 hNinv_zero
    have hNinv_pos : 0 < N A⁻¹ :=
      lt_of_le_of_ne (hNorm.nonneg _) (Ne.symm hNinv_ne_zero)
    exact (div_le_iff₀ hNinv_pos).2 <| by
      simpa [mul_comm] using hAx
