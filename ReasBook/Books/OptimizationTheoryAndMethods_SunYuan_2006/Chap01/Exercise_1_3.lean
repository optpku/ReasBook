/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Matrix.PosDef

open Matrix

-- Semantic recall hits verified for this item: `abs_real_inner_le_norm` is the canonical
-- Euclidean Cauchy-Schwarz statement, and `LinearMap.BilinForm.apply_sq_le_of_symm` is the
-- core bilinear-form Cauchy-Schwarz inequality behind the positive-definite matrix variant.

/-
Chapter01 Exercise 1.3

Canonical recall for Exercise 1.3 (1): the Euclidean Cauchy-Schwarz inequality on `ℝ^n` is the
mathlib theorem `abs_real_inner_le_norm`.
-/
#check abs_real_inner_le_norm

/-- Chapter01 Exercise 1.3 (2): if `A` is a real symmetric positive-definite matrix, then
`|xᵀ A y| ≤ sqrt (xᵀ A x) * sqrt (yᵀ A y)`, written on `EuclideanSpace ℝ (Fin n)` as a
`dotProduct`/`Matrix.mulVec` inequality. -/
theorem posDefMatrixCauchySchwarz {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (x y : EuclideanSpace ℝ (Fin n)) :
    |dotProduct x (A.mulVec y)| ≤
      Real.sqrt (dotProduct x (A.mulVec x)) * Real.sqrt (dotProduct y (A.mulVec y)) := by
  have hsymmBilin : A.toBilin'.IsSymm := by
    rw [Matrix.isSymm_toBilin'_iff_isSymm]
    simpa using hA.isHermitian
  have hsq := A.toBilin'.apply_sq_le_of_symm
      (fun z ↦ by
        simpa [Matrix.toBilin'_apply', Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using
          hA.toQuadraticForm'.nonneg z)
      (show LinearMap.IsSymm A.toBilin' from ⟨hsymmBilin.eq⟩)
      x y
  have hxx : 0 ≤ dotProduct x (A.mulVec x) := by
    simpa [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using hA.toQuadraticForm'.nonneg x
  have hyy : 0 ≤ dotProduct y (A.mulVec y) := by
    simpa [Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply'] using hA.toQuadraticForm'.nonneg y
  have habs_sq :
      |dotProduct x (A.mulVec y)| ^ 2 ≤ dotProduct x (A.mulVec x) * dotProduct y (A.mulVec y) := by
    simpa [Matrix.toBilin'_apply', sq_abs] using hsq
  have hsqrt :
      (Real.sqrt (dotProduct x (A.mulVec x)) * Real.sqrt (dotProduct y (A.mulVec y))) ^ 2 =
        dotProduct x (A.mulVec x) * dotProduct y (A.mulVec y) := by
    calc
      (Real.sqrt (dotProduct x (A.mulVec x)) * Real.sqrt (dotProduct y (A.mulVec y))) ^ 2 =
          (Real.sqrt (dotProduct x (A.mulVec x))) ^ 2 *
            (Real.sqrt (dotProduct y (A.mulVec y))) ^ 2 := by
        ring
      _ = dotProduct x (A.mulVec x) * dotProduct y (A.mulVec y) := by
        rw [Real.sq_sqrt hxx, Real.sq_sqrt hyy]
  exact le_of_sq_le_sq (hsqrt.symm ▸ habs_sq) (by positivity)
