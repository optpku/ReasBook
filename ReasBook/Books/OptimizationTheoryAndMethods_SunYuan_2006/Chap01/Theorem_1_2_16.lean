/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

universe u

open scoped Matrix

-- Semantic recall: `Matrix.add_mul_mul_inv_eq_sub` specializes to the formula below
-- with `C = 1` and `V = Vᴴ`.

/-- Chapter01 Theorem 1.2.16 (1): if `A` is nonsingular and
`1 + Vᴴ * A⁻¹ * U` is invertible, then `A + U * Vᴴ` is invertible. -/
theorem shermanMorrisonWoodbury_isUnit
    {n m : ℕ} {α : Type u} [CommRing α] [Star α]
    (A : Matrix (Fin n) (Fin n) α)
    (U V : Matrix (Fin n) (Fin m) α)
    (hA : IsUnit A) (hSchur : IsUnit (1 + Vᴴ * A⁻¹ * U)) :
    IsUnit (A + U * Vᴴ) := by
  letI : Invertible A := hA.unit.invertible
  letI : Invertible (1 : Matrix (Fin m) (Fin m) α) := isUnit_one.unit.invertible
  have hSchur' : IsUnit (⅟(1 : Matrix (Fin m) (Fin m) α) + Vᴴ * ⅟A * U) := by
    simpa [Matrix.invOf_eq_nonsing_inv] using hSchur
  letI : Invertible (⅟(1 : Matrix (Fin m) (Fin m) α) + Vᴴ * ⅟A * U) :=
    hSchur'.unit.invertible
  letI := Matrix.invertibleAddMulMul A U (1 : Matrix (Fin m) (Fin m) α) Vᴴ
  simpa using isUnit_of_invertible (A + U * (1 : Matrix (Fin m) (Fin m) α) * Vᴴ)

/-- Chapter01 Theorem 1.2.16 (2): under the same hypotheses,
`(A + U * Vᴴ)⁻¹ = A⁻¹ - A⁻¹ * U * (1 + Vᴴ * A⁻¹ * U)⁻¹ * Vᴴ * A⁻¹`. -/
theorem shermanMorrisonWoodbury_inv_eq
    {n m : ℕ} {α : Type u} [CommRing α] [Star α]
    (A : Matrix (Fin n) (Fin n) α)
    (U V : Matrix (Fin n) (Fin m) α)
    (hA : IsUnit A) (hSchur : IsUnit (1 + Vᴴ * A⁻¹ * U)) :
    (A + U * Vᴴ)⁻¹ = A⁻¹ - A⁻¹ * U * (1 + Vᴴ * A⁻¹ * U)⁻¹ * Vᴴ * A⁻¹ := by
  have hSchur' : IsUnit ((1 : Matrix (Fin m) (Fin m) α)⁻¹ + Vᴴ * A⁻¹ * U) := by
    simpa using hSchur
  simpa using Matrix.add_mul_mul_inv_eq_sub A U (1 : Matrix (Fin m) (Fin m) α) Vᴴ
    hA isUnit_one hSchur'
