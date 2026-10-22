/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

-- Semantic recall: `lean_leansearch` points to `Matrix.add_mul_mul_inv_eq_sub` as the
-- canonical Woodbury owner theorem. The rank-one Sherman-Morrison formula below is the
-- source-facing `m = Fin 1`, `C = 1` specialization, while the full Woodbury formula is
-- recalled directly from the canonical `Matrix` theorem surface.

universe u v

/-- Chapter01 Exercise 1.6 (1): the Sherman-Morrison formula `(1.2.67)` as the
`m = Fin 1`, `C = 1` specialization of the Woodbury identity. -/
theorem shermanMorrisonFormula
    {n : Type u} [Fintype n] [DecidableEq n] {α : Type v} [CommRing α]
    (A : Matrix n n α) (U : Matrix n (Fin 1) α) (V : Matrix (Fin 1) n α)
    (hA : IsUnit A)
    (hRankOne : IsUnit ((1 : Matrix (Fin 1) (Fin 1) α) + V * A⁻¹ * U)) :
    (A + U * V)⁻¹ =
      A⁻¹ - A⁻¹ * U * ((1 : Matrix (Fin 1) (Fin 1) α) + V * A⁻¹ * U)⁻¹ * V * A⁻¹ := by
  have hRankOne' : IsUnit ((1 : Matrix (Fin 1) (Fin 1) α)⁻¹ + V * A⁻¹ * U) := by
    simpa using hRankOne
  simpa using
    Matrix.add_mul_mul_inv_eq_sub A U (1 : Matrix (Fin 1) (Fin 1) α) V hA isUnit_one hRankOne'

/- Chapter01 Exercise 1.6 (2): the Sherman-Morrison-Woodbury formula `(1.2.68)` is exactly the
canonical Woodbury identity already provided by `Matrix.add_mul_mul_inv_eq_sub`. -/
#check Matrix.add_mul_mul_inv_eq_sub
