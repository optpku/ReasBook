/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

universe u v

open Matrix
open scoped Matrix

-- Semantic recall: `Matrix.add_mul_mul_inv_eq_sub` is the Woodbury identity in mathlib.
-- This item keeps the source-facing vector form and derives it from that owner theorem.

section

variable {n : Type u} [Fintype n] [DecidableEq n]
variable {α : Type v} [Field α]

private theorem rankOneUpdate_schurEntry
    (A : Matrix n n α) (u v : n → α) :
    (Matrix.replicateRow Unit v * A⁻¹ * Matrix.replicateCol Unit u) () () =
      v ⬝ᵥ (A⁻¹ *ᵥ u) := by
  simp [Matrix.mul_apply, dotProduct]
  simpa [Matrix.vecMul, dotProduct] using (Matrix.dotProduct_mulVec v A⁻¹ u).symm

private theorem rankOneUpdate_schur_isUnit
    (A : Matrix n n α) (u v : n → α)
    (hScalar : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    IsUnit
      ((1 : Matrix Unit Unit α)⁻¹
        + Matrix.replicateRow Unit v * A⁻¹ * Matrix.replicateCol Unit u) := by
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_unique]
  simp only [Matrix.one_apply_eq, inv_one, add_apply]
  rw [rankOneUpdate_schurEntry A u v]
  exact isUnit_iff_ne_zero.mpr hScalar

private theorem rankOneUpdate_correction_eq
    (A : Matrix n n α) (u v : n → α) :
    A⁻¹ * Matrix.replicateCol Unit u *
        Matrix.diagonal (fun _ : Unit ↦ (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹) *
        Matrix.replicateRow Unit v * A⁻¹ =
      (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • Matrix.vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  let D : Matrix Unit Unit α :=
    Matrix.diagonal (fun _ : Unit ↦ (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹)
  have hcol : A⁻¹ * Matrix.replicateCol Unit u = Matrix.replicateCol Unit (A⁻¹ *ᵥ u) := by
    simpa using (show
      Matrix.replicateCol Unit (A⁻¹ *ᵥ u) = A⁻¹ * Matrix.replicateCol Unit u from
        Matrix.replicateCol_mulVec A⁻¹ u).symm
  have hrow : Matrix.replicateRow Unit v * A⁻¹ = Matrix.replicateRow Unit (v ᵥ* A⁻¹) := by
    simpa using (show
      Matrix.replicateRow Unit (v ᵥ* A⁻¹) = Matrix.replicateRow Unit v * A⁻¹ from
        Matrix.replicateRow_vecMul A⁻¹ v).symm
  calc
    A⁻¹ * Matrix.replicateCol Unit u * D * Matrix.replicateRow Unit v * A⁻¹ =
        (A⁻¹ * Matrix.replicateCol Unit u * D) * (Matrix.replicateRow Unit v * A⁻¹) := by
          exact Matrix.mul_assoc _ _ _
    _ = (Matrix.replicateCol Unit (A⁻¹ *ᵥ u) * D) * Matrix.replicateRow Unit (v ᵥ* A⁻¹) := by
          rw [hcol, hrow]
    _ = (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • Matrix.vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
          ext i j
          simp [D, Matrix.vecMulVec, Matrix.mul_apply, mul_assoc]
          ring

/-- Chapter01 Theorem 1.2.15 (1): if `A` is nonsingular and
`1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0`, then the rank-one update `A + Matrix.vecMulVec u v`
is nonsingular. -/
theorem isUnit_rankOneUpdate_of_one_add_dotProduct_nonsingInv_mulVec_ne_zero
    (A : Matrix n n α) (u v : n → α)
    (hA : IsUnit A)
    (hScalar : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    IsUnit (A + Matrix.vecMulVec u v) := by
  let U : Matrix n Unit α := Matrix.replicateCol Unit u
  let V : Matrix Unit n α := Matrix.replicateRow Unit v
  letI : Invertible A := hA.unit.invertible
  letI : Invertible (1 : Matrix Unit Unit α) := isUnit_one.unit.invertible
  have hSchur : IsUnit ((1 : Matrix Unit Unit α)⁻¹ + V * A⁻¹ * U) := by
    simpa [U, V] using rankOneUpdate_schur_isUnit A u v hScalar
  have hSchur' : IsUnit (⅟(1 : Matrix Unit Unit α) + V * ⅟A * U) := by
    simpa [Matrix.invOf_eq_nonsing_inv] using hSchur
  letI : Invertible (⅟(1 : Matrix Unit Unit α) + V * ⅟A * U) := hSchur'.unit.invertible
  letI := Matrix.invertibleAddMulMul A U (1 : Matrix Unit Unit α) V
  simpa [U, V, Matrix.vecMulVec_eq Unit] using
    isUnit_of_invertible (A + U * (1 : Matrix Unit Unit α) * V)

/-- Chapter01 Theorem 1.2.15 (2): under the same hypotheses,
`(A + Matrix.vecMulVec u v)⁻¹ = A⁻¹ -
  (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • Matrix.vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹)`. -/
theorem inv_rankOneUpdate_eq_sub_of_one_add_dotProduct_nonsingInv_mulVec_ne_zero
    (A : Matrix n n α) (u v : n → α)
    (hA : IsUnit A)
    (hScalar : 1 + v ⬝ᵥ (A⁻¹ *ᵥ u) ≠ 0) :
    (A + Matrix.vecMulVec u v)⁻¹ =
      A⁻¹ - (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹ • Matrix.vecMulVec (A⁻¹ *ᵥ u) (v ᵥ* A⁻¹) := by
  let U : Matrix n Unit α := Matrix.replicateCol Unit u
  let V : Matrix Unit n α := Matrix.replicateRow Unit v
  have hSchur : IsUnit ((1 : Matrix Unit Unit α)⁻¹ + V * A⁻¹ * U) := by
    simpa [U, V] using rankOneUpdate_schur_isUnit A u v hScalar
  have hWoodbury :
      (A + U * (1 : Matrix Unit Unit α) * V)⁻¹ =
        A⁻¹ - A⁻¹ * U * ((1 : Matrix Unit Unit α)⁻¹ + V * A⁻¹ * U)⁻¹ * V * A⁻¹ :=
    Matrix.add_mul_mul_inv_eq_sub A U (1 : Matrix Unit Unit α) V hA isUnit_one hSchur
  have hSchurEq :
      (1 : Matrix Unit Unit α)⁻¹ + V * A⁻¹ * U =
        Matrix.diagonal (fun _ : Unit ↦ 1 + v ⬝ᵥ (A⁻¹ *ᵥ u)) := by
    ext _ _
    simpa [U, V] using rankOneUpdate_schurEntry A u v
  have hSchurInv :
      ((1 : Matrix Unit Unit α)⁻¹ + V * A⁻¹ * U)⁻¹ =
        Matrix.diagonal (fun _ : Unit ↦ (1 + v ⬝ᵥ (A⁻¹ *ᵥ u))⁻¹) := by
    rw [hSchurEq, Matrix.inv_subsingleton]
    simp
  rw [hSchurInv] at hWoodbury
  simpa [U, V, Matrix.vecMulVec_eq Unit, rankOneUpdate_correction_eq, mul_assoc] using hWoodbury

end
