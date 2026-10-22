/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_3_2

open Matrix

noncomputable section

section

variable {n m : ℕ}

local notation "HessianMatrix" => Matrix (Fin n) (Fin n) ℝ
local notation "ConstraintMatrix" => Matrix (Fin n) (Fin m) ℝ
local notation "DualMatrix" => Matrix (Fin m) (Fin m) ℝ

-- Domain-style sampling for this file:
-- * primary domain: KKT block matrices and Schur-complement inverse formulas.
-- * core/canonical owners inspected: the Chapter 9 KKT owner `kktMatrix`, together with
--   mathlib's block extraction owners `Matrix.toBlocks₁₁`/`toBlocks₁₂`/`toBlocks₂₂` and the
--   Schur-complement inverse formula `Matrix.invOf_fromBlocks₁₁_eq`.
-- * source-facing owner layer kept here: the inverse-KKT blocks `kktInverseU`, `kktInverseW`,
--   and `kktInverseT` from formula `(9.3.50)`.
-- * primitive data vs derived API: the primitive data are only these three extracted inverse
--   blocks; the Exercise 9.11 formulas are derived equalities for those owners.

/-- The `U` block in the inverse KKT matrix decomposition `(9.3.50)`. -/
def kktInverseU (G : HessianMatrix) (A : ConstraintMatrix) : HessianMatrix :=
  ((kktMatrix G A)⁻¹).toBlocks₁₁

#print axioms kktInverseU

/-- The `W` block in the inverse KKT matrix decomposition `(9.3.50)`. -/
def kktInverseW (G : HessianMatrix) (A : ConstraintMatrix) : ConstraintMatrix :=
  ((kktMatrix G A)⁻¹).toBlocks₁₂

#print axioms kktInverseW

/-- The `T` block in the inverse KKT matrix decomposition `(9.3.50)`. -/
def kktInverseT (G : HessianMatrix) (A : ConstraintMatrix) : DualMatrix :=
  ((kktMatrix G A)⁻¹).toBlocks₂₂

#print axioms kktInverseT

/-- Helper for Chapter09 Exercise 9.11: full column rank gives injectivity of the constraint
matrix action on multiplier vectors. -/
lemma injective_mulVec_of_rank_eq_width
    (A : ConstraintMatrix) (hA : Matrix.rank A = m) :
    Function.Injective A.mulVec := by
  -- Convert the rank hypothesis into the vanishing of the nullspace dimension.
  have hNullity : Matrix.rank A + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = m := by
    simpa [Matrix.rank] using LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hKerFinrank : Module.finrank ℝ (LinearMap.ker A.mulVecLin) = 0 := by
    omega
  have hKerBot : LinearMap.ker A.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 hKerFinrank
  -- A linear map with trivial kernel is injective.
  exact LinearMap.ker_eq_bot.mp hKerBot

/-- Helper for Chapter09 Exercise 9.11: the Schur factor `Aᵀ G⁻¹ A` is positive definite under
the source hypotheses. -/
lemma schur_factor_posDef
    (G : HessianMatrix) (A : ConstraintMatrix)
    (hG : G.PosDef) (hA : Matrix.rank A = m) :
    (A.transpose * G⁻¹ * A).PosDef := by
  -- Route the full-column-rank hypothesis into the conjugation lemma for positive-definite
  -- matrices.
  have hInj : Function.Injective A.mulVec := injective_mulVec_of_rank_eq_width A hA
  simpa using hG.inv.conjTranspose_mul_mul_same (B := A) hInj

/-- Helper for Chapter09 Exercise 9.11: the inverse KKT matrix is the Schur-complement block
inverse from formulas `(9.3.53)`-`(9.3.55)`. -/
lemma kktMatrix_inv_eq_schur_blocks
    (G : HessianMatrix) (A : ConstraintMatrix)
    (hG : G.PosDef) (hA : Matrix.rank A = m) :
    (kktMatrix G A)⁻¹ =
      Matrix.fromBlocks
        (G⁻¹ - G⁻¹ * A * (A.transpose * G⁻¹ * A)⁻¹ * A.transpose * G⁻¹)
        (-(G⁻¹ * A * (A.transpose * G⁻¹ * A)⁻¹))
        (-((A.transpose * G⁻¹ * A)⁻¹ * A.transpose * G⁻¹))
        (-((A.transpose * G⁻¹ * A)⁻¹)) := by
  -- Control the full inverse through the Schur complement of the positive-definite Hessian block.
  let _ : Invertible G := hG.isUnit.invertible
  have hSchurPos :
      (A.transpose * ⅟G * A).PosDef := by
    simpa [Matrix.invOf_eq_nonsing_inv] using schur_factor_posDef G A hG hA
  have hSchurUnit : IsUnit (0 - (-A.transpose) * ⅟G * (-A)) := by
    simpa [sub_eq_add_neg, neg_mul, mul_neg, neg_mul_neg, mul_assoc] using hSchurPos.isUnit.neg
  let _ : Invertible (0 - (-A.transpose) * ⅟G * (-A)) := hSchurUnit.invertible
  let _ : Invertible (Matrix.fromBlocks G (-A) (-A.transpose) (0 : DualMatrix)) :=
    Matrix.fromBlocks₁₁Invertible G (-A) (-A.transpose) 0
  have hBlocks :
      (Matrix.fromBlocks G (-A) (-A.transpose) (0 : DualMatrix))⁻¹ =
        Matrix.fromBlocks
          (G⁻¹ + G⁻¹ * A * (-(A.transpose * G⁻¹ * A))⁻¹ * A.transpose * G⁻¹)
          (G⁻¹ * A * (-(A.transpose * G⁻¹ * A))⁻¹)
          ((-(A.transpose * G⁻¹ * A))⁻¹ * A.transpose * G⁻¹)
          ((-(A.transpose * G⁻¹ * A))⁻¹) := by
    -- First rewrite `⅟` to `⁻¹`; keep the Schur factor as `-(Aᵀ G⁻¹ A)` for a separate sign pass.
    simpa [sub_eq_add_neg, neg_mul, mul_neg, neg_mul_neg, mul_assoc, Matrix.invOf_eq_nonsing_inv]
      using (Matrix.invOf_fromBlocks₁₁_eq G (-A) (-A.transpose) (0 : DualMatrix))
  have hSchurPos' : (A.transpose * G⁻¹ * A).PosDef := schur_factor_posDef G A hG hA
  let _ : Invertible (A.transpose * G⁻¹ * A : DualMatrix) := hSchurPos'.isUnit.invertible
  let _ : Invertible (-(A.transpose * G⁻¹ * A : DualMatrix)) := hSchurPos'.isUnit.neg.invertible
  have hNegInv : (-(A.transpose * G⁻¹ * A : DualMatrix))⁻¹ = -((A.transpose * G⁻¹ * A)⁻¹) := by
    calc
      (-(A.transpose * G⁻¹ * A : DualMatrix))⁻¹ = ⅟ (-(A.transpose * G⁻¹ * A : DualMatrix)) := by
        rw [← Matrix.invOf_eq_nonsing_inv]
      _ = -⅟ (A.transpose * G⁻¹ * A : DualMatrix) := invOf_neg _
      _ = -((A.transpose * G⁻¹ * A)⁻¹) := by
        rw [Matrix.invOf_eq_nonsing_inv]
  -- Rewrite the Schur-complement signs once, then repackage the result as the KKT inverse.
  calc
    (kktMatrix G A)⁻¹ = (Matrix.fromBlocks G (-A) (-A.transpose) (0 : DualMatrix))⁻¹ := by
      simp [kktMatrix_eq]
    _ =
        Matrix.fromBlocks
          (G⁻¹ + G⁻¹ * A * (-(A.transpose * G⁻¹ * A))⁻¹ * A.transpose * G⁻¹)
          (G⁻¹ * A * (-(A.transpose * G⁻¹ * A))⁻¹)
          ((-(A.transpose * G⁻¹ * A))⁻¹ * A.transpose * G⁻¹)
          ((-(A.transpose * G⁻¹ * A))⁻¹) := hBlocks
    _ =
        Matrix.fromBlocks
          (G⁻¹ - G⁻¹ * A * (A.transpose * G⁻¹ * A)⁻¹ * A.transpose * G⁻¹)
          (-(G⁻¹ * A * (A.transpose * G⁻¹ * A)⁻¹))
          (-((A.transpose * G⁻¹ * A)⁻¹ * A.transpose * G⁻¹))
          (-((A.transpose * G⁻¹ * A)⁻¹)) := by
      simp_rw [hNegInv]
      simp [sub_eq_add_neg, neg_mul]

/-- Chapter09 Exercise 9.11 (1): if `G` is positive definite and `A` has full column rank, then
the `U` block in `(9.3.50)` is `G⁻¹ - G⁻¹ A (Aᵀ G⁻¹ A)⁻¹ Aᵀ G⁻¹`, which is equation `(9.3.53)`. -/
theorem chapter09Exercise911_primalBlock_eq
    (G : HessianMatrix) (A : ConstraintMatrix)
    (hG : G.PosDef) (hA : Matrix.rank A = m) :
    kktInverseU G A =
      G⁻¹ - G⁻¹ * A * (A.transpose * G⁻¹ * A)⁻¹ * A.transpose * G⁻¹ := by
  -- Extract the `(1,1)` block from the shared inverse formula.
  have hInv := kktMatrix_inv_eq_schur_blocks G A hG hA
  simpa [kktInverseU, Matrix.toBlocks_fromBlocks₁₁] using
    congrArg Matrix.toBlocks₁₁ hInv

/-- Chapter09 Exercise 9.11 (2): if `G` is positive definite and `A` has full column rank, then
the `W` block in `(9.3.50)` is `-G⁻¹ A (Aᵀ G⁻¹ A)⁻¹`, which is equation `(9.3.54)`. -/
theorem chapter09Exercise911_multiplierBlock_eq
    (G : HessianMatrix) (A : ConstraintMatrix)
    (hG : G.PosDef) (hA : Matrix.rank A = m) :
    kktInverseW G A =
      -(G⁻¹ * A * (A.transpose * G⁻¹ * A)⁻¹) := by
  -- Extract the `(1,2)` block from the same Schur-complement inverse identity.
  have hInv := kktMatrix_inv_eq_schur_blocks G A hG hA
  simpa [kktInverseW, Matrix.toBlocks_fromBlocks₁₂] using
    congrArg Matrix.toBlocks₁₂ hInv

/-- Chapter09 Exercise 9.11 (3): if `G` is positive definite and `A` has full column rank, then
the `T` block in `(9.3.50)` is `-(Aᵀ G⁻¹ A)⁻¹`, which is equation `(9.3.55)`. -/
theorem chapter09Exercise911_dualBlock_eq
    (G : HessianMatrix) (A : ConstraintMatrix)
    (hG : G.PosDef) (hA : Matrix.rank A = m) :
    kktInverseT G A =
      -((A.transpose * G⁻¹ * A)⁻¹) := by
  -- Extract the `(2,2)` block from the shared inverse formula.
  have hInv := kktMatrix_inv_eq_schur_blocks G A hG hA
  simpa [kktInverseT, Matrix.toBlocks_fromBlocks₂₂] using
    congrArg Matrix.toBlocks₂₂ hInv

end
