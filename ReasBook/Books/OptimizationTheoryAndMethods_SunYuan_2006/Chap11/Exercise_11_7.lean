/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric

open Matrix

noncomputable section

section

variable {n : ℕ}

local notation "VectorN" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "BorderedIndex" => Sum (Fin n) (Fin 1)
local notation "BorderedVectorN" => EuclideanSpace ℝ BorderedIndex
local notation "BorderedMatrixN" => Matrix BorderedIndex BorderedIndex ℝ

-- Semantic recall: `lean_leansearch` surfaced the Schur-complement block-matrix API in
-- `Mathlib.LinearAlgebra.Matrix.SchurComplement`, especially the `Matrix.fromBlocks`
-- nonsingularity criteria and inverse formulas. This item keeps the source bordered matrix
-- explicit and records the scalar Schur-complement and rank-one inverse conclusions directly.

/-- The scalar Schur complement `β - bᵀ B⁻¹ b` appearing in Exercise 11.7. -/
def borderedMatrixSchurComplement (B : MatrixN) (b : VectorN) (β : ℝ) : ℝ :=
  β - dotProduct b ((B⁻¹).mulVec b)

/-- Helper for Chapter11 Exercise 11.7: the constant `1 × 1` block with entry `β`. -/
def scalarBlock (β : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  fun _ _ ↦ β

/-- Helper for Chapter11 Exercise 11.7: view `b` as the single-column matrix used in the bordered
block matrix. -/
def borderedColumn (b : Fin n → ℝ) : Matrix (Fin n) (Fin 1) ℝ :=
  fun i _ ↦ b i

/-- Helper for Chapter11 Exercise 11.7: view `bᵀ` as the single-row matrix used in the bordered
block matrix. -/
def borderedRow (b : Fin n → ℝ) : Matrix (Fin 1) (Fin n) ℝ :=
  fun _ j ↦ b j

/-- The bordered matrix `[[B, b], [bᵀ, β]]` from `(11.5.39)`, with `b` viewed as a column vector
and `bᵀ` as the corresponding row vector. -/
def borderedMatrix (B : MatrixN) (b : VectorN) (β : ℝ) : BorderedMatrixN :=
  Matrix.fromBlocks B (borderedColumn b) (borderedRow b) (scalarBlock β)

/-- The vector `[(B⁻¹ b)ᵀ, -1]ᵀ` whose outer product gives the rank-one correction term in the
inverse formula `(11.5.40)`. -/
def borderedMatrixRankOneVector (B : MatrixN) (b : VectorN) : BorderedVectorN :=
  WithLp.toLp 2 <| Sum.elim ((B⁻¹).mulVec b.ofLp) (fun _ ↦ (-1 : ℝ))

@[simp] theorem borderedMatrixRankOneVector_inl (B : MatrixN) (b : VectorN) (i : Fin n) :
    borderedMatrixRankOneVector B b (Sum.inl i) = ((B⁻¹).mulVec b) i :=
  by simp [borderedMatrixRankOneVector]

@[simp] theorem borderedMatrixRankOneVector_inr (B : MatrixN) (b : VectorN) (i : Fin 1) :
    borderedMatrixRankOneVector B b (Sum.inr i) = (-1 : ℝ) :=
  by simp [borderedMatrixRankOneVector]

/-- Helper for Chapter11 Exercise 11.7: multiplying the bordered column by `B⁻¹` produces the
single-column matrix built from `(B⁻¹) b`. -/
lemma nonsingInv_mul_borderedColumn_eq (B : MatrixN) (b : VectorN) :
    B⁻¹ * borderedColumn b = borderedColumn ((B⁻¹).mulVec b) := by
  -- Normalize the single-column block with the canonical `mulVec` API.
  ext i j
  simp [borderedColumn, Matrix.mul_apply, Matrix.mulVec, dotProduct]

/-- Helper for Chapter11 Exercise 11.7: multiplying the bordered row by `B⁻¹` produces the
single-row matrix built from `bᵀ B⁻¹`. -/
lemma borderedRow_mul_nonsingInv_eq (B : MatrixN) (b : VectorN) :
    borderedRow b * B⁻¹ = borderedRow (b ᵥ* B⁻¹) := by
  -- Normalize the single-row block with the canonical `vecMul` API.
  ext i j
  simp [borderedRow, Matrix.mul_apply, Matrix.vecMul, dotProduct]

/-- Helper for Chapter11 Exercise 11.7: the `1 × 1` Schur block in the block-inverse formula is
the constant matrix with value `β - bᵀ B⁻¹ b`. -/
lemma bordered_schur_block_eq (B : MatrixN) (b : VectorN) (β : ℝ) :
    (scalarBlock β - borderedRow b * B⁻¹ * borderedColumn b) =
      fun _ _ ↦ borderedMatrixSchurComplement B b β := by
  have hProduct :
      borderedRow b * B⁻¹ * borderedColumn b =
        fun _ _ ↦ dotProduct b ((B⁻¹).mulVec b) := by
    -- Normalize the column block so the `1 × 1` product becomes the scalar dot product.
    rw [Matrix.mul_assoc, nonsingInv_mul_borderedColumn_eq]
    ext i j
    simp [borderedRow, borderedColumn, Matrix.mul_apply, dotProduct]
  -- Substitute the scalar Schur complement once the unique block entry is identified.
  ext i j
  simp [scalarBlock, borderedMatrixSchurComplement, hProduct]

/-- Helper for Chapter11 Exercise 11.7: when `B` is symmetric, the row vector `bᵀ B⁻¹`
coincides with the column vector `B⁻¹ b`. -/
lemma vecMul_nonsingInv_eq_mulVec_of_isSymm
    (B : MatrixN) (b : VectorN) (hBsym : B.IsSymm) :
    b ᵥ* B⁻¹ = (B⁻¹).mulVec b := by
  -- Symmetry of `B⁻¹` turns the row expression into the same column vector.
  calc
    b ᵥ* B⁻¹ = b ᵥ* (B⁻¹)ᵀ := by rw [hBsym.inv.eq]
    _ = (B⁻¹).mulVec b := by rw [Matrix.vecMul_transpose]

/-- Helper for Chapter11 Exercise 11.7: after extracting the scalar Schur factor, the remaining
block correction is the outer product `u uᵀ` from `(11.5.40)`. -/
lemma bordered_rank_one_correction_eq
    (B : MatrixN) (b : VectorN) (hBsym : B.IsSymm) :
    Matrix.fromBlocks
      (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹)
      (-(B⁻¹ * borderedColumn b))
      (-(borderedRow b * B⁻¹))
      (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      Matrix.vecMulVec
        (borderedMatrixRankOneVector B b)
        (borderedMatrixRankOneVector B b) := by
  have hRow :
      borderedRow b * B⁻¹ = borderedRow ((B⁻¹).mulVec b) := by
    -- Symmetry identifies the lower-left row with the same vector used in the upper-right block.
    rw [borderedRow_mul_nonsingInv_eq, vecMul_nonsingInv_eq_mulVec_of_isSymm B b hBsym]
  -- Route correction: normalize the off-diagonal blocks first, then compare the four bordered
  -- blocks entrywise with the outer product of `[(B⁻¹ b)ᵀ, -1]ᵀ`.
  calc
    Matrix.fromBlocks
        (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹)
        (-(B⁻¹ * borderedColumn b))
        (-(borderedRow b * B⁻¹))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) =
      Matrix.fromBlocks
        (borderedColumn ((B⁻¹).mulVec b) * borderedRow ((B⁻¹).mulVec b))
        (-borderedColumn ((B⁻¹).mulVec b))
        (-borderedRow ((B⁻¹).mulVec b))
        (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
          -- Rewrite the four blocks into the common vector `(B⁻¹) b`.
          rw [Matrix.mul_assoc, nonsingInv_mul_borderedColumn_eq, hRow]
    _ =
      Matrix.vecMulVec
        (borderedMatrixRankOneVector B b)
        (borderedMatrixRankOneVector B b) := by
          -- Each block entry is now a direct evaluation of the outer product.
          ext i j
          rcases i with i | i <;> rcases j with j | j
          · simp [borderedColumn, borderedRow, Matrix.mul_apply, Matrix.vecMulVec]
          · simp [borderedColumn, Matrix.vecMulVec]
          · simp [borderedRow, Matrix.vecMulVec]
          · have hij : i = j := Subsingleton.elim _ _
            simp [Matrix.vecMulVec, hij]

/-- Chapter11 Exercise 11.7 (1): if `B` is invertible, then the bordered matrix
`borderedMatrix B b β = [[B, b], [bᵀ, β]]` is invertible if and only if the scalar Schur
complement `β - bᵀ B⁻¹ b` is nonzero, i.e. formula `(11.5.39)`. The symmetry assumption from the
exercise is not needed for this invertibility criterion. -/
theorem borderedMatrix_isUnit_iff_schurComplement_ne_zero
    (B : MatrixN) (b : VectorN) (β : ℝ) (hB : IsUnit B) :
    IsUnit (borderedMatrix B b β) ↔ borderedMatrixSchurComplement B b β ≠ 0 := by
  letI : Invertible B := hB.unit.invertible
  have hSchurEq :
      scalarBlock β - borderedRow b * ⅟B * borderedColumn b =
        scalarBlock (borderedMatrixSchurComplement B b β) := by
    -- Rewrite the Schur block into the scalar complement using `⅟B = B⁻¹`.
    have hSchurEqFun :
        scalarBlock β - borderedRow b * ⅟B * borderedColumn b =
          (fun _ _ ↦ borderedMatrixSchurComplement B b β : Matrix (Fin 1) (Fin 1) ℝ) := by
      simpa [Matrix.invOf_eq_nonsing_inv] using bordered_schur_block_eq B b β
    exact hSchurEqFun.trans rfl
  -- Reduce the bordered matrix criterion to the `1 × 1` Schur block.
  rw [borderedMatrix]
  rw [Matrix.isUnit_fromBlocks_iff_of_invertible₁₁, hSchurEq]
  -- A `1 × 1` matrix is invertible exactly when its unique scalar entry is nonzero.
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
  simpa [scalarBlock] using (isUnit_iff_ne_zero : IsUnit (borderedMatrixSchurComplement B b β) ↔
    borderedMatrixSchurComplement B b β ≠ 0)

/-- Chapter11 Exercise 11.7 (2): under the same symmetric and invertible hypotheses on `B`, if
`borderedMatrix B b β` is invertible, then its inverse is the block-diagonal term
`Matrix.fromBlocks B⁻¹ 0 0 0` plus the canonical rank-one correction from `(11.5.40)`. The
symmetry of `B` is used here to write the correction as `Matrix.vecMulVec u u` with the same
vector on both sides. -/
theorem borderedMatrix_inv_eq_inverseBase_add_rankOne
    (B : MatrixN) (b : VectorN) (β : ℝ)
    (hBsym : B.IsSymm) (hB : IsUnit B)
    (hBordered : IsUnit (borderedMatrix B b β)) :
    (borderedMatrix B b β)⁻¹ =
      Matrix.fromBlocks B⁻¹ 0 0 0 +
        (borderedMatrixSchurComplement B b β) ⁻¹ •
          Matrix.vecMulVec
            (borderedMatrixRankOneVector B b)
            (borderedMatrixRankOneVector B b) := by
  letI : Invertible B := hB.unit.invertible
  letI : Invertible (borderedMatrix B b β) := hBordered.unit.invertible
  let s : ℝ := (borderedMatrixSchurComplement B b β) ⁻¹
  let S : Matrix (Fin 1) (Fin 1) ℝ := scalarBlock s
  have hSchurNonzero : borderedMatrixSchurComplement B b β ≠ 0 :=
    (borderedMatrix_isUnit_iff_schurComplement_ne_zero B b β hB).mp hBordered
  have hSchurUnit :
      IsUnit (scalarBlock β - borderedRow b * ⅟B * borderedColumn b) := by
    have hScalarUnit : IsUnit (scalarBlock (borderedMatrixSchurComplement B b β)) := by
      -- The Schur block is invertible because its determinant is the nonzero scalar complement.
      rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
      simpa [scalarBlock] using (isUnit_iff_ne_zero.mpr hSchurNonzero)
    -- Transport the scalar invertibility back across the Schur-block identification.
    have hSchurEq :
        scalarBlock β - borderedRow b * ⅟B * borderedColumn b =
          scalarBlock (borderedMatrixSchurComplement B b β) := by
      have hSchurEqFun :
          scalarBlock β - borderedRow b * ⅟B * borderedColumn b =
            (fun _ _ ↦ borderedMatrixSchurComplement B b β : Matrix (Fin 1) (Fin 1) ℝ) := by
        simpa [Matrix.invOf_eq_nonsing_inv] using bordered_schur_block_eq B b β
      exact hSchurEqFun.trans rfl
    rw [hSchurEq]
    exact hScalarUnit
  letI : Invertible (scalarBlock β - borderedRow b * ⅟B * borderedColumn b) :=
    hSchurUnit.unit.invertible
  letI : Invertible (Matrix.fromBlocks B (borderedColumn b) (borderedRow b) (scalarBlock β)) :=
    Invertible.copy ‹Invertible (borderedMatrix B b β)› _ (by simp [borderedMatrix])
  have hInv :
      (borderedMatrix B b β)⁻¹ =
        Matrix.fromBlocks
          (B⁻¹ + B⁻¹ * borderedColumn b * S * borderedRow b * B⁻¹)
          (-(B⁻¹ * borderedColumn b * S))
          (-(S * borderedRow b * B⁻¹))
          S := by
    -- Apply the Schur-complement block inverse formula and collapse the `1 × 1` inverse block.
    have hInvOf :=
      Matrix.invOf_fromBlocks₁₁_eq B (borderedColumn b) (borderedRow b) (scalarBlock β)
    simp only [Matrix.invOf_eq_nonsing_inv] at hInvOf
    have hSchurEq :
        scalarBlock β - borderedRow b * B⁻¹ * borderedColumn b =
          scalarBlock (borderedMatrixSchurComplement B b β) := by
      exact (bordered_schur_block_eq B b β).trans rfl
    have hSchurInv :
        (scalarBlock (borderedMatrixSchurComplement B b β))⁻¹ = S := by
      ext i j
      have hij : i = j := Subsingleton.elim _ _
      subst j
      simp [S, s, scalarBlock, Matrix.inv_subsingleton]
    rw [hSchurEq, hSchurInv] at hInvOf
    simpa [borderedMatrix, S, s] using hInvOf
  have hScalarOne : S = s • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    -- The unique `1 × 1` matrix with entry `s` is `s` times the identity.
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    simp [S, scalarBlock, hij, s]
  have hReshape :
      Matrix.fromBlocks
          (B⁻¹ + B⁻¹ * borderedColumn b * S * borderedRow b * B⁻¹)
          (-(B⁻¹ * borderedColumn b * S))
          (-(S * borderedRow b * B⁻¹))
          S =
        Matrix.fromBlocks
          (B⁻¹ + s • (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹))
          (s • (-(B⁻¹ * borderedColumn b)))
          (s • (-(borderedRow b * B⁻¹)))
          (s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
    -- Rewrite multiplication by the `1 × 1` scalar block as ordinary scalar multiplication.
    rw [hScalarOne]
    have hTopLeft :
        B⁻¹ + B⁻¹ * borderedColumn b * (s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * borderedRow b * B⁻¹ =
          B⁻¹ + s • (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹) := by
      calc
        B⁻¹ + B⁻¹ * borderedColumn b * (s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * borderedRow b * B⁻¹ =
            B⁻¹ + ((B⁻¹ * borderedColumn b) * (s • (1 : Matrix (Fin 1) (Fin 1) ℝ))) *
              borderedRow b * B⁻¹ := by simp [Matrix.mul_assoc]
        _ = B⁻¹ + (s • ((B⁻¹ * borderedColumn b) * (1 : Matrix (Fin 1) (Fin 1) ℝ))) *
              borderedRow b * B⁻¹ := by rw [Matrix.mul_smul]
        _ = B⁻¹ + (s • (B⁻¹ * borderedColumn b)) * borderedRow b * B⁻¹ := by
              rw [Matrix.mul_one]
        _ = B⁻¹ + s • ((B⁻¹ * borderedColumn b) * borderedRow b) * B⁻¹ := by
              rw [Matrix.smul_mul]
        _ = B⁻¹ + s • (((B⁻¹ * borderedColumn b) * borderedRow b) * B⁻¹) := by
              rw [Matrix.smul_mul]
        _ = B⁻¹ + s • (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹) := by
              simp [Matrix.mul_assoc]
    have hTopRight :
        -(B⁻¹ * borderedColumn b * (s • (1 : Matrix (Fin 1) (Fin 1) ℝ))) =
          s • (-(B⁻¹ * borderedColumn b)) := by
      calc
        -(B⁻¹ * borderedColumn b * (s • (1 : Matrix (Fin 1) (Fin 1) ℝ))) =
            -(s • ((B⁻¹ * borderedColumn b) * (1 : Matrix (Fin 1) (Fin 1) ℝ))) := by
              rw [Matrix.mul_smul]
        _ = -(s • (B⁻¹ * borderedColumn b)) := by rw [Matrix.mul_one]
        _ = s • (-(B⁻¹ * borderedColumn b)) := by rw [← smul_neg]
    have hBottomLeft :
        -((s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * borderedRow b * B⁻¹) =
          s • (-(borderedRow b * B⁻¹)) := by
      calc
        -((s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) * borderedRow b * B⁻¹) =
            -((s • borderedRow b) * B⁻¹) := by rw [Matrix.smul_mul, Matrix.one_mul]
        _ = -(s • (borderedRow b * B⁻¹)) := by rw [Matrix.smul_mul]
        _ = s • (-(borderedRow b * B⁻¹)) := by rw [← smul_neg]
    rw [hTopLeft, hTopRight, hBottomLeft]
  -- Substitute the normalized correction block and package it as a rank-one outer product.
  calc
    (borderedMatrix B b β)⁻¹ =
        Matrix.fromBlocks
          (B⁻¹ + s • (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹))
          (s • (-(B⁻¹ * borderedColumn b)))
          (s • (-(borderedRow b * B⁻¹)))
          (s • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by
            rw [hInv, hReshape]
    _ =
        Matrix.fromBlocks B⁻¹ 0 0 0 +
          s • Matrix.fromBlocks
            (B⁻¹ * borderedColumn b * borderedRow b * B⁻¹)
            (-(B⁻¹ * borderedColumn b))
            (-(borderedRow b * B⁻¹))
            (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
              rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
              simp
    _ =
        Matrix.fromBlocks B⁻¹ 0 0 0 +
          s • Matrix.vecMulVec
            (borderedMatrixRankOneVector B b)
            (borderedMatrixRankOneVector B b) := by
              rw [bordered_rank_one_correction_eq B b hBsym]
    _ =
        Matrix.fromBlocks B⁻¹ 0 0 0 +
          (borderedMatrixSchurComplement B b β) ⁻¹ •
            Matrix.vecMulVec
              (borderedMatrixRankOneVector B b)
              (borderedMatrixRankOneVector B b) := by
                simp [s]

end
