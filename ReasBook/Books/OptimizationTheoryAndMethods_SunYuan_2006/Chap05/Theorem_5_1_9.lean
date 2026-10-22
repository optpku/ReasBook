/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_6
import Mathlib.Analysis.Convex.StrictConvexSpace
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Analysis.Matrix.Normed

noncomputable section

open scoped Matrix.Norms.Frobenius

-- Semantic recall: `IsLeastChangeSecantUpdateHessianForm` is already the Chapter 5 owner for
-- Hessian-side least-change secant updates, while Chapter 1 provides the Frobenius norm as an
-- `IsMatrixNorm`. The primitive Broyden rank-one update formula is already a Chapter 5 owner in
-- `Definition_5_1_extra_4`, so this item reuses that owner directly at the Frobenius
-- specialization.

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Helper for Chapter05 Theorem 5.1.9: vectorize a matrix by reindexing its entries by pairs. -/
def matrixEntryVector (A : MatrixN) : EuclideanSpace ℝ (Fin n × Fin n) :=
  WithLp.toLp 2 fun ij : Fin n × Fin n ↦ A ij.1 ij.2

/-- Helper for Chapter05 Theorem 5.1.9: the Frobenius norm of a matrix is the Euclidean norm of
its entry vectorization. -/
lemma frobeniusNorm_eq_matrixEntryVectorNorm
    (A : MatrixN) :
    ‖A‖ = ‖matrixEntryVector A‖ := by
  -- Both sides are the `ℓ²` norm of the same family of entries, indexed differently.
  rw [Matrix.frobenius_norm_def, matrixEntryVector, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp [← Finset.univ_product_univ, Finset.sum_product]

/-- Helper for Chapter05 Theorem 5.1.9: a feasible correction `C` sends the rank-one projector
along `s` to the rank-one matrix built from the residual `r` and the same direction `s`. -/
lemma feasibleCorrection_mulRankOneProjector
    {C : MatrixN} {s r : Point}
    (hCs : Matrix.toEuclideanLin C s = r) :
    C * (((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec s s) =
      ((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec r s := by
  -- Push the feasibility equation through the matrix/right-rank-one multiplication formula.
  calc
    C * (((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec s s)
        = ((dotProduct s s)⁻¹ : ℝ) • (C * Matrix.vecMulVec s s) := by
            rw [Matrix.mul_smul]
    _ = ((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec (Matrix.toEuclideanLin C s) s := by
          simp [Matrix.mul_vecMulVec, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    _ = ((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec r s := by
          rw [hCs]

/-- Helper for Chapter05 Theorem 5.1.9: the Frobenius norm of the rank-one projector onto the
span of `s` is at most `1`. -/
lemma rankOneProjector_frobeniusNorm_le_one
    (s : Point) (hs : s ≠ 0) :
    ‖((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec s s : MatrixN))‖ ≤ 1 := by
  -- Convert the Gram denominator to `‖s‖²`, then bound the outer-product norm by the product
  -- of the column and row norms.
  have hss : dotProduct s s ≠ 0 := by
    intro hzero
    exact hs <| by
      simpa using congrArg (WithLp.toLp 2) ((dotProduct_self_eq_zero).1 hzero)
  have hdot : dotProduct s s = ‖s‖ ^ (2 : ℕ) := by
    simpa [dotProduct, pow_two] using (EuclideanSpace.real_norm_sq_eq s).symm
  have hVecEq :
      (Matrix.vecMulVec s s : MatrixN) =
        Matrix.replicateCol (Fin 1) s.ofLp * Matrix.replicateRow (Fin 1) s.ofLp := by
    ext i j
    simp [Matrix.vecMulVec_apply, Matrix.mul_apply]
  have hCol :
      ‖Matrix.replicateCol (Fin 1) s.ofLp‖ = ‖s‖ := by
    -- Read the single-column matrix as the Euclidean vector `s`.
    calc
      ‖Matrix.replicateCol (Fin 1) s.ofLp‖ = ‖WithLp.toLp 2 s.ofLp‖ := by
        exact Matrix.frobenius_norm_replicateCol (ι := Fin 1) s.ofLp
      _ = ‖s‖ := by
        simp
  have hRow :
      ‖Matrix.replicateRow (Fin 1) s.ofLp‖ = ‖s‖ := by
    -- Read the single-row matrix as the same Euclidean vector `s`.
    calc
      ‖Matrix.replicateRow (Fin 1) s.ofLp‖ = ‖WithLp.toLp 2 s.ofLp‖ := by
        exact Matrix.frobenius_norm_replicateRow (ι := Fin 1) s.ofLp
      _ = ‖s‖ := by
        simp
  have hvec :
      ‖(Matrix.vecMulVec s s : MatrixN)‖ ≤ ‖s‖ * ‖s‖ := by
    calc
      ‖(Matrix.vecMulVec s s : MatrixN)‖
          = ‖Matrix.replicateCol (Fin 1) s.ofLp * Matrix.replicateRow (Fin 1) s.ofLp‖ := by
              rw [hVecEq]
      _ ≤ ‖Matrix.replicateCol (Fin 1) s.ofLp‖ * ‖Matrix.replicateRow (Fin 1) s.ofLp‖ := by
            exact Matrix.frobenius_norm_mul _ _
      _ = ‖s‖ * ‖s‖ := by
            rw [hCol, hRow]
  have hinvNonneg : 0 ≤ ‖(dotProduct s s)⁻¹‖ := norm_nonneg _
  calc
    ‖((((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec s s : MatrixN))‖
        = ‖((dotProduct s s)⁻¹ : ℝ)‖ * ‖(Matrix.vecMulVec s s : MatrixN)‖ := by
            rw [norm_smul]
    _ ≤ ‖((dotProduct s s)⁻¹ : ℝ)‖ * (‖s‖ * ‖s‖) := by
          exact mul_le_mul_of_nonneg_left hvec hinvNonneg
    _ = (dotProduct s s)⁻¹ * (dotProduct s s) := by
          rw [Real.norm_of_nonneg (inv_nonneg.mpr (by rw [hdot]; positivity)), hdot]
          ring
    _ = 1 := inv_mul_cancel₀ hss

/-- Helper for Chapter05 Theorem 5.1.9: two distinct feasible least-change candidates have a
strictly smaller midpoint correction norm. -/
lemma midpointChangeNorm_lt_of_distinctLeastChangeCandidates
    {A₁ A₂ B : MatrixN}
    (hNorm : ‖A₁ - B‖ = ‖A₂ - B‖) (hne : A₁ ≠ A₂) :
    ‖(((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂) - B)‖ < ‖A₁ - B‖ := by
  -- Route correction: use strict convexity of the Euclidean entry-vector space directly instead
  -- of re-deriving midpoint strictness from norm-square algebra.
  let x : EuclideanSpace ℝ (Fin n × Fin n) := matrixEntryVector (A₁ - B)
  let y : EuclideanSpace ℝ (Fin n × Fin n) := matrixEntryVector (A₂ - B)
  have hNormVec :
      ‖x‖ = ‖y‖ := by
    simpa [x, y, frobeniusNorm_eq_matrixEntryVectorNorm] using hNorm
  have hcorrNe :
      x ≠ y := by
    intro hvec
    have hsub :
        A₁ - B = A₂ - B := by
      ext i j
      simpa [x, y, matrixEntryVector] using congrFun (congrArg WithLp.ofLp hvec) (i, j)
    apply hne
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      congrArg (fun M : MatrixN ↦ M + B) hsub
  have hMidVecLt : ‖(1 / 2 : ℝ) • (x + y)‖ < ‖x‖ := by
    -- Equal correction norms turn the strict-convex midpoint theorem into the desired inequality.
    exact (norm_midpoint_lt_iff hNormVec).2 hcorrNe
  have hmidVec :
      matrixEntryVector ((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ - B) = (1 / 2 : ℝ) • (x + y) := by
    ext ij
    rcases ij with ⟨j, i⟩
    simp [matrixEntryVector, x, y]
    ring
  calc
    ‖(((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂) - B)‖
        = ‖matrixEntryVector ((1 / 2 : ℝ) • A₁ + (1 / 2 : ℝ) • A₂ - B)‖ := by
            rw [frobeniusNorm_eq_matrixEntryVectorNorm]
    _ = ‖(1 / 2 : ℝ) • (x + y)‖ := by
          rw [hmidVec]
    _ < ‖x‖ := hMidVecLt
    _ = ‖A₁ - B‖ := by
          simpa [x] using (frobeniusNorm_eq_matrixEntryVectorNorm (A₁ - B)).symm

/-- The Broyden rank-one Hessian update is the Frobenius-norm specialization of the
Hessian-form least-change secant owner. -/
theorem broydenRankOneUpdate_isLeastChangeSecantUpdateHessianForm
    (B : MatrixN) (s y : Point) (hs : s ≠ 0) :
    IsLeastChangeSecantUpdateHessianForm (fun A : MatrixN ↦ ‖A‖)
      B (broydenRankOneUpdate B s y) s y := by
  refine ⟨?_, ?_⟩
  · -- The primitive Broyden rank-one update already satisfies the secant equation.
    simpa [satisfiesQuasiNewtonEquationHessianForm] using
      broydenRankOneUpdate_mulVec B s y hs
  · intro A hA
    let r : Point := y - Matrix.toEuclideanLin B s
    let P : MatrixN := (((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec s s)
    have hAs : Matrix.toEuclideanLin A s = y := hA
    have hCorr :
        Matrix.toEuclideanLin (A - B) s = r := by
      -- Rewrite the arbitrary feasible update as a correction solving the same secant residual.
      simp [r, hAs, sub_eq_add_neg, Matrix.toEuclideanLin, Matrix.toLpLin_apply]
    have hProject :
        (A - B) * P = (((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec r s) := by
      simpa [P] using feasibleCorrection_mulRankOneProjector (C := A - B) (s := s) (r := r) hCorr
    have hBroydenCorr :
        broydenRankOneUpdate B s y - B =
          (((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec r s) := by
      -- Normalize the Broyden correction so the competitor comparison is a one-line norm bound.
      simp [broydenRankOneUpdate_eq, r, sub_eq_add_neg]
    have hProjNorm : ‖P‖ ≤ 1 := rankOneProjector_frobeniusNorm_le_one s hs
    calc
      ‖broydenRankOneUpdate B s y - B‖
          = ‖(((dotProduct s s)⁻¹ : ℝ) • Matrix.vecMulVec r s : MatrixN)‖ := by
              rw [hBroydenCorr]
      _ = ‖(A - B) * P‖ := by
            rw [hProject]
      _ ≤ ‖A - B‖ * ‖P‖ := Matrix.frobenius_norm_mul _ _
      _ ≤ ‖A - B‖ * 1 := by
            exact mul_le_mul_of_nonneg_left hProjNorm (norm_nonneg _)
      _ = ‖A - B‖ := by ring

/-- Chapter05 Theorem 5.1.9: for `B : Matrix (Fin n) (Fin n) ℝ` and `s y : Fin n → ℝ` with
`s ≠ 0`, a matrix `Bhat` equals the Broyden rank-one update
`B + (dotProduct s s)⁻¹ • Matrix.vecMulVec (y - B.mulVec s) s` if and only if `Bhat` is a
solution of the constrained minimization problem `min {‖C - B‖ : C.mulVec s = y}` in the
Frobenius norm. In particular, this update is the unique Frobenius-nearest matrix satisfying the
quasi-Newton equation `Bhat.mulVec s = y`. -/
theorem eq_broydenRankOneUpdate_iff_isLeastChangeSecantUpdateHessianForm
    (B : MatrixN) (s y : Point) (Bhat : MatrixN) (hs : s ≠ 0) :
    Bhat = broydenRankOneUpdate B s y ↔
      IsLeastChangeSecantUpdateHessianForm (fun A : MatrixN ↦ ‖A‖) B Bhat s y := by
  constructor
  · intro hEq
    rw [hEq]
    exact broydenRankOneUpdate_isLeastChangeSecantUpdateHessianForm B s y hs
  · intro hLeast
    have hBroyden :
        IsLeastChangeSecantUpdateHessianForm (fun A : MatrixN ↦ ‖A‖)
          B (broydenRankOneUpdate B s y) s y :=
      broydenRankOneUpdate_isLeastChangeSecantUpdateHessianForm B s y hs
    have hBhatLe :
        ‖Bhat - B‖ ≤ ‖broydenRankOneUpdate B s y - B‖ :=
      hLeast.le_changeMeasure _ hBroyden.secantEquation
    have hBroydenLe :
        ‖broydenRankOneUpdate B s y - B‖ ≤ ‖Bhat - B‖ :=
      hBroyden.le_changeMeasure _ hLeast.secantEquation
    have hNorm :
        ‖Bhat - B‖ = ‖broydenRankOneUpdate B s y - B‖ :=
      le_antisymm hBhatLe hBroydenLe
    by_contra hne
    have hBhatApply : Bhat.mulVec s.ofLp = y.ofLp := hLeast.secantEquation_apply
    have hBroydenApply :
        (broydenRankOneUpdate B s y).mulVec s.ofLp = y.ofLp :=
      hBroyden.secantEquation_apply
    have hMidApply :
        (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • broydenRankOneUpdate B s y).mulVec s.ofLp)
          = y.ofLp := by
      -- The feasible set is affine, so the midpoint of two feasible candidates is still feasible.
      calc
        (((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • broydenRankOneUpdate B s y).mulVec s.ofLp)
            = (1 / 2 : ℝ) • Bhat.mulVec s.ofLp +
                (1 / 2 : ℝ) • (broydenRankOneUpdate B s y).mulVec s.ofLp := by
                  simp [Matrix.add_mulVec, Matrix.smul_mulVec]
        _ = (1 / 2 : ℝ) • y.ofLp + (1 / 2 : ℝ) • y.ofLp := by
              rw [hBhatApply, hBroydenApply]
        _ = y.ofLp := by
              ext i
              simp
              ring
    have hMidLeast :
        ‖Bhat - B‖ ≤ ‖((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • broydenRankOneUpdate B s y) - B‖ :=
      hLeast.le_changeMeasure _
        (satisfiesQuasiNewtonEquationHessianForm_toEuclideanLin_iff.mpr hMidApply)
    have hMidLt :
        ‖((1 / 2 : ℝ) • Bhat + (1 / 2 : ℝ) • broydenRankOneUpdate B s y) - B‖ < ‖Bhat - B‖ := by
      -- Distinct least-change candidates contradict strict convexity of the Frobenius norm.
      exact midpointChangeNorm_lt_of_distinctLeastChangeCandidates hNorm hne
    exact lt_irrefl _ (lt_of_lt_of_le hMidLt hMidLeast)
