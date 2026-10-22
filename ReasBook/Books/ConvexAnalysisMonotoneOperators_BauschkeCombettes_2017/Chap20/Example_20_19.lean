/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Example_20_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ContinuousLinearMap
open Matrix
open scoped EuclideanSpace InnerProductSpace

section

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)
local notation "toEuclideanOperator" =>
  ((Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ] (ℝ² →L[ℝ] ℝ²)))

private theorem real_inner_eq_mul (a b : ℝ) : ⟪a, b⟫_ℝ = a * b := by
  calc
    ⟪a, b⟫_ℝ = (starRingEnd ℝ) a * b := RCLike.inner_apply' a b
    _ = a * b := by simp

private theorem euclideanSpace_fin2_eq (x : ℝ²) : x = !₂[x 0, x 1] := by
  ext i
  fin_cases i <;> simp

private theorem toEuclideanOperator_adjoint (A : Matrix (Fin 2) (Fin 2) ℝ) :
    (toEuclideanOperator A).adjoint = toEuclideanOperator A.transpose := by
  change (A.toEuclideanLin.adjoint).toContinuousLinearMap =
      toEuclideanOperator A.transpose
  exact (congrArg (fun T ↦ T.toContinuousLinearMap)
    (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm).trans <| by rfl

/-- The bounded linear operator on `ℝ²` induced by the matrix `[[1, 1], [1, 1]]`. -/
private def allOnesMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 1; 1, 1]

/-- The bounded linear operator on `ℝ²` induced by the matrix `[[1, 0], [0, 0]]`. -/
private def firstCoordinateProjectorMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- The bounded linear operator on `ℝ²` induced by the quarter-turn matrix `[[0, -1], [1, 0]]`. -/
private def quarterTurnMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![0, -1; 1, 0]

private theorem allOnesMatrix_transpose : allOnesMatrix.transpose = allOnesMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [allOnesMatrix]

private theorem firstCoordinateProjectorMatrix_transpose :
    firstCoordinateProjectorMatrix.transpose = firstCoordinateProjectorMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [firstCoordinateProjectorMatrix]

private theorem quarterTurnMatrix_transpose : quarterTurnMatrix.transpose = -quarterTurnMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarterTurnMatrix]

private theorem quarterTurnMatrix_sq : quarterTurnMatrix * quarterTurnMatrix = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quarterTurnMatrix, Matrix.mul_apply, Fin.sum_univ_two]

/-- The bounded linear operator on `ℝ²` induced by the matrix
`[[1, 1], [1, 1]]`. -/
def allOnesOperator : ℝ² →L[ℝ] ℝ² :=
  toEuclideanOperator allOnesMatrix

/-- The bounded linear operator on `ℝ²` induced by the matrix
`[[1, 0], [0, 0]]`. -/
def firstCoordinateProjector : ℝ² →L[ℝ] ℝ² :=
  toEuclideanOperator firstCoordinateProjectorMatrix

/-- The bounded linear operator on `ℝ²` induced by the quarter-turn matrix
`[[0, -1], [1, 0]]`. -/
def quarterTurnOperator : ℝ² →L[ℝ] ℝ² :=
  toEuclideanOperator quarterTurnMatrix

private theorem allOnesOperator_isPositive : allOnesOperator.IsPositive := by
  refine (isPositive_iff' allOnesOperator).2 ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff']
    simpa [allOnesOperator, allOnesMatrix_transpose] using
      toEuclideanOperator_adjoint allOnesMatrix
  · intro x
    change 0 ≤ ⟪allOnesMatrix.toEuclideanLin.toContinuousLinearMap x, x⟫_ℝ
    simp only [allOnesMatrix, Matrix.toEuclideanLin]
    rw [euclideanSpace_fin2_eq x]
    norm_num [PiLp.inner_apply, Fin.sum_univ_two]
    have h : 0 ≤ (x 0 + x 1) ^ 2 := sq_nonneg (x 0 + x 1)
    simpa [pow_two, mul_add, add_mul, add_comm, add_left_comm, add_assoc] using h

private theorem firstCoordinateProjector_isPositive : firstCoordinateProjector.IsPositive := by
  refine (isPositive_iff' firstCoordinateProjector).2 ⟨?_, ?_⟩
  · rw [isSelfAdjoint_iff']
    simpa [firstCoordinateProjector, firstCoordinateProjectorMatrix_transpose] using
      toEuclideanOperator_adjoint firstCoordinateProjectorMatrix
  · intro x
    change 0 ≤ ⟪firstCoordinateProjectorMatrix.toEuclideanLin.toContinuousLinearMap x, x⟫_ℝ
    simp only [firstCoordinateProjectorMatrix, Matrix.toEuclideanLin]
    rw [euclideanSpace_fin2_eq x]
    norm_num [PiLp.inner_apply, Fin.sum_univ_two]
    nlinarith [sq_nonneg (x 0)]

private theorem quarterTurnOperator_adjoint_eq_neg :
    quarterTurnOperator.adjoint = -quarterTurnOperator := by
  calc
    quarterTurnOperator.adjoint =
        toEuclideanOperator quarterTurnMatrix.transpose := by
      simpa [quarterTurnOperator] using toEuclideanOperator_adjoint quarterTurnMatrix
    _ = toEuclideanOperator (-quarterTurnMatrix) := by
      rw [quarterTurnMatrix_transpose]
    _ = -quarterTurnOperator := by
      simp [quarterTurnOperator]

private theorem neg_quarterTurnOperator_adjoint_eq_neg :
    (-quarterTurnOperator).adjoint = -(-quarterTurnOperator) := by
  simp [quarterTurnOperator_adjoint_eq_neg]

private theorem quarterTurnOperator_sq : quarterTurnOperator ^ 2 = -1 := by
  calc
    quarterTurnOperator ^ 2 =
        toEuclideanOperator (quarterTurnMatrix * quarterTurnMatrix) := by
      rw [pow_two, quarterTurnOperator]
      exact (map_mul toEuclideanOperator quarterTurnMatrix quarterTurnMatrix).symm
    _ = toEuclideanOperator (-1) := by rw [quarterTurnMatrix_sq]
    _ = -(toEuclideanOperator (1 : Matrix (Fin 2) (Fin 2) ℝ)) := by
      exact map_neg toEuclideanOperator (1 : Matrix (Fin 2) (Fin 2) ℝ)
    _ = -1 := by
      rw [map_one toEuclideanOperator]

-- Proof sketch: compute the quadratic form of `allOnesOperator`; for
-- `x = (x₁, x₂)` it is `(x₁ + x₂)^2`, hence nonnegative.
/-- Example 20.19 (1): the operator `A = [[1, 1], [1, 1]]` is monotone on `ℝ²`. -/
theorem allOnesOperator_isMonotone :
    allOnesOperator.toLinearMap.IsMonotone := by
  exact allOnesOperator_isPositive.toLinearMap.isMonotone

-- Proof sketch: the quadratic form of `firstCoordinateProjector` is `x₁^2`,
-- so monotonicity follows immediately from the characterization in Example 20.16.
/-- Example 20.19 (2): the operator `B = [[1, 0], [0, 0]]` is monotone on `ℝ²`. -/
theorem firstCoordinateProjector_isMonotone :
    firstCoordinateProjector.toLinearMap.IsMonotone := by
  exact firstCoordinateProjector_isPositive.toLinearMap.isMonotone

-- Proof sketch: the quadratic form of `quarterTurnOperator` vanishes identically,
-- because `⟪(0 -1; 1 0)x, x⟫ = 0` for every `x ∈ ℝ²`.
/-- Example 20.19 (3): the operator `C = [[0, -1], [1, 0]]` is monotone on `ℝ²`. -/
theorem quarterTurnOperator_isMonotone :
    quarterTurnOperator.toLinearMap.IsMonotone := by
  exact ContinuousLinearMap.isMonotone_of_adjoint_eq_neg
    quarterTurnOperator quarterTurnOperator_adjoint_eq_neg

-- Proof sketch: `-quarterTurnOperator` is the opposite skew-symmetric rotation,
-- so its quadratic form also vanishes identically.
/-- Example 20.19 (4): the operator `-C` is monotone on `ℝ²`. -/
theorem neg_quarterTurnOperator_isMonotone :
    (-quarterTurnOperator).toLinearMap.IsMonotone := by
  exact ContinuousLinearMap.isMonotone_of_adjoint_eq_neg
    (-quarterTurnOperator) neg_quarterTurnOperator_adjoint_eq_neg

-- Proof sketch: compute `allOnesOperator * firstCoordinateProjector`, whose matrix is
-- `[[1, 0], [1, 0]]`. Evaluating the quadratic form at the vector `(1, -2)` gives a negative
-- value, so the product is not monotone.
/-- Example 20.19 (5): the product `AB` need not be monotone, showing that the hypotheses of
Fact 20.18 cannot be dropped. -/
theorem allOnesOperator_mul_firstCoordinateProjector_not_isMonotone :
    ¬ (allOnesOperator * firstCoordinateProjector).toLinearMap.IsMonotone := by
  intro h
  have h' := h !₂[(1 : ℝ), -2]
  change 0 ≤
    ⟪(allOnesMatrix.toEuclideanLin.toContinuousLinearMap *
        firstCoordinateProjectorMatrix.toEuclideanLin.toContinuousLinearMap) !₂[(1 : ℝ), -2],
      !₂[(1 : ℝ), -2]⟫_ℝ at h'
  norm_num [allOnesMatrix, firstCoordinateProjectorMatrix, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, dotProduct, Fin.sum_univ_two] at h'
  rw [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_mul, real_inner_eq_mul] at h'
  norm_num at h'

-- Proof sketch: the square of `quarterTurnOperator` is `-id`, whose quadratic form is
-- `-‖x‖^2`; it is negative on every nonzero vector.
/-- Example 20.19 (6): the square `C^2` is not monotone, again showing that the hypotheses of
Fact 20.18 are essential. -/
theorem quarterTurnOperator_sq_not_isMonotone :
    ¬ (quarterTurnOperator ^ 2).toLinearMap.IsMonotone := by
  rw [quarterTurnOperator_sq]
  intro h
  have h' := h !₂[(1 : ℝ), 0]
  rw [PiLp.inner_apply, Fin.sum_univ_two, real_inner_eq_mul, real_inner_eq_mul] at h'
  norm_num at h'

end
