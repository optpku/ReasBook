module

public import Mathlib.Analysis.Matrix.Order
public import ReasLib.Analysis.InnerProductSpace.Congruence

public section

/-!
# Square roots of positive-definite matrices

This module specializes the matrix continuous functional calculus to real positive-definite
matrices and exposes the resulting coordinate change through the generic congruence API.
-/

noncomputable section

universe u

open scoped MatrixOrder

namespace Matrix.PosDef

variable {n : Type u} [Fintype n]

open scoped Classical in
/-- The continuous-functional-calculus square root of a positive-definite real matrix is positive
definite. -/
theorem cfcSqrt {A : Matrix n n ℝ} (hA : A.PosDef) : (CFC.sqrt A).PosDef := by
  exact Matrix.IsStrictlyPositive.posDef (hA.isStrictlyPositive.sqrt A)

variable [DecidableEq n]

/-- The positive square root, transported to Euclidean space, is an invertible coordinate change. -/
noncomputable def sqrtEquiv {A : Matrix n n ℝ} (hA : A.PosDef) :
    EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n :=
  ContinuousLinearEquiv.ofUnit
    ((hA.cfcSqrt.isUnit.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ))).unit)

/-- The endomorphism underlying `sqrtEquiv` is the Euclidean realization of the matrix square
root. -/
@[simp]
theorem sqrtEquiv_toContinuousLinearMap {A : Matrix n n ℝ} (hA : A.PosDef) :
    hA.sqrtEquiv.toContinuousLinearMap =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) (CFC.sqrt A) := by
  exact (hA.cfcSqrt.isUnit.map (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ))).unit_spec

/-- The Euclidean square-root equivalence is self-adjoint. -/
theorem sqrtEquiv_isSelfAdjoint {A : Matrix n n ℝ} (hA : A.PosDef) :
    IsSelfAdjoint hA.sqrtEquiv.toContinuousLinearMap := by
  rw [hA.sqrtEquiv_toContinuousLinearMap]
  exact hA.cfcSqrt.isHermitian.isSelfAdjoint.map Matrix.toEuclideanCLM

/-- Squaring the Euclidean square-root equivalence gives the Euclidean realization of the
original matrix. -/
theorem sqrtEquiv_sq {A : Matrix n n ℝ} (hA : A.PosDef) :
    hA.sqrtEquiv.toContinuousLinearMap ^ 2 =
      (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A := by
  rw [hA.sqrtEquiv_toContinuousLinearMap, ← map_pow,
    CFC.sq_sqrt A hA.posSemidef.nonneg]

/-- The original positive-definite matrix is the pushforward of the identity by its positive
square-root equivalence. -/
theorem sqrtEquiv_pushforward_one {A : Matrix n n ℝ} (hA : A.PosDef) :
    (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A =
      hA.sqrtEquiv.toContinuousLinearMap.pushforward 1 := by
  rw [ContinuousLinearMap.pushforward_one, hA.sqrtEquiv_isSelfAdjoint.adjoint_eq]
  rw [← hA.sqrtEquiv_sq]
  simp [pow_two, ContinuousLinearMap.mul_def]

/-- The inverse square-root coordinate change normalizes the original matrix to the identity. -/
theorem sqrtEquiv_symm_pushforward {A : Matrix n n ℝ} (hA : A.PosDef) :
    hA.sqrtEquiv.symm.toContinuousLinearMap.pushforward
        ((Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ)) A) = 1 := by
  rw [hA.sqrtEquiv_pushforward_one]
  exact ContinuousLinearEquiv.symm_pushforward_pushforward_one hA.sqrtEquiv

end Matrix.PosDef
