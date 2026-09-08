module

public import ReasLib.Analysis.InnerProductSpace.SquareRootFinite
public import ReasLib.LinearAlgebra.Matrix.PosDef.Operator
public import Mathlib.Analysis.InnerProductSpace.Positive

public section

noncomputable section

universe u

open scoped MatrixOrder

namespace ContinuousLinearMap

/-- In finite-dimensional Euclidean space, a strict operator Loewner lower bound yields a
self-adjoint continuous linear equivalence whose pushforward of the identity is the operator. -/
theorem exists_sqrtEquiv_of_finiteDimensional_lowerBound
    {n : Type u} [Fintype n]
    {H : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) ≤ H) :
    ∃ L : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 := by
  classical
  let e : Matrix n n ℝ ≃⋆ₐ[ℝ]
      (EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) :=
    Matrix.toEuclideanCLM
  let A : Matrix n n ℝ := e.symm H
  have hdiff : (H - m • (1 : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n)).IsPositive :=
    (ContinuousLinearMap.le_def _ _).mp lower
  have hdiffA : (A - m • (1 : Matrix n n ℝ)).PosSemidef := by
    rw [← Matrix.isPositive_toEuclideanCLM_iff]
    change (e (A - m • (1 : Matrix n n ℝ))).IsPositive
    rw [map_sub, map_smul, map_one]
    simpa [A, e] using hdiff
  have hmatrix : m • (1 : Matrix n n ℝ) ≤ A := (Matrix.le_iff).mpr hdiffA
  obtain ⟨L, hL, hLA⟩ := Matrix.PosDef.exists_sqrtEquiv_of_loewner_lowerBound hm hmatrix
  refine ⟨L, hL, ?_⟩
  simpa [A, e] using hLA

/-- The inverse square-root coordinate change normalizes a finite-dimensional operator with a
strict Loewner lower bound to the identity. -/
theorem exists_normalizingSqrtEquiv_of_finiteDimensional_lowerBound
    {n : Type u} [Fintype n]
    {H : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n} {m : ℝ} (hm : 0 < m)
    (lower : m • (1 : EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) ≤ H) :
    ∃ L : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        H = L.toContinuousLinearMap.pushforward 1 ∧
          L.symm.toContinuousLinearMap.pushforward H = 1 := by
  obtain ⟨L, hL, hH⟩ := exists_sqrtEquiv_of_finiteDimensional_lowerBound hm lower
  refine ⟨L, hL, hH, ?_⟩
  rw [hH]
  exact ContinuousLinearEquiv.symm_pushforward_pushforward_one L

end ContinuousLinearMap
