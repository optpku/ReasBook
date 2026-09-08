module

public import ReasLib.LinearAlgebra.Matrix.PosDef.LowerBound
public import ReasLib.LinearAlgebra.Matrix.PosDef.Sqrt

public section

noncomputable section

universe u

open scoped MatrixOrder

namespace Matrix.PosDef

/-- In finite-dimensional Euclidean space, a strict matrix Loewner lower bound supplies the
self-adjoint invertible square-root factorization of the associated continuous operator. -/
theorem exists_sqrtEquiv_of_loewner_lowerBound
    {n : Type u} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} {m : ℝ} (hm : 0 < m)
    (h : m • (1 : Matrix n n ℝ) ≤ A) :
    ∃ L : EuclideanSpace ℝ n ≃L[ℝ] EuclideanSpace ℝ n,
      IsSelfAdjoint L.toContinuousLinearMap ∧
        ((Matrix.toEuclideanCLM :
          Matrix n n ℝ ≃⋆ₐ[ℝ] EuclideanSpace ℝ n →L[ℝ] EuclideanSpace ℝ n) A) =
          L.toContinuousLinearMap.pushforward 1 := by
  have hA : A.PosDef := Matrix.posDef_of_loewner_lowerBound hm h
  exact ⟨hA.sqrtEquiv, hA.sqrtEquiv_isSelfAdjoint, hA.sqrtEquiv_pushforward_one⟩

end Matrix.PosDef
