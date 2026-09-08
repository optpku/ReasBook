module

public import ReasLib.LinearAlgebra.Matrix.RealSymmetric2

/- The explicit low vector satisfies the low-eigenvalue equation for every real symmetric
`2 × 2` matrix. -/
#check (RealSymmetric2.lowVector_eigen : ∀ a b d : ℝ,
  (Matrix.toEuclideanCLM :
    Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ]
      EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
    (RealSymmetric2.matrix a b d) (RealSymmetric2.lowVector a b d) =
    RealSymmetric2.low a b d • RealSymmetric2.lowVector a b d)
