module

public import ReasLib.Analysis.Hessian

public section

/- The reusable Euclidean Hessian matrix. -/
#check (ConvexAnalysis.hessian :
  ∀ {n : ℕ}, (EuclideanSpace ℝ (Fin n) → ℝ) →
    EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)

/- The Hessian matrix represents the Fréchet derivative of the gradient. -/
#check (ConvexAnalysis.toEuclideanCLM_hessian :
  ∀ {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)),
    (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (ConvexAnalysis.hessian f x) = fderiv ℝ (gradient f) x)
