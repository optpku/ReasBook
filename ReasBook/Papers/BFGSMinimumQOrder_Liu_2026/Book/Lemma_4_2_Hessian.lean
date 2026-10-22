/-
Authors: Chenyi Li
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/BFGSMinimumQOrder_Liu_2026/README.md (formalization contributor).
-/

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
