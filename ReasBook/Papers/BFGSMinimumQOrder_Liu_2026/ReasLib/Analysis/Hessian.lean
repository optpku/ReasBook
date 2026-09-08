module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

namespace ConvexAnalysis

/-- The Hessian matrix of a real function on Euclidean space, obtained from the Fréchet
derivative of its gradient through the Euclidean matrix equivalence. -/
noncomputable def hessian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))).symm
    (fderiv ℝ (gradient f) x)

/-- Transporting the Hessian matrix back to a continuous linear map gives the derivative of
the gradient. -/
theorem toEuclideanCLM_hessian {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) :
    (Matrix.toEuclideanCLM :
        Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
          (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (hessian f x) = fderiv ℝ (gradient f) x := by
  -- Unfold the Hessian once, reducing the claim to the equivalence round-trip law.
  simpa only [hessian] using
    (StarAlgEquiv.apply_symm_apply (Matrix.toEuclideanCLM :
      Matrix (Fin n) (Fin n) ℝ ≃⋆ₐ[ℝ]
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
      (fderiv ℝ (gradient f) x))

end ConvexAnalysis
