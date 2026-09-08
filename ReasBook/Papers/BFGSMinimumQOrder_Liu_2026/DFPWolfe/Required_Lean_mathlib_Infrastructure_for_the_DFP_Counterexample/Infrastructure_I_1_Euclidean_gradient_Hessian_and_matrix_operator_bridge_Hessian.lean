module

public import ReasLib.Analysis.Calculus.EuclideanPlaneHessian

/- Compatibility bridge for the Euclidean-plane operator-valued Hessian. -/
#check (EuclideanPlane.hessian :
  (EuclideanSpace ℝ (Fin 2) → ℝ) → EuclideanSpace ℝ (Fin 2) →
    EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2))
