module

public import ReasLib.Optimization.BFGS.PlanarGradient

public section

noncomputable section

open scoped EuclideanSpace

#check
  (PlanarGradient.next EuclideanPlane.orientation :
    EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) → ℝ →
      EuclideanSpace ℝ (Fin 2))
