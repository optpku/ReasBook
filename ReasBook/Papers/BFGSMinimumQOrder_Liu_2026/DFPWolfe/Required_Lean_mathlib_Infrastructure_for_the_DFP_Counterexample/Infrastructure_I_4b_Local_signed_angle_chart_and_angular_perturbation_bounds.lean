module

public import ReasLib.Geometry.Euclidean.Angle.Oriented.Perturbation
public import ReasLib.Geometry.Euclidean.Plane.SignedAngle

open scoped EuclideanSpace
open scoped Matrix.Norms.Elementwise

/- Infrastructure I.4b (Local signed-angle chart and angular perturbation bounds) (1):
the explicit local coordinate, its branch interval, and its uniqueness for nearby rotations. -/
#check (EuclideanPlane.SignedAngle.coordinate_unique :
  ∀ (M : Matrix (Fin 2) (Fin 2) ℝ) (phi : ℝ),
    M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
      M ∈ EuclideanPlane.SignedAngle.chart →
        phi ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) →
          (EuclideanPlane.rotationMatrix phi = M ↔
            phi = EuclideanPlane.SignedAngle.coordinate M))
#check (EuclideanPlane.SignedAngle.chart : Set (Matrix (Fin 2) (Fin 2) ℝ))
#check (EuclideanPlane.SignedAngle.coordinate : Matrix (Fin 2) (Fin 2) ℝ → ℝ)
#check (EuclideanPlane.SignedAngle.coordinate_mem_interval :
  ∀ M : Matrix (Fin 2) (Fin 2) ℝ,
    EuclideanPlane.SignedAngle.coordinate M ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))

/- Infrastructure I.4b (Local signed-angle chart and angular perturbation bounds) (2):
real-analytic dependence of the signed-angle coordinate on the matrix entries. -/
#check (EuclideanPlane.SignedAngle.analyticOnNhd_coordinate :
  AnalyticOnNhd ℝ EuclideanPlane.SignedAngle.coordinate EuclideanPlane.SignedAngle.chart)

/- Infrastructure I.4b (Local signed-angle chart and angular perturbation bounds) (3):
recovery of a nearby rotation and agreement with the canonical `Real.Angle.toReal`
representative. -/
#check (EuclideanPlane.SignedAngle.rotationMatrix_coordinate :
  ∀ M : Matrix (Fin 2) (Fin 2) ℝ,
    M ∈ Matrix.specialOrthogonalGroup (Fin 2) ℝ →
      M ∈ EuclideanPlane.SignedAngle.chart →
        EuclideanPlane.rotationMatrix (EuclideanPlane.SignedAngle.coordinate M) = M)
#check (EuclideanPlane.SignedAngle.coordinate_rotationMatrix_toReal :
  ∀ theta : Real.Angle,
    theta.toReal ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) →
      EuclideanPlane.SignedAngle.coordinate (EuclideanPlane.rotationMatrix theta) = theta.toReal)

/- Infrastructure I.4b (Local signed-angle chart and angular perturbation bounds) (4):
the quantitative local signed-angle bound for perturbing a vector by an error vector. -/
#check (Orientation.abs_toReal_oangle_add_le EuclideanPlane.orientation :
  ∀ (v e : EuclideanSpace ℝ (Fin 2)) (rho : ℝ),
    0 < rho → rho ≤ ‖v‖ → rho ≤ ‖v + e‖ →
      |(EuclideanPlane.orientation.oangle v (v + e)).toReal| ≤ Real.pi * ‖e‖ / rho)
