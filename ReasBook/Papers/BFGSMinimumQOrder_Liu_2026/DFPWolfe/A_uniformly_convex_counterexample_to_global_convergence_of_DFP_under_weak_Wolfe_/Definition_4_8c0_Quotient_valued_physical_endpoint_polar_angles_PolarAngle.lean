module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngle

public section

noncomputable section

open scoped EuclideanSpace

/- Definition 4.8c0 (Quotient-valued physical endpoint polar angles) (2):
the canonical quotient-valued oriented angle assigned to every endpoint displacement. -/
#check (DFP.TwoPhaseOrbit.endpointPolarAngle :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ), Real.Angle)

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_def :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpointPolarAngle C k =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (orbit.endpoint k - C))

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_even :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    orbit.endpointPolarAngle C (2 * j) =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        ((orbit.state j).point - C))

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_odd :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ),
    orbit.endpointPolarAngle C (2 * j + 1) =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        ((orbit.state j).middlePoint - C))

#check (DFP.TwoPhaseOrbit.endpointPolarAngle_spec :
  ∀ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ),
    orbit.endpoint k - C ≠ 0 →
      orbit.endpoint k - C =
        ‖orbit.endpoint k - C‖ •
          EuclideanPlane.rotation (orbit.endpointPolarAngle C k)
            (EuclideanSpace.basisFun (Fin 2) ℝ 0))
