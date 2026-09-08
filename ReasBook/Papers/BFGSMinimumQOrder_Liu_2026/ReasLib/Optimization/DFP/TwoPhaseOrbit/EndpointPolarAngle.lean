module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Geometry.Euclidean.Plane.Rotation
import all ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/-- The oriented angle from the first standard basis vector to an endpoint displacement. -/
noncomputable def endpointPolarAngle (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) : Real.Angle :=
  EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    (orbit.endpoint k - C)

/-- The endpoint polar angle is the oriented angle from the first standard basis vector. -/
theorem endpointPolarAngle_def (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointPolarAngle C k =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (orbit.endpoint k - C) := by
  rfl

/-- The polar angle at an even index is the angle of the corresponding boundary endpoint. -/
theorem endpointPolarAngle_even (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    orbit.endpointPolarAngle C (2 * j) =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        ((orbit.state j).point - C) := by
  rw [endpointPolarAngle, endpoint_even]

/-- The polar angle at an odd index is the angle of the corresponding middle endpoint. -/
theorem endpointPolarAngle_odd (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    orbit.endpointPolarAngle C (2 * j + 1) =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        ((orbit.state j).middlePoint - C) := by
  rw [endpointPolarAngle, endpoint_odd]

/-- A nonzero endpoint displacement is reconstructed from its norm and polar angle. -/
theorem endpointPolarAngle_spec (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) (hne : orbit.endpoint k - C ≠ 0) :
    orbit.endpoint k - C =
      ‖orbit.endpoint k - C‖ •
        EuclideanPlane.rotation (orbit.endpointPolarAngle C k)
          (EuclideanSpace.basisFun (Fin 2) ℝ 0) := by
  let e : EuclideanSpace ℝ (Fin 2) := EuclideanSpace.basisFun (Fin 2) ℝ 0
  have he : e ≠ 0 := by
    intro h
    have h0 := congrArg (fun v : EuclideanSpace ℝ (Fin 2) ↦ v 0) h
    simp [e] at h0
  have hnorme : ‖e‖ = 1 := by
    simp [e]
  have hperpCoord :
      EuclideanPlane.orientation.rightAngleRotation e =
        (!₂[(0 : ℝ), 1] : EuclideanSpace ℝ (Fin 2)) := by
    change EuclideanPlane.perp e = _
    rw [EuclideanPlane.perp_apply]
    simp [e]
  have hpolar :=
    (EuclideanPlane.orientation.oangle_eq_iff_eq_norm_div_norm_smul_rotation_of_ne_zero
      he hne (orbit.endpointPolarAngle C k)).mp rfl
  have hpolar' : orbit.endpoint k - C =
      ‖orbit.endpoint k - C‖ •
        EuclideanPlane.orientation.rotation (orbit.endpointPolarAngle C k) e := by
    simpa [hnorme] using hpolar
  rw [Orientation.rotation_apply, hperpCoord] at hpolar'
  rw [EuclideanPlane.rotation_apply, EuclideanPlane.perp_apply]
  simpa [e] using hpolar'

end DFP.TwoPhaseOrbit
