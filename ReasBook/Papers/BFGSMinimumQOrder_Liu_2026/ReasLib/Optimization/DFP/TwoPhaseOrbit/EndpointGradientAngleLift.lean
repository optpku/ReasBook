module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradient
public import ReasLib.Geometry.Euclidean.Plane.Rotation

public section

noncomputable section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/-- The oriented direction angle of the gradient at endpoint `k`. -/
noncomputable def endpointGradientAngle (orbit : DFP.TwoPhaseOrbit) (k : ℕ) : Real.Angle :=
  EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
    (orbit.endpointGradient k)

/-- The endpoint-gradient angle is measured from the first standard basis vector. -/
theorem endpointGradientAngle_def (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointGradientAngle k =
      EuclideanPlane.orientation.oangle (EuclideanSpace.basisFun (Fin 2) ℝ 0)
        (orbit.endpointGradient k) := by
  rfl

/-- The recursively unwrapped real lift of the endpoint-gradient angles. -/
noncomputable def endpointGradientAngleLift (orbit : DFP.TwoPhaseOrbit) : ℕ → ℝ
  | 0 => (orbit.endpointGradientAngle 0).toReal
  | k + 1 => orbit.endpointGradientAngleLift k +
      (orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal

/-- The endpoint-gradient lift starts at the canonical representative of the zeroth angle. -/
theorem endpointGradientAngleLift_zero (orbit : DFP.TwoPhaseOrbit) :
    orbit.endpointGradientAngleLift 0 = (orbit.endpointGradientAngle 0).toReal := by
  rw [endpointGradientAngleLift.eq_1]

/-- The endpoint-gradient lift advances by the canonical representative of the next angle gap. -/
theorem endpointGradientAngleLift_succ (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointGradientAngleLift (k + 1) = orbit.endpointGradientAngleLift k +
      (orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal := by
  rw [endpointGradientAngleLift.eq_2]

/-- Consecutive endpoint-gradient lifts differ by the canonical representative of their
quotient-angle gap. -/
theorem endpointGradientAngleLift_succ_sub (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointGradientAngleLift (k + 1) - orbit.endpointGradientAngleLift k =
      (orbit.endpointGradientAngle (k + 1) - orbit.endpointGradientAngle k).toReal := by
  rw [endpointGradientAngleLift_succ]
  ring

/-- Coercing an endpoint-gradient lift recovers its quotient-valued direction angle. -/
theorem endpointGradientAngleLift_coe (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    (orbit.endpointGradientAngleLift k : Real.Angle) = orbit.endpointGradientAngle k := by
  induction k with
  | zero =>
      rw [endpointGradientAngleLift_zero]
      exact Real.Angle.coe_toReal _
  | succ k ih =>
      rw [endpointGradientAngleLift_succ]
      change (orbit.endpointGradientAngleLift k : Real.Angle) +
        (((orbit.endpointGradientAngle (k + 1) -
          orbit.endpointGradientAngle k).toReal : ℝ) : Real.Angle) = _
      rw [ih, Real.Angle.coe_toReal]
      abel

end DFP.TwoPhaseOrbit
