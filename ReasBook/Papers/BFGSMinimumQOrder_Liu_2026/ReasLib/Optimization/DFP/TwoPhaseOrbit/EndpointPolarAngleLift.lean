module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointPolarAngle

public section

open scoped EuclideanSpace

namespace DFP.TwoPhaseOrbit

/-- The recursively unwrapped real lift of the endpoint polar angles about `C`. -/
noncomputable def endpointPolarAngleLift (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) : ℕ → ℝ
  | 0 => (orbit.endpointPolarAngle C 0).toReal
  | k + 1 => orbit.endpointPolarAngleLift C k +
      (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal

/-- The endpoint polar-angle lift starts at the canonical representative of the zeroth angle. -/
theorem endpointPolarAngleLift_zero (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) :
    orbit.endpointPolarAngleLift C 0 = (orbit.endpointPolarAngle C 0).toReal := by
  rw [endpointPolarAngleLift.eq_1]

/-- The endpoint polar-angle lift advances by the canonical representative of the next angle gap. -/
theorem endpointPolarAngleLift_succ (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointPolarAngleLift C (k + 1) = orbit.endpointPolarAngleLift C k +
      (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal := by
  rw [endpointPolarAngleLift.eq_2]

/-- Consecutive lifted values differ by the canonical real representative of the
quotient-angle gap. -/
theorem endpointPolarAngleLift_succ_sub (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointPolarAngleLift C (k + 1) - orbit.endpointPolarAngleLift C k =
      (orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal := by
  rw [endpointPolarAngleLift_succ]
  ring

/-- Coercing an unwrapped endpoint polar angle recovers its quotient-valued angle. -/
theorem endpointPolarAngleLift_coe (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    (orbit.endpointPolarAngleLift C k : Real.Angle) = orbit.endpointPolarAngle C k := by
  induction k with
  | zero =>
      rw [endpointPolarAngleLift_zero]
      exact Real.Angle.coe_toReal _
  | succ k ih =>
      rw [endpointPolarAngleLift_succ]
      change (orbit.endpointPolarAngleLift C k : Real.Angle) +
        (((orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k).toReal : ℝ) :
          Real.Angle) = _
      rw [ih, Real.Angle.coe_toReal]
      abel

/-- In the local signed-angle interval, the recursive increment is the unique representative
of the corresponding quotient-valued endpoint-angle gap. -/
theorem endpointPolarAngleLift_succ_sub_unique (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) (δ : ℝ)
    (hδ : δ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (δ : Real.Angle) =
        orbit.endpointPolarAngle C (k + 1) - orbit.endpointPolarAngle C k ↔
      δ = orbit.endpointPolarAngleLift C (k + 1) - orbit.endpointPolarAngleLift C k := by
  rw [endpointPolarAngleLift_succ_sub]
  constructor
  · intro h
    have hre := congrArg Real.Angle.toReal h
    rw [Real.Angle.toReal_coe_eq_self_iff.mpr (by
      constructor <;> linarith [hδ.1, hδ.2, Real.pi_pos])] at hre
    exact hre
  · rintro rfl
    exact Real.Angle.coe_toReal _

end DFP.TwoPhaseOrbit
