module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterTailUniform
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradient
public import ReasLib.Optimization.DFP.TwoPhaseControls

public section

noncomputable section

namespace DFP.TwoPhaseOrbit

/-!
# Basic endpoint-correction interfaces

This companion records the algebraic endpoint, correction, radius, and parity
bridges independently of the quantitative decay theorems in the parent module.
-/

/-- The endpoint center attached to a flattened endpoint. -/
def endpointCenterBasic (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    EuclideanSpace ℝ (Fin 2) :=
  orbit.endpoint k - orbit.endpointGradient k

/-- The endpoint-center definition unfolds to endpoint minus endpoint gradient. -/
theorem endpointCenter_defBasic (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointCenterBasic k = orbit.endpoint k - orbit.endpointGradient k := by
  rfl

/-- The endpoint center at an even index is the cycle-boundary center. -/
theorem endpointCenter_evenBasic (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointCenterBasic (2 * j) = (orbit.state j).center := by
  rw [endpointCenter_defBasic, endpoint_even, endpointGradient_even, State.center_def]

/-- The endpoint center at an odd index is the intermediate center. -/
theorem endpointCenter_oddBasic (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointCenterBasic (2 * j + 1) = (orbit.state j).middleCenter := by
  rw [endpointCenter_defBasic, endpoint_odd, endpointGradient_odd,
    State.middleCenter_def]

/-- The endpoint correction attached to a chosen center and flattened endpoint. -/
def endpointCorrectionBasic (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) : EuclideanSpace ℝ (Fin 2) :=
  orbit.endpointGradient k - (orbit.endpoint k - C)

/-- The endpoint-correction definition unfolds to gradient minus endpoint plus center. -/
theorem endpointCorrection_defBasic (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointCorrectionBasic C k = orbit.endpointGradient k - (orbit.endpoint k - C) := by
  rfl

/-- Endpoint correction is the chosen center minus the endpoint center. -/
theorem endpointCorrection_eq_centerBasic (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (k : ℕ) :
    orbit.endpointCorrectionBasic C k = C - orbit.endpointCenterBasic k := by
  rw [endpointCorrection_defBasic, endpointCenter_defBasic]
  abel

/-- The endpoint correction at an even index is the chosen center minus the
cycle-boundary center. -/
theorem endpointCorrection_evenBasic (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    orbit.endpointCorrectionBasic C (2 * j) = C - (orbit.state j).center := by
  rw [endpointCorrection_eq_centerBasic, endpointCenter_evenBasic]

/-- The endpoint correction at an odd index is the chosen center minus the
intermediate center. -/
theorem endpointCorrection_oddBasic (orbit : DFP.TwoPhaseOrbit)
    (C : EuclideanSpace ℝ (Fin 2)) (j : ℕ) :
    orbit.endpointCorrectionBasic C (2 * j + 1) = C - (orbit.state j).middleCenter := by
  rw [endpointCorrection_eq_centerBasic, endpointCenter_oddBasic]

/-- The squared cycle scale attached to a flattened endpoint. -/
def endpointRadiusBasic (orbit : DFP.TwoPhaseOrbit) (k : ℕ) : ℝ :=
  TwoPhaseControls.radius (orbit.state (k / 2)).ε

/-- The endpoint-radius definition unfolds to the radius of the corresponding
cycle state. -/
theorem endpointRadius_defBasic (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    orbit.endpointRadiusBasic k = (orbit.state (k / 2)).ε ^ 2 := by
  rw [endpointRadiusBasic, TwoPhaseControls.radius_def]

/-- The endpoint radius at an even index is the square of the cycle scale. -/
theorem endpointRadius_evenBasic (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointRadiusBasic (2 * j) = (orbit.state j).ε ^ 2 := by
  rw [endpointRadius_defBasic]
  have hdiv : (2 * j) / 2 = j := by
    omega
  rw [hdiv]

/-- The endpoint radius at an odd index is the square of the cycle scale. -/
theorem endpointRadius_oddBasic (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointRadiusBasic (2 * j + 1) = (orbit.state j).ε ^ 2 := by
  rw [endpointRadius_defBasic]
  have hdiv : (2 * j + 1) / 2 = j := by
    omega
  rw [hdiv]

/-- The cube of a cycle scale equals that scale times its endpoint radius. -/
theorem endpointScale_mul_radiusBasic (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    (orbit.state (k / 2)).ε ^ 3 =
      (orbit.state (k / 2)).ε * orbit.endpointRadiusBasic k := by
  rw [endpointRadius_defBasic]
  ring

end DFP.TwoPhaseOrbit
