module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

namespace DFP.TwoPhaseOrbit

/-- The physical gradient at endpoint `k` of a two-phase orbit, including both
cycle boundaries and intermediate first-leg endpoints. -/
noncomputable def endpointGradient (orbit : DFP.TwoPhaseOrbit) (k : ℕ) :
    EuclideanSpace ℝ (Fin 2) :=
  if k % 2 = 0 then
    (orbit.state (k / 2)).gradient
  else
    (orbit.state (k / 2)).middleGradient

/-- At an even endpoint, `endpointGradient` is the corresponding cycle-boundary
gradient. -/
@[simp]
theorem endpointGradient_even (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointGradient (2 * j) = (orbit.state j).gradient := by
  simp [endpointGradient]

/-- At an odd endpoint, `endpointGradient` is the corresponding intermediate
first-leg gradient. -/
@[simp]
theorem endpointGradient_odd (orbit : DFP.TwoPhaseOrbit) (j : ℕ) :
    orbit.endpointGradient (2 * j + 1) = (orbit.state j).middleGradient := by
  have hdiv : (2 * j + 1) / 2 = j := by
    omega
  simp [endpointGradient, hdiv]

end DFP.TwoPhaseOrbit
