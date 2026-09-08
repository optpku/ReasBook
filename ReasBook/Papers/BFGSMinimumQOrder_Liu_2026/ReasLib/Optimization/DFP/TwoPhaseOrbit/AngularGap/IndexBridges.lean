module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointSet
public import Mathlib.Tactic

public section

namespace DFP.TwoPhaseOrbit.AngularGap

/-- Helper for the angular-gap index bridge: the second endpoint of the odd
phase in cycle `j` has index `2 * (j + 1)`. -/
theorem one_add_one_add_two_mul_eq_two_mul_succ (j : ℕ) :
    1 + (1 + 2 * j) = 2 * (j + 1) := by
  omega

/-- Helper for the angular-gap index bridge: the syntactic successor form of
an odd endpoint index agrees with the corresponding even cycle index. -/
theorem two_mul_add_one_add_one_eq_two_mul_succ (j : ℕ) :
    2 * j + 1 + 1 = 2 * (j + 1) := by
  omega

/-- Helper for the angular-gap orbit bridge: an endpoint expression transports
along an equality identifying a local orbit with its slow-curve orbit. -/
theorem endpoint_eq_of_orbit_eq_slowCurve
    {orbit : DFP.TwoPhaseOrbit} (p h : ℝ → ℝ) (ε₀ : ℝ)
    (horbit : orbit = DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀) (k : ℕ) :
    orbit.endpoint k = (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).endpoint k := by
  rw [horbit]

/-- Helper for the angular-gap orbit bridge: a state scale transports along
an equality identifying a local orbit with its slow-curve orbit. -/
theorem state_scale_eq_of_orbit_eq_slowCurve
    {orbit : DFP.TwoPhaseOrbit} (p h : ℝ → ℝ) (ε₀ : ℝ) (j : ℕ)
    (horbit : orbit = DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀) :
    (orbit.state j).ε =
      ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j).ε := by
  rw [horbit]

end DFP.TwoPhaseOrbit.AngularGap
