module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement

public section

open Filter
open scoped Topology

export DFP.TwoPhaseOrbit (slowCurveHalfCenterDisplacement)

/- Lemma 3.23 (Half-cycle center displacement): along every sufficiently small
exact orbit on the invariant slow curve, the change from the cycle-boundary
center to the intermediate center is `O(G_j * ε_j ^ 3)` as `j → ∞`. -/
#check (DFP.TwoPhaseOrbit.slowCurveHalfCenterDisplacement :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      (fun j : ℕ ↦ ‖(orbit.state j).halfCenterDisplacement‖) =O[atTop]
        (fun j : ℕ ↦ (orbit.state j).amplitude * (orbit.state j).ε ^ 3))
