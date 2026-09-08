module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement

public section

open Filter
open scoped Topology

export DFP.TwoPhaseOrbit (slowCurveFullCenterDrift)

/- Lemma 3.22 (Full-cycle center drift): along every sufficiently small exact
orbit on the invariant slow curve, one physical cycle changes the center by
`-(116 / 5) * G_j * ε_j ^ 6` times the physical low unit eigenvector, with
vector remainder `O(G_j * ε_j ^ 7)`. -/
#check (DFP.TwoPhaseOrbit.slowCurveFullCenterDrift :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Ccenter > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        let s := orbit.state j
        ‖(orbit.state (j + 1)).center - s.center +
          ((116 / 5) * s.amplitude * s.ε ^ 6) • s.lowVector‖ ≤
            Ccenter * s.amplitude * s.ε ^ 7)
