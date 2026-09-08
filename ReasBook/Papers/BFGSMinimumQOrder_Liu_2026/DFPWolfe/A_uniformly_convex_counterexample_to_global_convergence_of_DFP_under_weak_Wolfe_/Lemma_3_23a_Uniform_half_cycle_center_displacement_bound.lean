module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement

public section

open Filter
open scoped Topology

/- Lemma 3.23a (Uniform half-cycle center-displacement bound): one sufficiently
small scale threshold and one positive constant control the physical half-cycle
center displacement of every smaller exact slow-curve orbit at every cycle by
its amplitude times the cube of its scale. -/
#check (DFP.TwoPhaseOrbit.slowCurveHalfCenterDisplacementBound :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Chalf > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let s := (DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j
        ‖s.halfCenterDisplacement‖ ≤ Chalf * s.amplitude * s.ε ^ 3)
