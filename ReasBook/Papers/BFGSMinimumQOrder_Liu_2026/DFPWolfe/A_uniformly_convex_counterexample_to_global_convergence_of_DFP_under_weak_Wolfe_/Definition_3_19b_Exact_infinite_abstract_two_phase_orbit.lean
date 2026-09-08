module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

open Filter
open scoped Topology

/- Definition 3.19b (Exact infinite abstract two-phase orbit): for every sufficiently
small positive initial scale on an invariant slow curve, the recursively generated
physical two-phase orbit is exact at every cycle. -/
#check (DFP.TwoPhaseOrbit.ofSlowCurveExact :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∀ εbar : ℝ, εbar ∈ Set.Ioo 0 (1 / 4) →
      ∃ εmax ∈ Set.Ioc 0 εbar, ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
        DFP.TwoPhaseOrbit.State.ExactCycle
          ((DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀).state j))
