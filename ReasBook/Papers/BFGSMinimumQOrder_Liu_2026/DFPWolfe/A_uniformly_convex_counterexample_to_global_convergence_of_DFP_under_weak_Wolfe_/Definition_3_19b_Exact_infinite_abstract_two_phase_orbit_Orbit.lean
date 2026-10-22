/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Definition_3_19b_Exact_infinite_abstract_two_phase_orbit_Orbit.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit

public section

open Filter
open scoped Topology

/- The exact planar two-phase orbit obtained from an invariant slow curve. -/
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
