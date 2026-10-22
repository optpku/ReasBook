/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_23_Half_cycle_center_displacement.lean
-/

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
