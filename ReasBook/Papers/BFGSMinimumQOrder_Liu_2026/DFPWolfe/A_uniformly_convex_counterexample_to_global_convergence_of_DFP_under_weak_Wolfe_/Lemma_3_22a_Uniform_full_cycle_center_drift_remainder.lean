/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_22a_Uniform_full_cycle_center_drift_remainder.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.CenterDisplacement
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

open Filter
open scoped Topology

/- Lemma 3.22a (Uniform full-cycle center-drift remainder) -/
#check (DFP.TwoPhaseOrbit.slowCurveFullCenterDriftBound :
  ∀ (p h : ℝ → ℝ),
    (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε')) →
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5) →
    ∀ (εbar : ℝ), εbar ∈ Set.Ioo 0 (1 / 4) →
      ∃ εmax ∈ Set.Ioc 0 εbar, ∃ Ccenter > 0,
        ∀ ε₀ ∈ Set.Ioc 0 εmax, ∀ j : ℕ,
          let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
          let s := orbit.state j
          ‖(orbit.state (j + 1)).center - s.center +
              ((116 / 5) * s.amplitude * s.ε ^ 6) • s.lowVector‖ ≤
            Ccenter * s.amplitude * s.ε ^ 7)
