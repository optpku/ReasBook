/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_5_First_order_amplitude_tail.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_3_Tail_estimates_for_fourth_and_sixth_powers
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_4_Positive_limiting_gradient_amplitude
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.AmplitudeTail

public section

open Filter
open scoped Asymptotics Topology

export DFP.TwoPhaseOrbit (slowCurveAmplitudeAsymptotics)

/- Lemma 4.5 (First-order amplitude tail), equation `eq:G-tail`: every sufficiently
small positive canonical slow-curve orbit has a positive limiting amplitude whose
excess is asymptotic to `(13 / 3) * Glim * ε`. -/
#check (DFP.TwoPhaseOrbit.slowCurveAmplitudeAsymptotics :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar > 0, ∀ ε₀ ∈ Set.Ioc 0 εbar,
      let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
      ∃ Glim > 0,
        Tendsto (fun j : ℕ ↦ (orbit.state j).amplitude) atTop (𝓝 Glim) ∧
          (fun j : ℕ ↦ (orbit.state j).amplitude - Glim) ~[atTop]
            (fun j : ℕ ↦ (13 / 3 : ℝ) * Glim * (orbit.state j).ε))
