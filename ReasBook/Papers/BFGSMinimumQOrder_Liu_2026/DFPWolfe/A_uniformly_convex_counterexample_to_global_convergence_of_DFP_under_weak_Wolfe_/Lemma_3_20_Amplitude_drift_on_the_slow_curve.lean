/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_20_Amplitude_drift_on_the_slow_curve.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet

public section

open Filter
open scoped Topology

export DFP.TwoLeg (slowCurveAmplitudeDrift)

/- Lemma 3.20 (Amplitude drift on the slow curve): on an invariant slow graph
with the fixed shape jets, the normalized amplitude multiplier for one two-leg
cycle is `1 - (13 / 2) * ε ^ 4 + O(ε ^ 6)`. -/
#check (DFP.TwoLeg.slowCurveAmplitudeDrift :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 6))
