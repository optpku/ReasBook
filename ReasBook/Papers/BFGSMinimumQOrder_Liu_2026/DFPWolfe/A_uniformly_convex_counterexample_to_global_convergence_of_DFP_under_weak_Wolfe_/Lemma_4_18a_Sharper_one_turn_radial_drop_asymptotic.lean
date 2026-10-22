/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_18a_Sharper_one_turn_radial_drop_asymptotic.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.OneTurnAmplitudeDrop

public section

open Filter
open scoped Asymptotics Topology

/- Lemma 4.18a (Sharper one-turn radial-drop asymptotic): along the exact
slow-curve orbit, an ordered cofinal family of pairs whose unwrapped frame-angle
drop is within `ε_j ^ 2 / 4` of one full turn has amplitude drop asymptotic to
`(13 * Real.pi / 3) * (orbit.state j).amplitude * (orbit.state j).ε ^ 2`. -/
#check (DFP.TwoPhaseOrbit.slowCurveOneTurnAmplitudeDropAsymptotic :
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
      ∀ j ℓ : ℕ → ℕ, Tendsto j atTop atTop →
        (∀ᶠ n in atTop, j n < ℓ n) →
        (∀ᶠ n in atTop,
          |orbit.frameAngle (j n) - orbit.frameAngle (ℓ n) - 2 * Real.pi| <
            (orbit.state (j n)).ε ^ 2 / 4) →
        (fun n ↦
          (orbit.state (j n)).amplitude - (orbit.state (ℓ n)).amplitude) ~[atTop]
          (fun n ↦
            (13 * Real.pi / 3) * (orbit.state (j n)).amplitude *
              (orbit.state (j n)).ε ^ 2))
