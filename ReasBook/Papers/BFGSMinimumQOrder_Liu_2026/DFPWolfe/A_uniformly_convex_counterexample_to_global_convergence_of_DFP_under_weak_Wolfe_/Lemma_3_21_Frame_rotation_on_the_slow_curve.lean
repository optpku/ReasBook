/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_21_Frame_rotation_on_the_slow_curve.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.FrameAngleDrift

public section

open Filter
open scoped Topology

export DFP.TwoPhaseOrbit (slowCurveFrameRotation)

/- Lemma 3.21 (Frame rotation on the slow curve): along every sufficiently
small exact orbit on an invariant slow curve with the fixed shape jets, the
unwrapped physical frame angle advances by `-3 * ε_j ^ 2` with a uniform
fourth-order remainder. -/
#check (DFP.TwoPhaseOrbit.slowCurveFrameRotation :
  ∀ (p h : ℝ → ℝ),
    ((fun ε ↦ DFP.TwoLeg.stateMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
      (fun ε ↦
        let ε' := (DFP.TwoLeg.stateMap (ε, p ε, h ε)).1
        (ε', p ε', h ε'))) →
    ((fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5)) →
    ∃ εbar ∈ Set.Ioo (0 : ℝ) (1 / 4), ∃ Cφ > 0,
      ∀ ε₀ ∈ Set.Ioc 0 εbar, ∀ j : ℕ,
        let orbit := DFP.TwoPhaseOrbit.ofSlowCurve p h ε₀
        let εj := (orbit.state j).ε
        |orbit.frameAngle (j + 1) - orbit.frameAngle j + 3 * εj ^ 2| ≤
          Cφ * εj ^ 4)
