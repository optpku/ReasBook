/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_1_Asymptotic_decay_of_the_singular_scale.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.ScaleAsymptotics

public section

open Filter
open scoped Asymptotics Topology

export DFP.TwoLeg (slowCurveScaleAsymptotic)

/- Lemma 4.1 (Asymptotic decay of the singular scale): the scale along every
sufficiently small positive exact coordinate orbit on the invariant slow curve
is asymptotic to `((9 / 2) * j) ^ (-1 / 3)` at `atTop`. -/
#check (DFP.TwoLeg.slowCurveScaleAsymptotic :
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
      (fun j : ℕ ↦ (DFP.TwoLeg.stateMap^[j] (ε₀, p ε₀, h ε₀)).1) ~[atTop]
        (fun j : ℕ ↦ ((9 / 2 : ℝ) * (j : ℝ)) ^ (-(1 : ℝ) / 3)))
