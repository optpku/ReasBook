/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_3_15_Existence_of_a_local_C_7_invariant_slow_curve.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

noncomputable section

open Filter
open scoped Topology

export DFP.TwoLeg (exists_localForwardInvariantSlowCurve)

/- Lemma 3.15 (Existence of a local $C^7$ invariant slow curve): the analytic
two-leg map has a locally forward-invariant `C^7` graph through `(0, 2, 1)` that
is tangent to the `ε`-axis, has the displayed order-five graph jets, and induces
the displayed order-six recurrence for `ε`. -/
#check (DFP.TwoLeg.exists_localForwardInvariantSlowCurve :
    ∃ p h : ℝ → ℝ,
      ContDiffAt ℝ 7 (fun ε ↦ (p ε, h ε)) 0 ∧
        (p 0, h 0) = (2, 1) ∧
          HasFDerivAt (fun ε ↦ (p ε, h ε)) (0 : ℝ →L[ℝ] (ℝ × ℝ)) 0 ∧
            (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
              (fun ε ↦
                let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
                (ε', p ε', h ε')) ∧
              (fun ε : ℝ ↦
                p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
                (fun ε : ℝ ↦ ε ^ 5) ∧
                (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
                  (fun ε : ℝ ↦ ε ^ 5) ∧
                  (fun ε : ℝ ↦
                    (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1 -
                      (ε - (3 / 2) * ε ^ 4 + (5 / 4) * ε ^ 5)) =O[𝓝 0]
                    (fun ε : ℝ ↦ ε ^ 6))
