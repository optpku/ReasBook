module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_15a_Second_order_flatness_of_the_invariant_slow_graph
public import ReasLib.Optimization.DFP.TwoPhaseControls.SlowCurve.Taylor

public section

open Filter
open scoped Topology

/- Lemma 3.15b (Taylor ansatz of the invariant slow graph): a smooth graph
through `(0, 2, 1)` that is flat to second order admits cubic and quartic
coordinate expansions with residuals of order `O(ε ^ 5)`. -/
#check (DFP.TwoLeg.exists_flatGraphTaylorCoefficients :
  ∀ (p h : ℝ → ℝ),
    ContDiffAt ℝ 5 (fun ε ↦ (p ε, h ε)) 0 →
    (p 0, h 0) = (2, 1) →
    iteratedDeriv 1 p 0 = 0 →
    iteratedDeriv 1 h 0 = 0 →
    iteratedDeriv 2 p 0 = 0 →
    iteratedDeriv 2 h 0 = 0 →
    ∃ P₃ H₃ P₄ H₄ : ℝ,
      (fun ε ↦ p ε - (2 + P₃ * ε ^ 3 + P₄ * ε ^ 4)) =O[𝓝 0]
          (fun ε ↦ ε ^ 5) ∧
        (fun ε ↦ h ε - (1 + H₃ * ε ^ 3 + H₄ * ε ^ 4)) =O[𝓝 0]
          (fun ε ↦ ε ^ 5))
