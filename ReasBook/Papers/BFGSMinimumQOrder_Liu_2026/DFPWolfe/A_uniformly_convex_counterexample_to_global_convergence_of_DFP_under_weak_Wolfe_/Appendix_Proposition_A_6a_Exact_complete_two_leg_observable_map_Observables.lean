/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_6a_Exact_complete_two_leg_observable_map_Observables.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables

#check (DFP.TwoLeg.observableMap :
  (ℝ × ℝ × ℝ) → DFP.TwoLeg.CompleteTwoLegObservables)
