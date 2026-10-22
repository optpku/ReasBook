/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_6a_Exact_complete_two_leg_observable_map.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables

/- Appendix Definition A.6a (Observable package for complete two-leg data):
the exact evaluator of the normalized two-leg observables and its projection identities. -/
#check (DFP.TwoLeg.observableMap :
  (ℝ × ℝ × ℝ) → DFP.TwoLeg.CompleteTwoLegObservables)
#check DFP.TwoLeg.CompleteTwoLegObservables
#check DFP.TwoLeg.observableMap_amplitudeRatio
#check DFP.TwoLeg.observableMap_frameAngleIncrement
#check DFP.TwoLeg.observableMap_centerDisplacements
#check DFP.TwoLeg.observableMap_endpointAngleIncrements
#check DFP.TwoLeg.observableMap_stepNorms
#check DFP.TwoLeg.observableMap_gradientNorms
