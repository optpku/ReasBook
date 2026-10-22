/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Proposition_A_6e_Weighted_endpoint_gradient_direction_jets.lean
-/

module

public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet

public section

open Filter
open scoped Topology

/- Appendix Proposition A.6e (Weighted endpoint-gradient direction jets), first component. -/
#check (DFP.TwoLeg.EndpointAngleJet.slowFirst :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2 - (122 / 5) * ε ^ 5 + (88 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))

/- Appendix Proposition A.6e (Weighted endpoint-gradient direction jets), second component. -/
#check (DFP.TwoLeg.EndpointAngleJet.slowSecond :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).secondEndpointAngleIncrement.toReal -
        (-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))
