/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Lemma_A_10_Two_within_cycle_endpoint_gradient_angle_increments.lean
-/

module

import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Appendix_Proposition_A_6h_Common_domain_certificate_for_all_observable_jets

/- Appendix Lemma A.10 (Two within-cycle endpoint-gradient angle increments) (1):
the first-leg real-lifted endpoint-gradient angle increment along the slow graph. -/
#check DFP.TwoLeg.EndpointAngleJet.slowFirst

/- Appendix Lemma A.10 (Two within-cycle endpoint-gradient angle increments) (2):
the second-leg real-lifted endpoint-gradient angle increment along the slow graph. -/
#check DFP.TwoLeg.EndpointAngleJet.slowSecond

/- Appendix Lemma A.10 (Two within-cycle endpoint-gradient angle increments) (3):
the fixed common neighborhood and uniform observable-jet remainder certificate. -/
#check observableJetsCommonDomain
