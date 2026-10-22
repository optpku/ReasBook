/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Appendix_Lemma_A_9_Specialized_center_displacement_expansion.lean
-/

module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Appendix_Proposition_A_6h_Common_domain_certificate_for_all_observable_jets

/- Appendix Lemma A.9 (Specialized center-displacement expansion) (1). -/
#check DFP.TwoLeg.CenterJet.slowFullLowRemainder

/- Appendix Lemma A.9 (Specialized center-displacement expansion) (2). -/
#check DFP.TwoLeg.CenterJet.slowFullHighRemainder

/- Appendix Lemma A.9 (Specialized center-displacement expansion) (3). -/
#check observableJetsCommonDomain
