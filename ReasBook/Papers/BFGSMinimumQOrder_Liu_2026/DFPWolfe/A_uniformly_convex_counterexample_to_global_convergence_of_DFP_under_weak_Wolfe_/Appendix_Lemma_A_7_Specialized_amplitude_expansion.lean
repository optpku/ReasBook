module

import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Appendix_Proposition_A_6b_Weighted_amplitude_jet
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Appendix_Proposition_A_6h_Common_domain_certificate_for_all_observable_jets
import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_17_Slow_curve_shape_coefficients

open Filter
open scoped Topology

/- Appendix Lemma A.7 (Specialized amplitude expansion) (1): on the invariant
slow curve, the normalized two-leg amplitude ratio has the displayed
order-seven expansion with remainder `O(ε ^ 8)`. -/
#check (DFP.TwoLeg.amplitudeRemainderOfSlowGraphJets :
  ∀ (p h : ℝ → ℝ),
    (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8))

/- Appendix Lemma A.7 (Specialized amplitude expansion) (2): the amplitude
expansion holds on the fixed common slow-curve neighborhood. -/
#check observableJetsCommonDomain

/- The specialized slow-graph path uses the uniquely solved cubic and quartic
shape coefficients. -/
#check slowGraphShapeCoefficients
