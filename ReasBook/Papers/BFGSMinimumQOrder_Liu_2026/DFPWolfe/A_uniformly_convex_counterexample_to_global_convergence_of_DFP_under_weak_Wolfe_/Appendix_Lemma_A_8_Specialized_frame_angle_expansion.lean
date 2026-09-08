module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Appendix_Proposition_A_6h_Common_domain_certificate_for_all_observable_jets
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_17_Slow_curve_shape_coefficients
public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet.Specialization

public section

open Filter
open scoped Topology

/-- Appendix Lemma A.8 (Specialized frame-angle expansion): on an invariant
slow curve with the fixed cubic and quartic shape jets, the actual curve's
frame-angle increment is
`-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6 + O(ε ^ 7)`.
This transports the polynomial calculation on `DFP.TwoLeg.slowGraphJetPath`
to explicit invariant slow-curve functions. -/
theorem slowCurveFrameAngleExpansion (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5))
    (h_hJet :
      (fun ε ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).frameAngleIncrement -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  exact DFP.TwoLeg.frameAngleExpansionOfGraphJets p h h_pJet h_hJet

/- The coefficient-uniform certificate supplies the fixed common neighborhood
on which all specialized observable-jet remainders are controlled. -/
#check DFP.TwoLeg.ObservableJet.observableJetsCommonDomain
