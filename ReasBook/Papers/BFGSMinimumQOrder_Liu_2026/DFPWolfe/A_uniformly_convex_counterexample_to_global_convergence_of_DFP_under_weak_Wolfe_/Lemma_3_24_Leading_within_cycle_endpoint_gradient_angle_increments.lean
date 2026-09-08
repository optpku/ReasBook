module

public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.Specialization
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_11_Real_analytic_extension_of_the_complete_two_leg_map_Map

public section

open Filter
open scoped Topology

/-- Lemma 3.24 (Leading within-cycle endpoint-gradient angle increments) (1):
on an invariant slow curve with the fixed shape jets, the real lift of the
first endpoint-gradient angle increment is `-2 * ε ^ 2 + o(ε ^ 2)`. -/
theorem slowCurveFirstEndpointAngleIncrement (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).firstEndpointAngleIncrement.toReal -
        (-2 * ε ^ 2)) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
  exact DFP.TwoLeg.EndpointAngleJet.firstLeadingOfGraphJets p h h_pJet h_hJet

/-- Lemma 3.24 (Leading within-cycle endpoint-gradient angle increments) (2):
on an invariant slow curve with the fixed shape jets, the real lift of the
second endpoint-gradient angle increment is `-ε ^ 2 + o(ε ^ 2)`. -/
theorem slowCurveSecondEndpointAngleIncrement (p h : ℝ → ℝ)
    (h_invariant :
      (fun ε ↦ DFP.TwoLeg.extendedMap (ε, p ε, h ε)) =ᶠ[𝓝 0]
        (fun ε ↦
          let ε' := (DFP.TwoLeg.extendedMap (ε, p ε, h ε)).1
          (ε', p ε', h ε')))
    (h_pJet :
      (fun ε : ℝ ↦ p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5))
    (h_hJet :
      (fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).secondEndpointAngleIncrement.toReal -
        (-(ε ^ 2))) =o[𝓝 0] (fun ε : ℝ ↦ ε ^ 2) := by
  exact DFP.TwoLeg.EndpointAngleJet.secondLeadingOfGraphJets p h h_pJet h_hJet
