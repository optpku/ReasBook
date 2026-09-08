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
