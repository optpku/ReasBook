module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FrameAngleJet

public section

open Filter
open scoped Topology

/- Appendix Proposition A.6c (Weighted frame-angle jet): along the polynomial
slow-graph path, the local real cycle-frame increment is
`-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6 + O(ε ^ 7)`. -/
#check (DFP.TwoLeg.slowGraphFrameAngleRemainder :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).frameAngleIncrement -
        (-3 * ε ^ 2 - (196 / 5) * ε ^ 5 + (28 / 5) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7))
