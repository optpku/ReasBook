module

public import ReasLib.Optimization.DFP.TwoPhaseControls.AmplitudeJet

public section

noncomputable section

open Filter
open scoped Topology

export DFP.TwoLeg (slowGraphAmplitudeJet slowGraphAmplitudeRemainder)

/- Appendix Proposition A.6b (Weighted amplitude jet): after substituting the
polynomial slow graph, the normalized amplitude has the displayed expansion
with local remainder `O(ε ^ 8)`. -/
#check (DFP.TwoLeg.slowGraphAmplitudeRemainder :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).amplitudeRatio -
        (1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8))

/- The same expansion gives the complete order-seven finite Taylor jet. -/
#check (DFP.TwoLeg.slowGraphAmplitudeJet :
    FiniteTaylorJet.ofFunction ℝ 7
        (fun ε : ℝ ↦
          (DFP.TwoLeg.observableMap
            (DFP.TwoLeg.slowGraphJetPath ε)).amplitudeRatio) 0 =
      FiniteTaylorJet.ofFunction ℝ 7
        (fun ε : ℝ ↦
          1 - (13 / 2) * ε ^ 4 + (116 / 5) * ε ^ 6 - (976 / 5) * ε ^ 7) 0)
