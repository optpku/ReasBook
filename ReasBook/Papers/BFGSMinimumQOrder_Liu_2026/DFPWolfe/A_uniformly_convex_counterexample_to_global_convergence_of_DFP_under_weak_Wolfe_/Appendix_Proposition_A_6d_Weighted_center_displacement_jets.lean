module

public import ReasLib.Optimization.DFP.TwoPhaseControls.CenterJet

public section

open Filter
open scoped Topology

#check (DFP.TwoLeg.CenterJet.slowFullLow :
  FiniteTaylorJet.ofFunction ℝ 7
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).fullCenterDisplacement 0) 0 =
    FiniteTaylorJet.ofFunction ℝ 7
      (fun ε : ℝ ↦ -(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7) 0)

#check (DFP.TwoLeg.CenterJet.slowFullHigh :
  FiniteTaylorJet.ofFunction ℝ 8
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).fullCenterDisplacement 1) 0 =
    FiniteTaylorJet.ofFunction ℝ 8
      (fun ε : ℝ ↦ -(508 / 5) * ε ^ 8) 0)

#check (DFP.TwoLeg.CenterJet.slowHalfLow :
  FiniteTaylorJet.ofFunction ℝ 3
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).halfCenterDisplacement 0) 0 =
    FiniteTaylorJet.ofFunction ℝ 3 (fun ε : ℝ ↦ 2 * ε ^ 3) 0)

#check (DFP.TwoLeg.CenterJet.slowHalfHigh :
  FiniteTaylorJet.ofFunction ℝ 5
      (fun ε : ℝ ↦
        (DFP.TwoLeg.observableMap
          (DFP.TwoLeg.slowGraphJetPath ε)).halfCenterDisplacement 1) 0 =
    FiniteTaylorJet.ofFunction ℝ 5 (fun ε : ℝ ↦ 2 * ε ^ 5) 0)

/- Appendix Proposition A.6d (Weighted center-displacement jets) (1):
low full-cycle coordinate. -/
#check (DFP.TwoLeg.CenterJet.slowFullLowRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 0 -
        (-(116 / 5) * ε ^ 6 + (38 / 5) * ε ^ 7)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 8))

/- Appendix Proposition A.6d (Weighted center-displacement jets) (2):
high full-cycle coordinate. -/
#check (DFP.TwoLeg.CenterJet.slowFullHighRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).fullCenterDisplacement 1 -
        (-(508 / 5) * ε ^ 8)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 9))

/- Appendix Proposition A.6d (Weighted center-displacement jets) (3):
low first-leg coordinate. -/
#check (DFP.TwoLeg.CenterJet.slowHalfLowRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).halfCenterDisplacement 0 -
        2 * ε ^ 3) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3))

/- Appendix Proposition A.6d (Weighted center-displacement jets) (4):
high first-leg coordinate. -/
#check (DFP.TwoLeg.CenterJet.slowHalfHighRemainder :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).halfCenterDisplacement 1 -
        2 * ε ^ 5) =o[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 5))

#check (DFP.TwoLeg.CenterJet.slowHalfBound :
  ∀ (p h : ℝ → ℝ),
    ((fun ε : ℝ ↦
      p ε - (2 + (198 / 5) * ε ^ 3 - (9 / 5) * ε ^ 4)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    ((fun ε : ℝ ↦ h ε - (1 + 8 * ε ^ 3)) =O[𝓝 0]
        (fun ε : ℝ ↦ ε ^ 5)) →
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap (ε, p ε, h ε)).halfCenterDisplacement) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 3))
