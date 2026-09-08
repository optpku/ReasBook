module

public import ReasLib.Optimization.DFP.TwoPhaseControls.FlatSliceJets.StateJetCommonDomain

public section

/-!
# Axiom-clean closure of the joint DFP state jet

This post-`StateJet` facade exposes the exact joint zero-jet statement using the
scale-stationarity proof chain, without routing through the older scalar jet declarations.
-/

noncomputable section

namespace DFP.TwoLeg.StateJet

/-- The joint normalized-radius and transverse residual has zero Taylor jet through order four,
with the scalar leaves discharged by scale stationarity. -/
theorem weightedStateJet_via_scaleStationarity
    (θ : (ℝ × ℝ) × (ℝ × ℝ)) :
    FiniteTaylorJet.ofFunction ℝ 4 (remainder θ) 0 =
      FiniteTaylorJet.ofFunction ℝ 4
        (fun _ : ℝ ↦ ((0, 0, 0) : ℝ × ℝ × ℝ)) 0 := by
  have hremainder : remainder θ = DFP.TwoLeg.StateJetAssembly.jointResidual θ := by
    funext ε
    rw [remainder_apply, DFP.TwoLeg.StateJetAssembly.jointResidual_apply]
  rw [hremainder]
  exact DFP.TwoLeg.StateJetAssembly.weightedJointResidualJet_via_scaleStationarity θ

end DFP.TwoLeg.StateJet
