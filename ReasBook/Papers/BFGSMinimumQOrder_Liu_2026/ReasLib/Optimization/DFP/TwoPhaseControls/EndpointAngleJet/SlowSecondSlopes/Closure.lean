module

public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondSlopes.Intermediate
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondSlopes.Final
public import ReasLib.Optimization.DFP.TwoPhaseControls.EndpointAngleJet.SlowSecondReduction

public section

/-!
# Closure of the slow second-endpoint angle jet

This module combines the independently proved intermediate- and final-slope
remainders through the scalar reduction theorem.
-/

open Filter
open Asymptotics
open scoped Topology

namespace DFP.TwoLeg.EndpointAngleJet

/-- Along the slow-graph path, the canonical real lift of the second
endpoint-gradient angle increment has the required sixth-order polynomial and
a seventh-order remainder. -/
theorem slowSecondRemainder :
    (fun ε : ℝ ↦
      (DFP.TwoLeg.observableMap
        (DFP.TwoLeg.slowGraphJetPath ε)).secondEndpointAngleIncrement.toReal -
        (-ε ^ 2 - (104 / 5) * ε ^ 5 + (71 / 15) * ε ^ 6)) =O[𝓝 0]
      (fun ε : ℝ ↦ ε ^ 7) := by
  exact slowSecond_of_slope_remainders slowIntermediateSlope_remainder
    slowFinalSlopeRemainder

end EndpointAngleJet
end TwoLeg
end DFP
