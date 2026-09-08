module

public import ReasLib.Optimization.DFP.TwoPhaseControls.Observables

/- Appendix Definition A.6a (Observable package for complete two-leg data):
the exact evaluator of the normalized two-leg observables and its projection identities. -/
#check (DFP.TwoLeg.observableMap :
  (ℝ × ℝ × ℝ) → DFP.TwoLeg.CompleteTwoLegObservables)
#check DFP.TwoLeg.CompleteTwoLegObservables
#check DFP.TwoLeg.observableMap_amplitudeRatio
#check DFP.TwoLeg.observableMap_frameAngleIncrement
#check DFP.TwoLeg.observableMap_centerDisplacements
#check DFP.TwoLeg.observableMap_endpointAngleIncrements
#check DFP.TwoLeg.observableMap_stepNorms
#check DFP.TwoLeg.observableMap_gradientNorms
