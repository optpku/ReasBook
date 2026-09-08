module

public import ReasLib.Optimization.DFP.TwoPhaseOrbit.EndpointGradientAngleLift

public section

/- Lemma 4.8d (Center-tail perturbation from gradient directions to physical endpoint angles)
The endpoint-gradient angle and its compatible real lift are provided by the shared
two-phase-orbit API. -/
#check DFP.TwoPhaseOrbit.endpointGradientAngle
#check DFP.TwoPhaseOrbit.endpointGradientAngle_def
#check DFP.TwoPhaseOrbit.endpointGradientAngleLift
#check DFP.TwoPhaseOrbit.endpointGradientAngleLift_zero
#check DFP.TwoPhaseOrbit.endpointGradientAngleLift_succ
#check DFP.TwoPhaseOrbit.endpointGradientAngleLift_succ_sub
#check DFP.TwoPhaseOrbit.endpointGradientAngleLift_coe
