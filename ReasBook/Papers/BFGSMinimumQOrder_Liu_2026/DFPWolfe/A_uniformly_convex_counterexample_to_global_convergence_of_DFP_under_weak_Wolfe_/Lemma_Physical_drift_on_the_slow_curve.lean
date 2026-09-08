module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_20_Amplitude_drift_on_the_slow_curve
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_21_Frame_rotation_on_the_slow_curve
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_22_Full_cycle_center_drift
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_23_Half_cycle_center_displacement
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_24_Leading_within_cycle_endpoint_gradient_angle_increments
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_20a_Uniform_amplitude_drift_remainder
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_22a_Uniform_full_cycle_center_drift_remainder
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_23a_Uniform_half_cycle_center_displacement_bound
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_3_24a_Uniform_within_cycle_endpoint_gradient_angle_remainders

/- Lemma (Physical drift on the slow curve) (1): amplitude drift along the
exact orbit on the invariant slow curve. -/
#check slowCurveAmplitudeDrift

/- Lemma (Physical drift on the slow curve) (2): unwrapped frame rotation
along the exact orbit on the invariant slow curve. -/
#check slowCurveFrameRotation

/- Lemma (Physical drift on the slow curve) (3): full-cycle center drift in
the physical low-unit-vector direction. -/
#check slowCurveFullCenterDrift

/- Lemma (Physical drift on the slow curve) (4): half-cycle center
displacement along the exact orbit. -/
#check slowCurveHalfCenterDisplacement

/- Lemma (Physical drift on the slow curve) (5): first within-cycle endpoint
gradient-angle increment. -/
#check slowCurveFirstEndpointAngleIncrement

/- Lemma (Physical drift on the slow curve) (6): second within-cycle endpoint
gradient-angle increment. -/
#check slowCurveSecondEndpointAngleIncrement

/- Lemma (Physical drift on the slow curve) (7): uniform physical amplitude-drift remainder along exact slow-curve orbits. -/
#check DFP.TwoPhaseOrbit.slowCurveAmplitudeDriftModulus

/- Lemma (Physical drift on the slow curve) (8): uniform physical full-cycle center-drift remainder. -/
#check DFP.TwoPhaseOrbit.slowCurveFullCenterDriftBound

/- Lemma (Physical drift on the slow curve) (9): uniform physical half-cycle center-displacement bound. -/
#check DFP.TwoPhaseOrbit.slowCurveHalfCenterDisplacementBound

/- Lemma (Physical drift on the slow curve) (10): uniform physical endpoint-gradient angle remainders. -/
#check DFP.TwoPhaseOrbit.slowCurveEndpointAngleRemainderModulus
