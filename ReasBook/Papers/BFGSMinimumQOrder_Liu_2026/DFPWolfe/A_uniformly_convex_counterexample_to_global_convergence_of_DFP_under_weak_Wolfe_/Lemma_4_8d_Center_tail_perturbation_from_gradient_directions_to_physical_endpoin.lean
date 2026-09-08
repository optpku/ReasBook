module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_4b_Uniform_endpoint_gradient_norm_bounds_in_both_phases
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_7a_Uniform_center_tail_bounds_over_all_sufficiently_small_initial_scales
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_8c1_Compatible_real_lifts_of_the_physical_endpoint_polar_angles
public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Lemma_4_8d_Center_tail_perturbation_from_gradient_directions_to_physical_endpoin_GradientAngleLift
public import ReasLib.Geometry.Euclidean.Angle.Oriented.Perturbation
public import ReasLib.Optimization.DFP.TwoPhaseOrbit.PolarGradientAngleError

public section

/- Lemma 4.8d (Center-tail perturbation from gradient directions to physical endpoint angles)
(1): one constant, uniform in the initial scale, cycle, and endpoint phase, bounds the
lifted polar-to-gradient angle error by `ε_j ^ 3`. -/
#check DFP.TwoPhaseOrbit.slowCurvePolarGradientAngleErrorUniform

/- Lemma 4.8d (Center-tail perturbation from gradient directions to physical endpoint angles)
(2): in each endpoint phase, the lifted polar-to-gradient angle error is
`O(ε_j ^ 3)` along the slow-curve orbit. -/
#check DFP.TwoPhaseOrbit.slowCurvePolarGradientAngleErrorIsBigO

/- Lemma 4.8d (Center-tail perturbation from gradient directions to physical endpoint angles)
(3): in each endpoint phase, the lifted polar-to-gradient angle error is
`o(ε_j ^ 2)` along the slow-curve orbit. -/
#check DFP.TwoPhaseOrbit.slowCurvePolarGradientAngleErrorIsLittleO
