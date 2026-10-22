/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_/Lemma_4_8d_Center_tail_perturbation_from_gradient_directions_to_physical_endpoin_GradientAngleLift.lean
-/

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
