module

public import DFPWolfe.A_uniformly_convex_counterexample_to_global_convergence_of_DFP_under_weak_Wolfe_.Definition_4_8b_Limiting_circle_and_endpoint_closed_set_candidate_EndpointSet

/- Definition 4.8b (Limiting circle and endpoint closed-set candidate):
`limitCircle C G` is the affine unit circle Γ, and `orbit.closedSetCandidate C G`
is Γ together with the range of the flattened endpoint sequence. -/
#check DFP.TwoPhaseOrbit.limitCircle
#check DFP.TwoPhaseOrbit.mem_limitCircle
#check DFP.TwoPhaseOrbit.limitCircle_eq_sphere
#check DFP.TwoPhaseOrbit.closedSetCandidate
#check DFP.TwoPhaseOrbit.mem_closedSetCandidate
#check DFP.TwoPhaseOrbit.isClosed_closedSetCandidate
