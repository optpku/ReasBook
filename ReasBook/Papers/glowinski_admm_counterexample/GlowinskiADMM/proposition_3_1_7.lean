module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.EndpointLower
public import glowinski_admm_counterexample.GlowinskiADMM.lemma_3_1_5
public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_2_ConvergenceEndpoint

@[expose] public section

namespace ADMM

/-- Proposition 3.1.7: The uniform-convergence endpoint is strictly greater than
`377 / 200`. -/
theorem uniformConvergenceEndpoint_gt :
    (377 : ℝ) / 200 < uniformConvergenceEndpoint := by
  exact EndpointLower.endpoint_gt

end ADMM
