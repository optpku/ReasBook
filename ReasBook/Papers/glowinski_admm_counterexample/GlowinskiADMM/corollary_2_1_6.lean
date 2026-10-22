/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.proposition_3_1_7
public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_2_ConvergenceEndpoint
public import glowinski_admm_counterexample.GlowinskiADMM.theorem_2_1_4_ADMM

@[expose] public section

namespace ADMM

/-- Corollary 2.1.6: The uniform-convergence endpoint lies strictly between
`377 / 200` and the critical factor. -/
theorem uniformConvergenceEndpoint_bounds :
    (377 : ℝ) / 200 < uniformConvergenceEndpoint ∧
      uniformConvergenceEndpoint < ConsensusADMM.criticalFactor := by
  exact ⟨uniformConvergenceEndpoint_gt, EndpointBounds.prefix_bounded_and_endpoint_lt.2⟩

end ADMM
