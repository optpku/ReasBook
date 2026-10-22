/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_2

@[expose] public section

/- Lemma 5.1.3 (1): strictification of a projection cycle with one strict block. -/
#check ConsensusADMM.IsProjectionCycle.strictifyOneBlock

/- Lemma 5.1.3 (2): the uniform-convergence endpoint lies strictly below the cycle factor. -/
#check ConsensusADMM.IsProjectionCycle.uniformConvergenceEndpoint_lt
