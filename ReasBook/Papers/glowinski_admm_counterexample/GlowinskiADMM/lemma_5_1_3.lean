module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_2

@[expose] public section

/- Lemma 5.1.3 (1): strictification of a projection cycle with one strict block. -/
#check ConsensusADMM.IsProjectionCycle.strictifyOneBlock

/- Lemma 5.1.3 (2): the uniform-convergence endpoint lies strictly below the cycle factor. -/
#check ConsensusADMM.IsProjectionCycle.uniformConvergenceEndpoint_lt
