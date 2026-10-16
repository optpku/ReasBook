module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_2_ConvergenceEndpoint

@[expose] public section

/- Definition 2.1.5 (1): `ADMM.UniformConvergenceAt γ` requires the rank-free
convergence conclusions for every admissible exact trajectory and convergence to
a KKT triple when both constraint matrices have full column rank. Rank-free image
convergence is an additional conclusion and is not part of this predicate. -/
#check ADMM.UniformConvergenceAt
#check ADMM.uniformConvergenceAt_iff

/- Definition 2.1.5 (2): `ADMM.uniformConvergenceEndpoint` is the supremum of
positive endpoints whose strict positive prefixes satisfy uniform convergence. -/
#check ADMM.uniformConvergenceEndpoint
#check ADMM.uniformConvergenceEndpoint_def
