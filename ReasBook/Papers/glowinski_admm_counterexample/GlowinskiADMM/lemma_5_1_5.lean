module

public import glowinski_admm_counterexample.GlowinskiADMM.lemma_5_1_4

@[expose] public section

/- Lemma 5.1.5: strict finite projection-cycle data with a nonzero residual admit
smooth strongly convex real objectives whose unit-penalty consensus ADMM trajectory
reproduces the prescribed cycle and its exact minimal period, has positive constant
objective value and globally unique block minimizers, and has `(0, 0, 0)` as its
unique KKT triple with optimal value zero. -/
#check ConsensusADMM.IsStrictProjectionCycle.smoothStronglyConvexRealization
