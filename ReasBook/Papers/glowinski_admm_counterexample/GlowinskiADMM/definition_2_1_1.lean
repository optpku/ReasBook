module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.Trajectory

@[expose] public section

/- Definition 2.1.1 (1): the KKT set and its three defining conditions. -/
#check ADMM.Problem.kktSet
#check ADMM.Problem.isKKT_iff

/- Definition 2.1.1 (2): the optimal value of the constrained problem. -/
#check ADMM.Problem.optimalValue

/- Definition 2.1.1 (3): the primal residual `A (x k) + B (y k) - b`. -/
#check ADMM.Trajectory.primalResidual_apply

/- Definition 2.1.1 (4): the second-block increment `B (y k - y (k - 1))` for `1 ≤ k`. -/
#check ADMM.Trajectory.secondIncrement_apply

/- Definition 2.1.1 (5): a well-defined exact trajectory has finite attained block minima
at every step and obeys the multiplier update. Its initialization and all choices among
minimizers are arbitrary; nonemptiness of the KKT set does not imply block attainment. -/
#check ADMM.Trajectory.spec
