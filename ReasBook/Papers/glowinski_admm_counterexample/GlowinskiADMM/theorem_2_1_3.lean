/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.ConsensusADMM.Period48.Counterexamples

@[expose] public section

namespace ConsensusADMM

/- Theorem 2.1.3 (1): fixed compact convex polytopes give exact-period
counterexamples for every multiplier factor at least `criticalFactor`. -/
#check ConsensusADMM.fixedPolytopes

/- Theorem 2.1.3 (2): at `criticalFactor`, smooth strongly convex objectives
with globally Lipschitz derivatives admit a period-`48` consensus ADMM
trajectory of constant positive objective value, while the origin is their
unique primal optimum of value zero and forms a KKT triple. -/
#check ConsensusADMM.smoothCounterexample

/- Theorem 2.1.3 (3): finite closed convex piecewise-quadratic objectives at
`criticalFactor` admit a period-`48` consensus ADMM trajectory of constant
positive objective value, while the origin is KKT and has optimal value zero. -/
#check ConsensusADMM.periodicPiecewiseQuadratic

/- Theorem 2.1.3 (4): a distinct pair of finite closed convex
piecewise-quadratic objectives gives geometric residual and objective growth. -/
#check ConsensusADMM.growingPiecewiseQuadratic

end ConsensusADMM
