/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Lemma_13_6_7

noncomputable section

/-!
Chapter13 Exercise 13.6

Discuss the local convergence properties of Powell-Yuan's trust-region algorithm.

Domain sampling pass:
* primary domain: local convergence of the Chapter 13 Powell-Yuan trust-region method;
* inspected project declarations:
  `PowellYuanTrustRegionMethod`,
  `PowellYuanTrustRegionMethod.finitelyTerminates`,
  `PowellYuanTrustRegionMethod.satisfiesAssumption1362`,
  `PowellYuanTrustRegionMethod.tendsto_radius_zero_of_not_finitelyTerminates`;
* owner abstraction: `PowellYuanTrustRegionMethod`;
* source/core/bridge triage:
  - source-facing: the two local-convergence clauses of Exercise 13.6;
  - core/canonical: the Chapter 13 theorem owners in `Lemma_13_6_7.lean`;
  - bridge/view: none in this file, since the exercise is exact recall.

This is a source-facing recall item. The two local-convergence clauses already live on the
canonical Chapter 13 owner `PowellYuanTrustRegionMethod` in `Lemma_13_6_7.lean`, so this file
reuses those theorem owners directly instead of restating their telescopes through local
`example` wrappers.
-/

/- Clause (1): under Chapter 13 Assumption 13.6.2, if the Powell-Yuan trust-region run does not
terminate finitely, then the trust-region radii `Δ_k` converge to `0`, encoded on the shifted
sequence `k ↦ method.radius (k + 1)`. -/
#check PowellYuanTrustRegionMethod.tendsto_radius_zero_of_not_finitelyTerminates

/- Clause (2): under Chapter 13 Assumption 13.6.2, if the Powell-Yuan trust-region run does not
terminate finitely, then the Euclidean constraint-residual norms `‖c_k‖₂` converge to `0`,
encoded on the shifted sequence `k ↦ ‖method.constraintResidual (k + 1)‖`. -/
#check PowellYuanTrustRegionMethod.tendsto_constraintResidualNorm_zero_of_not_finitelyTerminates
