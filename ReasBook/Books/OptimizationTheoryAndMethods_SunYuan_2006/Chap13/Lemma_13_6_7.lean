/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap13.Algorithm_13_6_1

noncomputable section

open Filter

section

variable {m n : ℕ}

-- Domain sampling pass:
-- * primary domain: Powell-Yuan trust-region local convergence under Chapter 13 Assumption
--   13.6.2
-- * inspected project declarations:
--   `PowellYuanTrustRegionMethod` from `Algorithm_13_6_1`
--   `PowellYuanTrustRegionMethod.satisfiesAssumption1362`
--   `PowellYuanTrustRegionMethod.finitelyTerminates`
--   `powellYuanPenaltyParameters_eventuallyConstant` from `Lemma_13_6_6`
--   `NullSpaceTrustRegionMethod.tendsto_stoppingResidual_zero_of_bounded_hessianApproximation`
--   from `Theorem_13_4_5`
-- * owner abstraction: `PowellYuanTrustRegionMethod`
-- * source/core/bridge triage:
--   - source-facing: the two local-convergence clauses of Lemma 13.6.7
--   - core/canonical: the Chapter 13 method owner `PowellYuanTrustRegionMethod`
--   - bridge/view: the Chapter 13 penalty-stabilization and stopping-residual convergence
--     machinery from `Lemma_13_6_6` and `Theorem_13_4_5`
-- * primitive data vs derived API:
--   - primitive data: the recorded run data in `PowellYuanTrustRegionMethod`
--   - derived API: `terminatedAt`, `finitelyTerminates`, and `satisfiesAssumption1362`

namespace PowellYuanTrustRegionMethod

variable (method : @_root_.PowellYuanTrustRegionMethod m n)

/-- Chapter13 Lemma 13.6.7 (1): under Chapter13 Assumption 13.6.2, if the Powell-Yuan
algorithm does not terminate finitely, then the trust-region radii `Δ_k` converge to `0`,
encoded on the shifted sequence `k ↦ method.radius (k + 1)`. -/
theorem tendsto_radius_zero_of_not_finitelyTerminates
    (h1362 : method.satisfiesAssumption1362)
    (hNoTerminate : ¬ method.finitelyTerminates)
    :
    Tendsto (fun k : ℕ ↦ method.radius (k + 1)) atTop (nhds 0) := sorry

/-- Chapter13 Lemma 13.6.7 (2): under Chapter13 Assumption 13.6.2, if the Powell-Yuan
algorithm does not terminate finitely, then the Euclidean constraint-residual norms `‖c_k‖₂`
converge to `0`, encoded on the shifted sequence
`k ↦ ‖method.constraintResidual (k + 1)‖`. -/
theorem tendsto_constraintResidualNorm_zero_of_not_finitelyTerminates
    (h1362 : method.satisfiesAssumption1362)
    (hNoTerminate : ¬ method.finitelyTerminates)
    :
    Tendsto
      (fun k : ℕ ↦ ‖method.constraintResidual (k + 1)‖)
      atTop
      (nhds 0) := sorry

end PowellYuanTrustRegionMethod

end
