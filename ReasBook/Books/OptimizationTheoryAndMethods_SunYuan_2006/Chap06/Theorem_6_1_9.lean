/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Assumption_6_1_extra_2

noncomputable section

open Filter

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/-- Chapter06 Theorem 6.1.9: let Assumption `(A₀)` hold. If Algorithm `6.1.1` has infinitely
many successful active iterations, then the gradient sequence of Algorithm `6.1.1` satisfies
`liminf_(k → ∞) ‖g_k‖ = 0`, encoded through the owner companion
`A.gradientNormAt k = ‖A.g k‖` as `liminf A.gradientNormAt atTop = 0`. -/
theorem trustRegionAlgorithm_liminf_gradientNorm_eq_zero
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s]
    (hSuccessful : A.hasInfinitelyManySuccessfulIterations) :
    liminf A.gradientNormAt atTop = 0 := sorry
