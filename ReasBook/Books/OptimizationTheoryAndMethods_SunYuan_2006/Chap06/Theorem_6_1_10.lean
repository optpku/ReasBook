/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Assumption_6_1_extra_2

noncomputable section

open Filter

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace TrustRegionAlgorithm

/-- Chapter06 Theorem 6.1.10: suppose that Assumption `(A₀)` holds. Then the gradient sequence of
Algorithm `6.1.1` converges to `0`, encoded as `Tendsto A.g atTop (nhds (0 : Point))`. The
book's infinite-sequence reading is recorded explicitly by the extra hypotheses `hε : A.ε = 0`
and `hStutter : ∀ k, A.terminatedAt k → A.g (k + 1) = A.g k`, rather than being hidden inside a
stronger algorithm wrapper. -/
theorem tendsto_gradient_zero
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s]
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.g (k + 1) = A.g k) :
    Tendsto A.g atTop (nhds (0 : Point)) := sorry

/-- Under the source exact-stopping and post-termination stuttering hypotheses, the gradient norms
in Theorem `6.1.10` also converge to `0`. -/
theorem tendsto_gradientNorm_zero
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s]
    (hε : A.ε = 0)
    (hStutter : ∀ k : ℕ, A.terminatedAt k → A.g (k + 1) = A.g k) :
    Tendsto A.gradientNormAt atTop (nhds 0) := by
  change Tendsto (fun k : ℕ ↦ ‖A.g k‖) atTop (nhds 0)
  simpa using (A.tendsto_gradient_zero hε hStutter).norm

end TrustRegionAlgorithm
