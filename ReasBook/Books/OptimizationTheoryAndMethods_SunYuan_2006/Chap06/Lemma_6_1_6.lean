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

-- Domain-style sampling for this model-error lemma:
-- * `TrustRegionAlgorithm` in `Algorithm_6_1_1` is the Chapter 6 owner of the iteration data,
--   and the stage-`k` quadratic model is the derived owner `A.subproblem k`.
-- * `TrustRegionSubproblem.actualReduction` and `TrustRegionSubproblem.predictedReduction` in
--   `Definition_6_1_extra_1` are the canonical Chapter 6 owners for the trust-region agreement
--   numerator, so the model-error lemma should use that owner surface rather than a parallel
--   expanded difference `f (x_k + s_k) - q^(k) (s_k)`.
-- * `TrustRegionAssumptionA0` in `Assumption_6_1_extra_2` is the source-facing Chapter 6
--   regularity package, and `TrustRegionAssumptionA0.hessianBound_nonneg` is its canonical
--   derived API extracting the nonnegative uniform Hessian-operator-norm bound from `(A₀)`.
-- * The Chapter 1 / mathlib remainder owner relevant here is the first-order differentiability
--   remainder `HasFDerivAt.isLittleO`, not the convex-segment Hölder/Lipschitz owner used for
--   stronger remainder estimates on convex sets.
-- This theorem is therefore source-facing, with `TrustRegionAlgorithm` and the Chapter 6
-- reduction owners as the core owners and no parallel local wrapper around the quadratic model.

namespace TrustRegionAlgorithm

/-- Chapter06 Lemma 6.1.6: under Assumption `(A₀)` for a Chapter 6 trust-region algorithm `A`,
there exist `hessianBound ≥ 0` and `C : ℝ → ℝ` with
`Filter.Tendsto C (nhds 0) (nhds 0)` such that, at every active iteration `k`, the actual and
predicted reductions of the canonical stage subproblem differ by at most
`(1 / 2) * hessianBound * ‖A.s k‖^2 + C ‖A.s k‖ * ‖A.s k‖`. The active-iteration hypothesis is
the canonical Chapter 6 owner-side condition under which the algorithm fixes the stage-`k`
subproblem data and the Step 3 trial step. -/
theorem trustRegionQuadraticModelErrorBound
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s] :
    ∃ hessianBound : ℝ,
      0 ≤ hessianBound ∧
        ∃ C : ℝ → ℝ,
          Tendsto C (nhds 0) (nhds 0) ∧
            ∀ ⦃k : ℕ⦄,
              A.activeAt k →
              |TrustRegionSubproblem.actualReduction (A k) f (A.s k) -
                  (A.subproblem k).predictedReduction (A.s k)| ≤
                (1 / 2 : ℝ) * hessianBound * ‖A.s k‖ ^ (2 : ℕ) + C ‖A.s k‖ * ‖A.s k‖ := sorry

end TrustRegionAlgorithm

#print axioms TrustRegionAlgorithm.trustRegionQuadraticModelErrorBound
