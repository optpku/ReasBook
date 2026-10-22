/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Assumption_6_1_extra_2

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain-style sampling for this threshold lemma:
-- * `TrustRegionSubproblem` in `Definition_6_1_extra_1` is the Chapter 6 owner of the quadratic
--   trust-region model and its step-space data.
-- * `TrustRegionSubproblem.cauchyPoint` and related Cauchy-step API in
--   `Definition_6_1_extra_3` are derived subproblem data, not primitive fields of the algorithm.
-- * `TrustRegionSubproblem.isApproximateSolution` in `Lemma_6_1_5` is the canonical Step 3
--   predicate on a subproblem.
-- * `TrustRegionAlgorithm` in `Algorithm_6_1_1` is the Chapter 6 owner of the iteration data and
--   derives `q^(k)` from `subproblem k` instead of storing a parallel local wheel.
-- For this file, the source-facing item is the threshold theorem below; the core/canonical
-- owners are the existing Chapter 6 algorithm and subproblem declarations; there is no new
-- bridge/view data to package here.

namespace TrustRegionAlgorithm

/-- Chapter06 Lemma 6.1.7: under Assumption `(A₀)` and a positive tolerance `A.ε`, there is a
threshold `Δ̃ > 0` such that every active iteration `k` with `A.activeAt k` and
`A.Δ k < Δ̃` is very successful and satisfies `A.Δ k ≤ A.Δ (k + 1)`. -/
theorem existsVerySuccessfulThreshold_ofTrustRegionAssumptionA0
    {f : Point → ℝ} (A : TrustRegionAlgorithm n f)
    [TrustRegionAssumptionA0 f A.x0 A.subproblem A.s]
    (hε : 0 < A.ε) :
    ∃ deltaTilde > 0,
      ∀ k : ℕ,
        A.activeAt k →
        A.Δ k < deltaTilde →
        A.verySuccessfulAt k ∧ A.Δ k ≤ A.Δ (k + 1) := sorry

/-- Any threshold witness for Lemma `6.1.7` yields very success at each active iteration whose
radius is below the threshold. -/
theorem verySuccessfulAt_of_smallRadius
    {f : Point → ℝ} {A : TrustRegionAlgorithm n f} {deltaTilde : ℝ}
    (hthreshold :
      ∀ k : ℕ,
        A.activeAt k →
        A.Δ k < deltaTilde →
        A.verySuccessfulAt k ∧ A.Δ k ≤ A.Δ (k + 1))
    {k : ℕ} (hk : A.activeAt k) (hΔ : A.Δ k < deltaTilde) :
    A.verySuccessfulAt k :=
  (hthreshold k hk hΔ).1

/-- Any threshold witness for Lemma `6.1.7` also yields the monotonicity
`A.Δ k ≤ A.Δ (k + 1)` at each active iteration whose radius is below the threshold. -/
theorem radius_le_next_of_smallRadius
    {f : Point → ℝ} {A : TrustRegionAlgorithm n f} {deltaTilde : ℝ}
    (hthreshold :
      ∀ k : ℕ,
        A.activeAt k →
        A.Δ k < deltaTilde →
        A.verySuccessfulAt k ∧ A.Δ k ≤ A.Δ (k + 1))
    {k : ℕ} (hk : A.activeAt k) (hΔ : A.Δ k < deltaTilde) :
    A.Δ k ≤ A.Δ (k + 1) :=
  (hthreshold k hk hΔ).2

end TrustRegionAlgorithm
