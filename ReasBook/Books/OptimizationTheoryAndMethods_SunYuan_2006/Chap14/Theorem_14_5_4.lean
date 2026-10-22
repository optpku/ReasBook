/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_5_3

noncomputable section

section

variable {n : ℕ}

open Chapter14

local notation "Point" => Chapter14.Point n

/-- Chapter14 Theorem 14.5.4: let `method` be a run of Algorithm 14.5.3. Assume the same
convexity, open-sublevel-set, bounded-subgradient, and shifted-iterate-value lower-boundedness
hypotheses as in Chapter14 Theorem 14.5.2. Then the bundle method terminates in finitely many
iterations in the source sense: there exists a positive integer `k` such that
`method.isEpsilonOptimalAt k`. -/
theorem exists_epsilonOptimal_stage_of_convexOn_of_bounded_subgradient_on_open_sublevelSet
    (method : BundleMethod n)
    (C : ℝ)
    (h_convex : ConvexOn ℝ Set.univ method.objective)
    {U : Set Point}
    (hU_open : IsOpen U)
    (h_initialSublevel_subset :
      method.objective ⁻¹' Set.Iic (method.objective method.initialPoint) ⊆ U)
    (h_subgradient_bound :
      ∀ ⦃z ξ : Point⦄,
        z ∈ U →
        IsSubgradientAt method.objective z ξ →
          ‖ξ‖ ≤ C)
    (h_shifted_values_bddBelow :
      BddBelow (Set.range (method.objective ∘ method.shiftedIterate))) :
    ∃ k : ℕ, 1 ≤ k ∧ method.isEpsilonOptimalAt k := sorry

end
