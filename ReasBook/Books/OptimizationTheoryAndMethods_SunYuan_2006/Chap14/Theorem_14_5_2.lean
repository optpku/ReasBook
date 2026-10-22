/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Function
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_5_1

noncomputable section

section

variable {n : ℕ}

open Chapter14

local notation "Point" => Chapter14.Point n

/-- The common Chapter 14.5.2/14.5.4 finite-termination hypotheses: `objective` is convex,
`U` is an open neighborhood of the initial sublevel set, every subgradient on `U` has norm at
most `C`, and the shifted iterate-value sequence is bounded below. -/
def Chapter14.HasOpenSublevelTerminationHypotheses
    (objective : Point → ℝ)
    (initialPoint : Point)
    (shiftedIterate : ℕ → Point)
    (C : ℝ)
    (U : Set Point) : Prop :=
  ConvexOn ℝ Set.univ objective ∧
    IsOpen U ∧
      objective ⁻¹' Set.Iic (objective initialPoint) ⊆ U ∧
        (∀ ⦃z ξ : Point⦄,
          z ∈ U →
          IsSubgradientAt objective z ξ →
            ‖ξ‖ ≤ C) ∧
        BddBelow (Set.range (objective ∘ shiftedIterate))

/-- Unfolding `HasOpenSublevelTerminationHypotheses objective initialPoint shiftedIterate C U`
gives the Chapter 14.5.2/14.5.4 convexity, open-sublevel-set, bounded-subgradient, and
shifted-value lower-bound hypotheses. -/
theorem Chapter14.hasOpenSublevelTerminationHypotheses_iff
    (objective : Point → ℝ)
    (initialPoint : Point)
    (shiftedIterate : ℕ → Point)
    (C : ℝ)
    (U : Set Point) :
    Chapter14.HasOpenSublevelTerminationHypotheses
        objective initialPoint shiftedIterate C U ↔
      ConvexOn ℝ Set.univ objective ∧
        IsOpen U ∧
          objective ⁻¹' Set.Iic (objective initialPoint) ⊆ U ∧
            (∀ ⦃z ξ : Point⦄,
              z ∈ U →
              IsSubgradientAt objective z ξ →
                ‖ξ‖ ≤ C) ∧
            BddBelow (Set.range (objective ∘ shiftedIterate)) :=
  Iff.rfl

namespace ConjugateSubgradientMethod

/-- Under the common Chapter 14.5.2/14.5.4 convexity, open-sublevel-set, bounded-subgradient,
and shifted-value lower-bound hypotheses, Algorithm 14.5.1 reaches a stage where the stopping
test `‖d_k‖ ≤ η` holds. -/
theorem exists_stopping_stage_of_hasOpenSublevelTerminationHypotheses
    (method : ConjugateSubgradientMethod n)
    (C : ℝ)
    {U : Set Point}
    (h_term :
      Chapter14.HasOpenSublevelTerminationHypotheses
        method.objective
        method.initialPoint
        method.shiftedIterate
        C
        U) :
    ∃ k : ℕ, 1 ≤ k ∧ method.stopsAt k := by
  sorry

end ConjugateSubgradientMethod

/-- Chapter14 Theorem 14.5.2: let `method` be a run of Algorithm 14.5.1 for a convex objective.
Assume there is an open set `U` containing the initial sublevel set
`method.objective ⁻¹' Set.Iic (method.objective method.initialPoint)` on which every subgradient
of `method.objective` has norm at most `C`, and assume the shifted iterate-value sequence
`method.objective (method.shiftedIterate k)` is bounded below. Then the algorithm terminates in
finitely many iterations, i.e. there exists `k ≥ 1` with `method.stopsAt k`. -/
theorem exists_stopping_stage_of_convexOn_of_bounded_subgradient_on_open_sublevelSet
    (method : ConjugateSubgradientMethod n)
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
    ∃ k : ℕ, 1 ≤ k ∧ method.stopsAt k :=
  method.exists_stopping_stage_of_hasOpenSublevelTerminationHypotheses C
    ⟨h_convex, hU_open, h_initialSublevel_subset, h_subgradient_bound,
      h_shifted_values_bddBelow⟩

end
