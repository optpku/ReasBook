/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_14

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Helper for Exercise 7.8: if `C` is equal to its polar set, then every point of `C` has norm at
most `1`. -/
lemma norm_le_one_of_mem_of_polarSet_eq_self {C : Set 𝓗} {x : 𝓗} (hx : x ∈ C) (hC : Cᵒ⊙ = C) :
    ‖x‖ ≤ 1 := by
  -- Rewrite `x ∈ C` as `x ∈ Cᵒ⊙`, so the polar inequality can be applied to `x` itself.
  have hxpolar : x ∈ Cᵒ⊙ := by
    simpa [hC] using hx
  have hxx : ⟪x, x⟫_ℝ ≤ 1 :=
    (mem_polarSet_iff_forall_inner_le_one.mp hxpolar) x hx
  -- Convert the self-inner-product bound into the desired norm bound.
  have hnormsq : ‖x‖ ^ 2 ≤ 1 := by
    simpa [real_inner_self_eq_norm_sq] using hxx
  exact (sq_le_one_iff₀ (norm_nonneg _)).mp hnormsq

/-- Helper for Exercise 7.8: if `C` is contained in the closed unit ball, then the closed unit ball
is contained in the polar set of `C`. -/
lemma closedBall_zero_one_subset_polarSet_of_subset_closedBall_zero_one (C : Set 𝓗)
    (hCball : C ⊆ Metric.closedBall (0 : 𝓗) 1) :
    Metric.closedBall (0 : 𝓗) 1 ⊆ Cᵒ⊙ := by
  intro y hy
  rw [mem_polarSet_iff_forall_inner_le_one]
  intro x hx
  -- Both vectors have norm at most `1`, so Cauchy-Schwarz yields the polar inequality.
  have hxnorm : ‖x‖ ≤ 1 := by
    exact mem_closedBall_zero_iff.mp (hCball hx)
  have hynorm : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
  calc
    ⟪x, y⟫_ℝ ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
    _ ≤ 1 * 1 := by
      exact mul_le_mul hxnorm hynorm (norm_nonneg _) zero_le_one
    _ = 1 := by norm_num

/-- Helper for Exercise 7.8: if `C` is equal to its polar set, then the closed unit ball is
contained in `C`. -/
lemma closedBall_zero_one_subset_of_polarSet_eq_self (C : Set 𝓗) (hC : Cᵒ⊙ = C) :
    Metric.closedBall (0 : 𝓗) 1 ⊆ C := by
  have hCball : C ⊆ Metric.closedBall (0 : 𝓗) 1 := by
    intro x hx
    -- The first inclusion comes from applying the self-polar hypothesis to points of `C`.
    exact mem_closedBall_zero_iff.mpr (norm_le_one_of_mem_of_polarSet_eq_self hx hC)
  intro y hy
  -- Any point of the closed unit ball belongs to `Cᵒ⊙`, hence to `C`.
  have hyPolar : y ∈ Cᵒ⊙ :=
    closedBall_zero_one_subset_polarSet_of_subset_closedBall_zero_one C hCball hy
  simpa [hC] using hyPolar

-- Proof sketch: first show `C ⊆ Metric.closedBall (0 : 𝓗) 1` by applying the polar-set inequality
-- to `x ∈ C = Cᵒ⊙` with itself. For the reverse inclusion, use the resulting norm bound on every
-- `x ∈ C` and Cauchy-Schwarz to prove each `y` in the closed unit ball belongs to `Cᵒ⊙ = C`.
/-- Exercise 7.8: if a subset of a real inner-product space is equal to its polar set, then it is
the closed unit ball centered at the origin. -/
theorem eq_closedBall_zero_one_of_polarSet_eq_self (C : Set 𝓗) (hC : Cᵒ⊙ = C) :
    C = Metric.closedBall (0 : 𝓗) 1 := by
  apply Set.Subset.antisymm
  · intro x hx
    -- The fixed-point hypothesis bounds the norm of every point of `C` by `1`.
    exact mem_closedBall_zero_iff.mpr (norm_le_one_of_mem_of_polarSet_eq_self hx hC)
  · -- Route correction: prove the reverse inclusion via `Metric.closedBall (0 : 𝓗) 1 ⊆ Cᵒ⊙ = C`,
    -- rather than by introducing a separate self-polarity proof for the unit ball.
    exact closedBall_zero_one_subset_of_polarSet_eq_self C hC

end

end Set
