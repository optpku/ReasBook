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

/-- Helper for Exercise 7.7: every point of the closed unit ball satisfies the defining polar-set
inequality against the whole closed unit ball. -/
private theorem closedUnitBall_subset_polarSet_closedUnitBall :
    Metric.closedBall (0 : 𝓗) 1 ⊆ ((Metric.closedBall (0 : 𝓗) 1 : Set 𝓗)ᵒ⊙ : Set 𝓗) := by
  intro u hu
  rw [mem_polarSet_iff_forall_inner_le_one]
  intro x hx
  -- Rewrite both closed-ball hypotheses into the norm bounds used by Cauchy--Schwarz.
  have hu_norm : ‖u‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu
  have hx_norm : ‖x‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hx
  -- The inner product is bounded by the product of the norms, which is at most `1`.
  have hmul : ‖x‖ * ‖u‖ ≤ 1 := by
    nlinarith [norm_nonneg x, norm_nonneg u, hx_norm, hu_norm]
  exact le_trans (real_inner_le_norm x u) hmul

/-- Helper for Exercise 7.7: the normalized vector `‖u‖⁻¹ • u` lies in the closed unit ball when
`u ≠ 0`. -/
private theorem inv_norm_smul_mem_closedUnitBall {u : 𝓗} (hu : u ≠ 0) :
    ‖u‖⁻¹ • u ∈ Metric.closedBall (0 : 𝓗) 1 := by
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnorm_ne : ‖u‖ ≠ 0 := hnorm_pos.ne'
  -- Compute the norm of the normalized test vector exactly.
  have hunit : ‖‖u‖⁻¹ • u‖ = 1 := by
    calc
      ‖‖u‖⁻¹ • u‖ = |‖u‖⁻¹| * ‖u‖ := norm_smul _ _
      _ = ‖u‖⁻¹ * ‖u‖ := by
        rw [abs_of_pos (inv_pos.mpr hnorm_pos)]
      _ = 1 := by
        rw [inv_mul_cancel₀ hnorm_ne]
  -- The exact norm computation is the closed-ball membership statement at the origin.
  simp [Metric.mem_closedBall, dist_eq_norm, hunit]

/-- Helper for Exercise 7.7: pairing a nonzero vector with its normalized version recovers its
norm. -/
private theorem inner_inv_norm_smul_self {u : 𝓗} (hu : u ≠ 0) :
    ⟪‖u‖⁻¹ • u, u⟫_ℝ = ‖u‖ := by
  have hnorm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hnorm_ne : ‖u‖ ≠ 0 := hnorm_pos.ne'
  -- Rewrite the inner product into a scalar identity in `ℝ`.
  calc
    ⟪‖u‖⁻¹ • u, u⟫_ℝ = ‖u‖⁻¹ * ⟪u, u⟫_ℝ := by
      rw [real_inner_smul_left]
    _ = ‖u‖⁻¹ * ‖u‖ ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq]
    _ = ‖u‖ := by
      rw [pow_two]
      ring_nf
      field_simp [hnorm_ne]

/-- Helper for Exercise 7.7: a vector in the polar of the closed unit ball has norm at most `1`,
so it belongs to the closed unit ball. -/
private theorem polarSet_closedUnitBall_subset_closedUnitBall :
    ((Metric.closedBall (0 : 𝓗) 1 : Set 𝓗)ᵒ⊙ : Set 𝓗) ⊆ Metric.closedBall (0 : 𝓗) 1 := by
  intro u hu
  by_cases hu0 : u = 0
  · -- The zero vector is trivially in the closed unit ball.
    simp [Metric.mem_closedBall, hu0]
  · rw [mem_polarSet_iff_forall_inner_le_one] at hu
    -- Route correction: test the polar inequality on the normalized vector `‖u‖⁻¹ • u`.
    have htest_mem : ‖u‖⁻¹ • u ∈ Metric.closedBall (0 : 𝓗) 1 :=
      inv_norm_smul_mem_closedUnitBall hu0
    have hnorm_le : ‖u‖ ≤ 1 := by
      have htest := hu (‖u‖⁻¹ • u) htest_mem
      rwa [inner_inv_norm_smul_self hu0] at htest
    -- Convert the norm bound back into the closed-ball membership statement.
    simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm_le

-- Proof sketch: prove both inclusions using `mem_polarSet_iff_forall_inner_le_one`. If
-- `u ∈ Metric.closedBall (0 : 𝓗) 1`, Cauchy--Schwarz gives `⟪x, u⟫_ℝ ≤ ‖x‖ * ‖u‖ ≤ 1` for every
-- `x` in the closed unit ball, so `u` lies in the polar set. Conversely, if
-- `u ∈ (Metric.closedBall (0 : 𝓗) 1)ᵒ⊙`, test against `x = u / ‖u‖` when `u ≠ 0` to obtain
-- `‖u‖ ≤ 1`, while the case `u = 0` is immediate.
/-- Exercise 7.7: the polar set of the closed unit ball `B(0;1)` is the closed unit ball itself.
-/
theorem polarSet_closedUnitBall_eq_closedUnitBall :
    ((Metric.closedBall (0 : 𝓗) 1 : Set 𝓗)ᵒ⊙ : Set 𝓗) = Metric.closedBall (0 : 𝓗) 1 := by
  -- Prove equality by the textbook two-inclusion argument.
  apply subset_antisymm
  · exact polarSet_closedUnitBall_subset_closedUnitBall
  · exact closedUnitBall_subset_polarSet_closedUnitBall

end

end Set
