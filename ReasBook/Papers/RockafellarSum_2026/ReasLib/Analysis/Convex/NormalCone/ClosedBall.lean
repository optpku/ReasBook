/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import RockafellarSum_2026.ReasLib.Analysis.Convex.NormalCone
import Mathlib.Analysis.Normed.Module.HahnBanach

/-!
# Maximal monotonicity of closed-ball normal cones

This module proves maximal monotonicity of a positive-radius closed-ball
normal cone under surjectivity of the dual-pairing map.
-/

public section

universe u v

namespace DualPairing

variable {X : Type u} {Xstar : Type v} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Xstar] [NormedSpace ℝ Xstar]

/-- The normal-cone graph of a positive-radius closed ball is maximally monotone when
the pairing map onto the strong dual is surjective. -/
theorem maximalMonotone_normalConeGraph_closedBall (P : DualPairing X Xstar)
    (h_surjective : Function.Surjective P.toDual) (r : ℝ) (hr : 0 < r) :
    Maximal P.IsMonotone (P.normalConeGraph (Metric.closedBall (0 : X) r)) := by
  -- Reduce maximality to showing that the graph equals its monotone polar.
  have hmono : P.IsMonotone (P.normalConeGraph (Metric.closedBall (0 : X) r)) :=
    P.isMonotone_normalConeGraph _
  apply (P.maximalMonotone_iff_polar_eq _ hmono).2
  apply Set.Subset.antisymm
  · intro z hz
    rcases z with ⟨x, xstar⟩
    have hpolar := (P.mem_monotonePolar _ (x, xstar)).1 hz
    -- Scaled supporting normals rule out a polar point based outside the ball.
    have hxC : x ∈ Metric.closedBall (0 : X) r := by
      by_contra hxC
      rw [mem_closedBall_zero_iff] at hxC
      have hxnorm : r < ‖x‖ := lt_of_not_ge hxC
      have hxnorm_pos : 0 < ‖x‖ := lt_of_lt_of_le hr hxnorm.le
      obtain ⟨φ, hφnorm, hφx⟩ := exists_dual_vector'' ℝ x
      obtain ⟨n, hn⟩ := h_surjective φ
      let y : X := (r / ‖x‖) • x
      -- The radial rescaling lies on the boundary and is supported by `φ`.
      have hy_norm : ‖y‖ = r := by
        dsimp [y]
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hr hxnorm_pos)]
        exact div_mul_cancel₀ r (ne_of_gt hxnorm_pos)
      have hyC : y ∈ Metric.closedBall (0 : X) r := by
        rw [mem_closedBall_zero_iff]
        exact hy_norm.le
      have hφy : φ y = r := by
        dsimp [y]
        rw [map_smul, hφx]
        exact div_mul_cancel₀ r (ne_of_gt hxnorm_pos)
      have hφ_le (u : X) (hu : u ∈ Metric.closedBall (0 : X) r) : φ u ≤ r := by
        have hu_norm : ‖u‖ ≤ r := mem_closedBall_zero_iff.mp hu
        calc
          φ u ≤ ‖φ u‖ := le_abs_self _
          _ ≤ ‖φ‖ * ‖u‖ := φ.le_opNorm u
          _ ≤ 1 * ‖u‖ := mul_le_mul_of_nonneg_right hφnorm (norm_nonneg _)
          _ ≤ 1 * r := mul_le_mul_of_nonneg_left hu_norm zero_le_one
          _ = r := one_mul _
      have hn_normal : n ∈ P.normalCone (Metric.closedBall (0 : X) r) y := by
        apply (P.mem_normalCone _ _ _).2
        refine ⟨hyC, ?_⟩
        intro u hu
        rw [P.toLinearPairing_apply, hn, map_sub]
        linarith [hφ_le u hu, hφy]
      -- Nonnegative integer multiples remain normal at the same boundary point.
      have hscaled (k : ℕ) :
          (k : ℝ) • n ∈ P.normalCone (Metric.closedBall (0 : X) r) y := by
        apply (P.mem_normalCone _ _ _).2
        refine ⟨hyC, ?_⟩
        intro u hu
        have hbase : φ (u - y) ≤ 0 := by
          simpa only [P.toLinearPairing_apply, hn] using
            ((P.mem_normalCone _ _ _).1 hn_normal).2 u hu
        rw [P.toLinearPairing_apply, map_smul, hn]
        simpa [smul_eq_mul] using
          (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg k) hbase)
      have hgraph_scaled (k : ℕ) :
          (y, (k : ℝ) • n) ∈ P.normalConeGraph (Metric.closedBall (0 : X) r) :=
        (P.mem_graph_normalCone _ _ _).2
          ((P.mem_normalCone _ _ _).1 (hscaled k))
      have hφdiff : 0 < φ (x - y) := by
        rw [map_sub, hφx, hφy]
        exact sub_pos.mpr hxnorm
      let a : ℝ := P.toDual xstar (x - y)
      let b : ℝ := φ (x - y)
      have hb : 0 < b := hφdiff
      -- Polar membership gives an affine lower bound for every natural scale.
      have hineq (k : ℕ) : 0 ≤ a - (k : ℝ) * b := by
        have hk := hpolar (y, (k : ℝ) • n) (hgraph_scaled k)
        have hdiff :
            (x, xstar) - (y, (k : ℝ) • n) =
              (x - y, xstar - (k : ℝ) • n) := by
          rfl
        rw [hdiff, P.quadratic_apply] at hk
        have hdecomp :
            P.toDual (xstar - (k : ℝ) • n) (x - y) =
              P.toDual xstar (x - y) - (k : ℝ) * φ (x - y) := by
          rw [P.toDual.map_sub, P.toDual.map_smul, hn]
          simp [smul_eq_mul]
        rw [hdecomp] at hk
        simpa [a, b] using hk
      -- An Archimedean choice of scale contradicts that lower bound because `b > 0`.
      obtain ⟨k, hk⟩ : ∃ k : ℕ, a / b < k := exists_nat_gt (a / b)
      have hkb : a < (k : ℝ) * b := by
        have hmul := mul_lt_mul_of_pos_right hk hb
        rw [div_mul_cancel₀ a (ne_of_gt hb)] at hmul
        exact hmul
      linarith [hineq k]
    -- Testing against every `(y, 0)` in the graph recovers the normal inequality.
    have hnormal : xstar ∈ P.normalCone (Metric.closedBall (0 : X) r) x := by
      apply (P.mem_normalCone _ _ _).2
      refine ⟨hxC, ?_⟩
      intro y hy
      have hzero_normal : 0 ∈ P.normalCone (Metric.closedBall (0 : X) r) y := by
        apply (P.mem_normalCone _ _ _).2
        refine ⟨hy, ?_⟩
        intro u hu
        simp
      have hzero : (y, 0) ∈ P.normalConeGraph (Metric.closedBall (0 : X) r) :=
        (P.mem_graph_normalCone _ _ _).2
          ((P.mem_normalCone _ _ _).1 hzero_normal)
      have h := hpolar (y, 0) hzero
      have hdiff : (x, xstar) - (y, 0) = (x - y, xstar) := by
        apply Prod.ext
        · rfl
        · simp
      rw [hdiff, P.quadratic_apply] at h
      rw [P.toLinearPairing_apply]
      have hmap := (P.toDual xstar).map_sub x y
      rw [hmap] at h
      have hmap' := (P.toDual xstar).map_sub y x
      rw [hmap']
      linarith
    exact (P.mem_graph_normalCone _ _ _).2
      ((P.mem_normalCone _ _ _).1 hnormal)
  -- Monotonicity supplies the reverse inclusion of the graph into its polar.
  · exact (P.isMonotone_iff_subset_polar _).mp hmono

end DualPairing
