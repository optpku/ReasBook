/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.Projection.Minimal

-- Semantic recall hits verified for this item:
-- `exists_norm_eq_iInf_of_complete_convex`, `norm_eq_iInf_iff_real_inner_le_zero`.

section Theorem1320

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- Chapter01 Theorem 1.3.20 (1). If `S` is a nonempty, closed, convex subset of a complete real
inner product space, then for every `y` there exists a unique point `xbar ∈ S` with minimal
distance from `y`, formalized as `‖y - xbar‖ = ⨅ x : S, ‖y - x‖`. This is the intrinsic owner
abstraction of the textbook `ℝ^n` statement, and the source hypothesis `y ∉ S` is redundant for
this canonical nearest-point formulation. -/
theorem existsUnique_norm_eq_iInf_of_nonempty_isClosed_convex
    (S : Set F) (hS_nonempty : S.Nonempty) (hS_closed : IsClosed S) (hS_convex : Convex ℝ S)
    (y : F) :
    ∃! xbar : F, xbar ∈ S ∧ ‖y - xbar‖ = ⨅ x : S, ‖y - x‖ := by
  rcases
      exists_norm_eq_iInf_of_complete_convex hS_nonempty hS_closed.isComplete hS_convex y with
    ⟨xbar, hxbar, hxbar_min⟩
  refine ⟨xbar, ⟨hxbar, hxbar_min⟩, ?_⟩
  intro z hz
  rcases hz with ⟨hz_mem, hz_min⟩
  have hxbar_char :
      ∀ x ∈ S, inner ℝ (y - xbar) (x - xbar) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hS_convex hxbar).mp hxbar_min
  have hz_char :
      ∀ x ∈ S, inner ℝ (y - z) (x - z) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hS_convex hz_mem).mp hz_min
  have hxbar_le : inner ℝ (y - xbar) (z - xbar) ≤ 0 := hxbar_char z hz_mem
  have hz_ge : 0 ≤ inner ℝ (y - z) (z - xbar) := by
    have hz_le : inner ℝ (y - z) (xbar - z) ≤ 0 := hz_char xbar hxbar
    have hneg : 0 ≤ -inner ℝ (y - z) (xbar - z) := neg_nonneg.mpr hz_le
    have hsub : z - xbar = -(xbar - z) := by abel_nf
    calc
      0 ≤ -inner ℝ (y - z) (xbar - z) := hneg
      _ = inner ℝ (y - z) (-(xbar - z)) := by rw [← inner_neg_right]
      _ = inner ℝ (y - z) (z - xbar) := by rw [hsub]
  have hnorm : ‖z - xbar‖ ^ 2 ≤ 0 := by
    have hrewrite :
        inner ℝ (y - z) (z - xbar) =
          inner ℝ (y - xbar) (z - xbar) - ‖z - xbar‖ ^ 2 := by
      calc
        inner ℝ (y - z) (z - xbar)
          = inner ℝ ((y - xbar) - (z - xbar)) (z - xbar) := by abel_nf
        _ = inner ℝ (y - xbar) (z - xbar) - inner ℝ (z - xbar) (z - xbar) := by
          rw [inner_sub_left]
        _ = inner ℝ (y - xbar) (z - xbar) - ‖z - xbar‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
    linarith
  have hsq : ‖z - xbar‖ ^ 2 = 0 := le_antisymm hnorm (sq_nonneg ‖z - xbar‖)
  have hnorm_zero : ‖z - xbar‖ = 0 := by
    exact mul_self_eq_zero.mp (by simpa [sq] using hsq)
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm_zero)

/- Chapter01 Theorem 1.3.20 (2): this is exactly the canonical mathlib minimizer
characterization for convex subsets of a real inner product space. -/

#check norm_eq_iInf_iff_real_inner_le_zero

end Theorem1320
