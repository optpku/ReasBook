/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_48
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_51

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology Pointwise

universe u

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [NormedSpace ℝ 𝓗] [FiniteDimensional ℝ 𝓗]

omit [FiniteDimensional ℝ 𝓗] in
/-- Helper for Corollary 6.52: a bounded convex set has no nonzero recession direction. -/
lemma eq_zero_of_mem_recessionCone_of_bounded {C : Set 𝓗}
    (hC_nonempty : C.Nonempty) (hC_bounded : Bornology.IsBounded C) (hC_convex : Convex ℝ C)
    {x : 𝓗} (hx : x ∈ rec C) : x = 0 := by
  rcases hC_nonempty with ⟨y, hy⟩
  rcases isBounded_iff_forall_norm_le.mp hC_bounded with ⟨R, hR⟩
  by_contra hx_ne
  have hx_norm_pos : 0 < ‖x‖ := norm_pos_iff.mpr hx_ne
  obtain ⟨n, hn⟩ := exists_nat_gt ((R + ‖y‖) / ‖x‖)
  have hn' : (R + ‖y‖) / ‖x‖ < (n : ℝ) := by
    exact_mod_cast hn
  have hray_mem : ((n : ℝ) • x + y) ∈ C :=
    nat_ray_point_mem_of_mem_recessionCone hC_convex hx hy n
  have hbounded_ray : ‖(n : ℝ) • x + y‖ ≤ R := hR _ hray_mem
  have htriangle : ‖(n : ℝ) • x‖ ≤ ‖(n : ℝ) • x + y‖ + ‖y‖ := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      norm_sub_le ((n : ℝ) • x + y) y
  have hscaled_norm : ‖(n : ℝ) • x‖ = (n : ℝ) * ‖x‖ := by
    simpa using norm_smul (n : ℝ) x
  have hlarge : R + ‖y‖ < (n : ℝ) * ‖x‖ := by
    exact (div_lt_iff₀ hx_norm_pos).mp hn'
  have hlower : R < ‖(n : ℝ) • x + y‖ := by
    have htriangle' : (n : ℝ) * ‖x‖ ≤ ‖(n : ℝ) • x + y‖ + ‖y‖ := by
      simpa [hscaled_norm] using htriangle
    linarith
  exact (not_lt_of_ge hbounded_ray) hlower

omit [NormedSpace ℝ 𝓗] [FiniteDimensional ℝ 𝓗] in
/-- Helper for Corollary 6.52: an unbounded set contains points with norms above every `n + 1`. -/
lemma exists_seq_mem_norm_gt_nat_succ_of_not_bounded {C : Set 𝓗}
    (hC_unbounded : ¬ Bornology.IsBounded C) :
    ∃ x : ℕ → 𝓗, (∀ n, x n ∈ C) ∧ ∀ n, (((n + 1 : ℕ) : ℝ)) < ‖x n‖ := by
  have hlarge : ∀ R : ℝ, ∃ z : 𝓗, z ∈ C ∧ R < ‖z‖ := by
    intro R
    by_contra hR
    apply hC_unbounded
    refine isBounded_iff_forall_norm_le.mpr ?_
    refine ⟨R, ?_⟩
    intro z hz
    by_contra hzR
    exact hR ⟨z, hz, lt_of_not_ge hzR⟩
  choose x hxC hxnorm using fun n : ℕ ↦ hlarge (((n + 1 : ℕ) : ℝ))
  exact ⟨x, hxC, hxnorm⟩

omit [NormedSpace ℝ 𝓗] [FiniteDimensional ℝ 𝓗] in
/-- Helper for Corollary 6.52: reciprocal norms converge to `0` once the norms dominate `n + 1`. -/
lemma tendsto_zero_inv_norm_of_norm_ge_nat_succ {z : ℕ → 𝓗}
    (hz : ∀ n, (((n + 1 : ℕ) : ℝ)) ≤ ‖z n‖) :
    Tendsto (fun n ↦ ‖z n‖⁻¹) atTop (𝓝 (0 : ℝ)) := by
  have htail : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)⁻¹) atTop (𝓝 (0 : ℝ)) := by
    have hshift : Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
    simpa [one_div] using (tendsto_inv_atTop_zero.comp hshift)
  refine squeeze_zero' (Eventually.of_forall fun n ↦ inv_nonneg.mpr (norm_nonneg _)) ?_ htail
  filter_upwards with n
  have hnat_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast Nat.succ_pos n
  have hnorm_pos : 0 < ‖z n‖ := lt_of_lt_of_le hnat_pos (hz n)
  have hinv : ‖z n‖⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := by
    simpa [Nat.cast_add] using (inv_le_inv₀ hnorm_pos hnat_pos).mpr (hz n)
  simpa [one_div] using hinv

-- Proof sketch: if `C` is bounded and `x ∈ rec C`, then for any `c ∈ C` the whole ray
-- `fun t : ℝ ↦ c + t • x` stays in `C`, so boundedness forces `x = 0`. Conversely, if `C` is
-- unbounded, choose a sequence in `C` with norms tending to infinity; finite dimensionality gives
-- a convergent subsequence of the normalized vectors, whose nonzero limit belongs to `rec C` by
-- Proposition 6.51, so `rec C ≠ {0}`.
/-- Corollary 6.52: for a nonempty closed convex subset `C` of a finite-dimensional real normed
space, `C` is bounded if and only if its recession cone is the singleton `{0}`. -/
theorem bounded_iff_recessionCone_eq_singleton_zero_of_nonempty_isClosed_convex
    (C : Set 𝓗) (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    Bornology.IsBounded C ↔ rec C = ({0} : Set 𝓗) := by
  constructor
  · intro hC_bounded
    ext x
    constructor
    · intro hx
      -- A bounded set admits only the zero recession direction.
      simpa using eq_zero_of_mem_recessionCone_of_bounded hC_nonempty hC_bounded hC_convex hx
    · intro hx
      -- The zero vector is always a recession direction.
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact zero_mem_recessionCone C
  · intro hrec
    by_contra hC_unbounded
    rcases exists_seq_mem_norm_gt_nat_succ_of_not_bounded hC_unbounded with ⟨x, hxC, hnorm_lt⟩
    let u : ℕ → 𝓗 := fun n ↦ ‖x n‖⁻¹ • x n
    have hnorm_le : ∀ n, (((n + 1 : ℕ) : ℝ)) ≤ ‖x n‖ := fun n ↦ le_of_lt (hnorm_lt n)
    letI : ProperSpace 𝓗 := FiniteDimensional.proper ℝ 𝓗
    have hu_norm : ∀ n, ‖u n‖ = 1 := by
      intro n
      have htail_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_pos n
      have hnorm_pos : 0 < ‖x n‖ := lt_of_lt_of_le htail_pos (hnorm_le n)
      have hnorm_ne : ‖x n‖ ≠ 0 := ne_of_gt hnorm_pos
      simp [u, norm_smul, hnorm_ne]
    have hu_mem : ∀ n, u n ∈ Metric.closedBall (0 : 𝓗) 1 := by
      intro n
      rw [Metric.mem_closedBall, dist_eq_norm]
      simp [hu_norm n]
    obtain ⟨y, -, φ, hφ, hφtendsto⟩ :=
      tendsto_subseq_of_bounded Metric.isBounded_closedBall hu_mem
    have hy_norm : ‖y‖ = 1 := by
      have hnorm_tendsto : Tendsto (fun n ↦ ‖u (φ n)‖) atTop (𝓝 ‖y‖) := hφtendsto.norm
      have hconst : Tendsto (fun n ↦ ‖u (φ n)‖) atTop (𝓝 (1 : ℝ)) := by
        refine tendsto_const_nhds.congr' ?_
        exact Eventually.of_forall fun n ↦ by simp [hu_norm (φ n)]
      exact tendsto_nhds_unique hnorm_tendsto hconst
    have hy_ne : y ≠ 0 := by
      intro hy_zero
      simp [hy_zero] at hy_norm
    have hnorm_subseq : ∀ n, (((n + 1 : ℕ) : ℝ)) ≤ ‖x (φ n)‖ := by
      intro n
      have hφ_le : n ≤ φ n := StrictMono.id_le hφ n
      have hstep : (((n + 1 : ℕ) : ℝ)) ≤ (((φ n + 1 : ℕ) : ℝ)) := by
        exact_mod_cast Nat.succ_le_succ hφ_le
      exact le_trans hstep (hnorm_le (φ n))
    have hα_tendsto :
        Tendsto (fun n ↦ ‖x (φ n)‖⁻¹) atTop (𝓝 (0 : ℝ)) :=
      tendsto_zero_inv_norm_of_norm_ge_nat_succ hnorm_subseq
    have hy_rec : y ∈ rec C := by
      rw [mem_recessionCone_iff]
      rintro w hw
      rcases Set.mem_add.1 hw with ⟨w', hwmem, z, hz, hwz⟩
      have hw' : w' = y := by
        simpa using hwmem
      subst w'
      subst hwz
      let v : ℕ → 𝓗 := fun n ↦ u (φ n) + (1 - ‖x (φ n)‖⁻¹) • z
      have hv_mem : ∀ n, v n ∈ C := by
        intro n
        have hα_nonneg : 0 ≤ ‖x (φ n)‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
        have hone_le_norm : (1 : ℝ) ≤ ‖x (φ n)‖ := by
          have hone_le_tail : (1 : ℝ) ≤ (((n + 1 : ℕ) : ℝ)) := by
            exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
          exact le_trans hone_le_tail (hnorm_subseq n)
        have hα_le_one : ‖x (φ n)‖⁻¹ ≤ 1 := by
          simpa [one_div] using
            one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hone_le_norm
        have hOneSub_nonneg : 0 ≤ 1 - ‖x (φ n)‖⁻¹ := by
          linarith
        have hxφ : x (φ n) ∈ C := hxC (φ n)
        have hcombo :
            ‖x (φ n)‖⁻¹ • x (φ n) + (1 - ‖x (φ n)‖⁻¹) • z ∈ C :=
          (convex_iff_add_mem.1 hC_convex) hxφ hz hα_nonneg hOneSub_nonneg (by ring)
        simpa [v, u] using hcombo
      have hOneSub_tendsto :
          Tendsto (fun n ↦ 1 - ‖x (φ n)‖⁻¹) atTop (𝓝 (1 : ℝ)) := by
        simpa using tendsto_const_nhds.sub hα_tendsto
      have hz_tendsto :
          Tendsto (fun n ↦ (1 - ‖x (φ n)‖⁻¹) • z) atTop (𝓝 z) := by
        simpa using hOneSub_tendsto.smul_const z
      have hv_tendsto : Tendsto v atTop (𝓝 (y + z)) := by
        simpa [v, u] using hφtendsto.add hz_tendsto
      have hyz_closure : y + z ∈ closure C :=
        mem_closure_of_tendsto hv_tendsto <| Filter.Eventually.of_forall hv_mem
      simpa [hC_closed.closure_eq] using hyz_closure
    have hy_zero : y = 0 := by
      have hy_singleton : y ∈ ({0} : Set 𝓗) := by
        simpa [hrec] using hy_rec
      simpa using hy_singleton
    exact hy_ne hy_zero

end

end Set
