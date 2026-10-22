/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_18

-- Theorem-local interior-geometry helper for Lemma 13.19.

noncomputable section

open Matrix
open scoped BigOperators

namespace Lemma_13_19_InteriorWeights

/-- Helper for Lemma 13.19: a strictly positive simplex-weighted combination of the vertices lies
in the interior of the finite convex hull whenever that convex hull has nonempty interior. -/
theorem strictly_positive_stdSimplex_weighted_sum_mem_interior_convexHull
    {n l : ℕ} {a : Fin l → Fin n → ℝ} {w : Fin l → ℝ}
    (hΩ : (interior (convexHull ℝ (Set.range a))).Nonempty)
    (hw : w ∈ stdSimplex ℝ (Fin l))
    (hwPos : ∀ j, 0 < w j) :
    (∑ j, w j • a j) ∈ interior (convexHull ℝ (Set.range a)) := by
  classical
  let Ω : Set (Fin n → ℝ) := convexHull ℝ (Set.range a)
  change (interior Ω).Nonempty at hΩ
  change (∑ j, w j • a j) ∈ interior Ω
  have hl : Nonempty (Fin l) := by
    by_contra hl
    haveI : IsEmpty (Fin l) := not_nonempty_iff.mp hl
    simpa [Ω, Set.range_eq_empty a] using (interior_subset hΩ.some_mem)
  letI : Nonempty (Fin l) := hl
  let L : (Fin l → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    ∑ i, (LinearMap.proj (R := ℝ) i).smulRight (a i)
  have hL_basis : L ∘ (fun i : Fin l ↦ Pi.single i 1) = a := by
    funext i
    simp [L]
  have hΩ_image : Ω = L '' stdSimplex ℝ (Fin l) := by
    rw [← convexHull_rangle_single_eq_stdSimplex (ℝ) (Fin l),
      LinearMap.image_convexHull, ← Set.range_comp, hL_basis]
  obtain ⟨y, hyΩ⟩ := hΩ
  have hy_mem : y ∈ Ω := interior_subset hyΩ
  obtain ⟨u, hu, rfl⟩ : ∃ u, u ∈ stdSimplex ℝ (Fin l) ∧ L u = y := by
    rw [hΩ_image] at hy_mem
    simpa only [Set.mem_image] using hy_mem
  let m : ℝ := Finset.univ.inf' Finset.univ_nonempty w
  have hm_pos : 0 < m :=
    (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun j _ ↦ hwPos j
  have hm_le (j : Fin l) : m ≤ w j := Finset.inf'_le _ (Finset.mem_univ j)
  let ε : ℝ := min (m / 2) (1 / 2)
  have hε_pos : 0 < ε := by
    dsimp [ε]
    exact lt_min (half_pos hm_pos) (by norm_num)
  have hε_lt_one : ε < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hε_le_w (j : Fin l) : ε ≤ w j := by
    exact (min_le_left _ _).trans ((half_le_self hm_pos.le).trans (hm_le j))
  have hu_le_one (j : Fin l) : u j ≤ 1 := by
    rw [← hu.2]
    exact Finset.single_le_sum (fun k _ ↦ hu.1 k) (Finset.mem_univ j)
  let ρ : Fin l → ℝ := fun j ↦ w j - ε * u j
  have hρ_nonneg (j : Fin l) : 0 ≤ ρ j := by
    dsimp [ρ]
    exact sub_nonneg.mpr <| (mul_le_of_le_one_right hε_pos.le (hu_le_one j)).trans (hε_le_w j)
  have hρ_sum : ∑ j, ρ j = 1 - ε := by
    rw [show (∑ j, ρ j) = ∑ j, w j - ε * ∑ j, u j by
      simp [ρ, Finset.sum_sub_distrib, Finset.mul_sum]]
    rw [hw.2, hu.2, mul_one]
  let w' : Fin l → ℝ := fun j ↦ ρ j / (1 - ε)
  let z : Fin n → ℝ := ∑ j, w' j • a j
  have hden_pos : 0 < 1 - ε := sub_pos.mpr hε_lt_one
  have hw'_nonneg (j : Fin l) : 0 ≤ w' j := div_nonneg (hρ_nonneg j) hden_pos.le
  have hw'_sum : ∑ j, w' j = 1 := by
    calc
      ∑ j, w' j = (∑ j, ρ j) / (1 - ε) := by simp [w', Finset.sum_div]
      _ = 1 := by rw [hρ_sum]; exact div_self hden_pos.ne'
  have hzΩ : z ∈ Ω :=
    weighted_sum_mem_convexHull_range (a := a) w' hw'_nonneg hw'_sum rfl
  have hLu : L u = ∑ j, u j • a j := by
    simp [L]
  have hsplit :
      ∑ j, w j • a j = (1 - ε) • z + ε • L u := by
    rw [hLu]
    simp only [z, Finset.smul_sum, smul_smul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hrescale : (1 - ε) * w' j = ρ j := by
      dsimp [w']
      field_simp [hden_pos.ne']
    rw [hrescale]
    dsimp [ρ]
    module
  rw [hsplit]
  exact (convex_convexHull ℝ (Set.range a)).combo_self_interior_mem_interior
    hzΩ hyΩ hden_pos.le hε_pos (by ring)

end Lemma_13_19_InteriorWeights
