/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5_2.ch3_sec3_5_2_definition_3_5_2_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_14

open scoped Pointwise Matrix

/-- Helper for Lemma 4.50: positive `polyhedronDim` forces the matrix polyhedron
`polyhedron_le_set A b` to be nonempty. -/
lemma polyhedron_nonempty_of_pos_dim
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_dim : 0 < polyhedronDim (polyhedron_le_set A b)) :
    (polyhedron_le_set A b).Nonempty := by
  by_contra hP_empty
  have hP_dim_zero : polyhedronDim (polyhedron_le_set A b) = 0 := by
    simp [polyhedronDim, Set.not_nonempty_iff_eq_empty.mp hP_empty]
  rw [hP_dim_zero] at hP_dim
  exact Nat.lt_irrefl 0 hP_dim

/-- Bridge/view for Lemma 4.50: a polytope of positive `polyhedronDim` has strictly larger
dimension than its recession cone, so Exercise 3.14 applies directly. -/
lemma polyhedron_dim_gt_recessionConeDim_of_polytope_pos_dim
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (hP_polytope : (polyhedron_le_set A b).IsPolytope ℝ)
    (hP_dim : 0 < polyhedronDim (polyhedron_le_set A b)) :
    polyhedronDim (polyhedron_le_set A b) > recessionConeDim (polyhedron_le_set A b) := by
  let P : Set (Fin n → ℝ) := polyhedron_le_set A b
  have hP_nonempty : P.Nonempty := by
    simpa [P] using polyhedron_nonempty_of_pos_dim A b hP_dim
  have hP_bounded : Bornology.IsBounded P := by
    rcases hP_polytope with ⟨V, hV, hVeq⟩
    simpa [P, hVeq] using (isBounded_convexHull).2 hV.isBounded
  obtain ⟨x, hxP⟩ := hP_nonempty
  have htranslate : ({x} + recessionCone P) ⊆ P := by
    rintro y ⟨x', hx', r, hr, rfl⟩
    rw [Set.mem_singleton_iff] at hx'
    subst x'
    rw [mem_recessionCone_iff] at hr
    simpa using hr hxP 1 zero_le_one
  have hrec_zero : recessionCone P = ({0} : Set (Fin n → ℝ)) := by
    have hrec_bounded : Bornology.IsBounded (recessionCone P) := by
      obtain ⟨R, hR_pos, hP_ball⟩ := hP_bounded.subset_ball_lt 0 (0 : Fin n → ℝ)
      exact Bornology.IsBounded.subset
        (show Bornology.IsBounded (Metric.ball (0 : Fin n → ℝ) (R + ‖x‖)) from
          Metric.isBounded_ball)
        (by
          intro r hr
          have hxrP : x + r ∈ P := htranslate ⟨x, Set.mem_singleton x, r, hr, by simp⟩
          have hxr_ball : ‖x + r‖ < R := by
            simpa [Metric.mem_ball, dist_eq_norm] using hP_ball hxrP
          have hr_eq : r = (x + r) + (-x) := by
            ext i
            simp
          have hr_norm_le : ‖r‖ ≤ ‖x + r‖ + ‖x‖ := by
            rw [hr_eq]
            simpa using norm_add_le (x + r) (-x)
          have hr_norm_lt : ‖r‖ < R + ‖x‖ := by
            linarith
          simpa [Metric.mem_ball, dist_eq_norm] using hr_norm_lt)
    ext r
    constructor
    · intro hr
      by_cases hr0 : r = 0
      · simp [hr0]
      · obtain ⟨R, hR⟩ := hrec_bounded.subset_closedBall (0 : Fin n → ℝ)
        have hzero_mem : (0 : Fin n → ℝ) ∈ recessionCone P :=
          zero_mem_recessionCone
        have hR_nonneg : 0 ≤ R := by
          have hzero_ball : (0 : Fin n → ℝ) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR hzero_mem
          simpa [Metric.mem_closedBall] using hzero_ball
        have hr_norm_pos : 0 < ‖r‖ := norm_pos_iff.mpr hr0
        have hr_norm_ne : ‖r‖ ≠ 0 := ne_of_gt hr_norm_pos
        have ht_nonneg : 0 ≤ R / ‖r‖ + 1 := by positivity
        have htr_mem : ((R / ‖r‖ + 1) • r) ∈ recessionCone P :=
          smul_mem_recessionCone hr ht_nonneg
        have htr_ball :
            ((R / ‖r‖ + 1) • r) ∈ Metric.closedBall (0 : Fin n → ℝ) R := hR htr_mem
        have htr_bound : ‖(R / ‖r‖ + 1) • r‖ ≤ R := by
          simpa [Metric.mem_closedBall, dist_eq_norm] using htr_ball
        have htr_norm : ‖(R / ‖r‖ + 1) • r‖ = R + ‖r‖ := by
          calc
            ‖(R / ‖r‖ + 1) • r‖ = |R / ‖r‖ + 1| * ‖r‖ := norm_smul _ _
            _ = (R / ‖r‖ + 1) * ‖r‖ := by rw [abs_of_nonneg ht_nonneg]
            _ = (R / ‖r‖) * ‖r‖ + ‖r‖ := by rw [add_mul, one_mul]
            _ = R + ‖r‖ := by rw [div_mul_cancel₀ _ hr_norm_ne]
        have hlarge : R + ‖r‖ ≤ R := by
          simpa [htr_norm] using htr_bound
        linarith
    · intro hr
      have hzero_mem : (0 : Fin n → ℝ) ∈ recessionCone P :=
        zero_mem_recessionCone
      have hr0 : r = 0 := Set.mem_singleton_iff.mp hr
      simpa [hr0] using hzero_mem
  have hrec_dim_zero : recessionConeDim P = 0 := by
    simp [recessionConeDim, hrec_zero]
  have hP_dim_pos : 0 < polyhedronDim P := by
    simpa [P] using hP_dim
  simpa [P, hrec_dim_zero] using hP_dim_pos

/-- Lemma 4.50. Let `P := {x : ℝ^n | A *ᵥ x ≤ b}` be a polytope of dimension at least one. An
inequality `c ⬝ᵥ x ≤ δ` is valid for `P` if and only if there exists a nonnegative multiplier `u`
such that `u ᵥ* A = c` and `u ⬝ᵥ b = δ`. This is the Chapter 4 specialization of the Chapter 3
owner theorem `valid_inequality_iff_exists_nonneg_row_multiplier_of_dim_gt_dim_recession`. -/
theorem valid_inequality_iff_exists_exact_nonneg_row_multiplier_of_polytope_pos_dim
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (δ : ℝ)
    (hP_polytope : (polyhedron_le_set A b).IsPolytope ℝ)
    (hP_dim : 0 < polyhedronDim (polyhedron_le_set A b)) :
    is_valid_inequality (polyhedron_le_set A b) c δ ↔
      ∃ u : Fin m → ℝ, 0 ≤ u ∧ u ᵥ* A = c ∧ u ⬝ᵥ b = δ := by
  exact
    valid_inequality_iff_exists_nonneg_row_multiplier_of_dim_gt_dim_recession A b c δ
      (polyhedron_dim_gt_recessionConeDim_of_polytope_pos_dim A b hP_polytope hP_dim)
