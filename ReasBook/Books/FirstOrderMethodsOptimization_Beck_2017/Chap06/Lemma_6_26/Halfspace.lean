/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap01.Definition_1_13
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

noncomputable section

open scoped RealInnerProductSpace

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Helper for Lemma 6.26: a half-space is convex because the defining inner-product inequality is
preserved under convex combinations. -/
lemma convex_halfSpace_owner (a : E) (α : ℝ) : Convex ℝ (halfSpace a α) := by
  intro x hx y hy t₁ t₂ ht₁ ht₂ hsum
  rw [mem_halfSpace_iff] at hx hy ⊢
  rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
  calc
    t₁ * inner ℝ a x + t₂ * inner ℝ a y ≤ t₁ * α + t₂ * α := by
      gcongr
    _ = (t₁ + t₂) * α := by
      ring
    _ = α := by
      rw [hsum, one_mul]

/-- Helper for Lemma 6.26: on the active branch of the half-space projection formula, the affine
correction lands on the boundary hyperplane. -/
lemma halfSpace_active_correction_mem
    (a x : E) (α : ℝ) (ha : a ≠ 0) :
    x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a) ∈ halfSpace a α := by
  have hnorm_sq_ne : ‖a‖ ^ (2 : ℕ) ≠ 0 := by
    positivity
  rw [mem_halfSpace_iff]
  calc
    inner ℝ a (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a)) =
        inner ℝ a x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * inner ℝ a a) := by
          rw [inner_sub_right, real_inner_smul_right]
    _ = inner ℝ a x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * ‖a‖ ^ (2 : ℕ)) := by
          rw [real_inner_self_eq_norm_sq]
    _ = α := by
          have hcancel :
              (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * ‖a‖ ^ (2 : ℕ)) = inner ℝ a x - α := by
            field_simp [hnorm_sq_ne]
          linarith
  exact le_rfl

/-- Helper for Lemma 6.26: on the active branch, the normal correction is no farther from `x`
than any feasible point of the half-space. -/
lemma halfSpace_active_correction_distance_le
    (a x y : E) (α : ℝ) (ha : a ≠ 0) (hy : y ∈ halfSpace a α) (hx : α < inner ℝ a x) :
    ‖x - (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a))‖ ≤ ‖x - y‖ := by
  have hnorm_pos : 0 < ‖a‖ := by
    exact norm_pos_iff.mpr ha
  have hy_inner : inner ℝ a y ≤ α := by
    exact mem_halfSpace_iff.mp hy
  have hnum_le : inner ℝ a x - α ≤ ‖a‖ * ‖x - y‖ := by
    have hxy : inner ℝ a x - α ≤ inner ℝ a (x - y) := by
      rw [inner_sub_right]
      linarith
    exact le_trans hxy (real_inner_le_norm _ _)
  have hcorrection :
      ‖x - (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a))‖ =
        (inner ℝ a x - α) / ‖a‖ := by
    calc
      ‖x - (x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a))‖ =
          ‖(((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a)‖ := by
            abel_nf
      _ = |((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ))| * ‖a‖ := by
            rw [norm_smul, Real.norm_eq_abs]
      _ = (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) * ‖a‖) := by
            rw [abs_of_nonneg]
            exact div_nonneg (by linarith) (by positivity)
      _ = (inner ℝ a x - α) / ‖a‖ := by
            field_simp [show ‖a‖ ≠ 0 by positivity]
  have hdiv : (inner ℝ a x - α) / ‖a‖ ≤ ‖x - y‖ := by
    rw [div_le_iff₀ hnorm_pos]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hnum_le
  rw [hcorrection]
  exact hdiv

/-- Lemma 6.26 (5): for a nontrivial closed half-space `halfSpace a α`, the orthogonal
projection is the singleton obtained by subtracting the positive-part affine violation in the
normal direction `a`. -/
lemma projection_mapping_halfSpace_eq_singleton_positivePartCorrection
    (a x : E) (α : ℝ) (ha : a ≠ 0) :
    P[halfSpace a α] x =
      {x - (((⟪a, x⟫ - α)⁺ / ‖a‖ ^ (2 : ℕ)) • a)} := by
  by_cases hx : inner ℝ a x ≤ α
  · have hp_proj : x ∈ P[halfSpace a α] x := by
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨?_, ?_⟩
      · rw [mem_halfSpace_iff]
        exact hx
      · intro y hy
        simp
    have hp_eq : x - (((⟪a, x⟫ - α)⁺ / ‖a‖ ^ (2 : ℕ)) • a) = x := by
      have hpos : (⟪a, x⟫ - α)⁺ = 0 := by
        simp [sub_nonpos.mpr hx]
      rw [hpos, zero_div, zero_smul, sub_zero]
    have hsub :
        (P[halfSpace a α] x).Subsingleton :=
      projection_mapping_subsingleton (halfSpace a α) (convex_halfSpace_owner a α) x
    simpa [hp_eq] using hsub.eq_singleton_of_mem hp_proj
  · have hviol : α < inner ℝ a x := by
      exact lt_of_not_ge hx
    have hp_proj : x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a) ∈ P[halfSpace a α] x := by
      rw [mem_projection_mapping_iff, isMinOn_iff]
      refine ⟨halfSpace_active_correction_mem a x α ha, ?_⟩
      intro y hy
      simpa [norm_sub_rev] using
        halfSpace_active_correction_distance_le a x y α ha hy hviol
    have hp_eq :
        x - (((⟪a, x⟫ - α)⁺ / ‖a‖ ^ (2 : ℕ)) • a) =
          x - (((inner ℝ a x - α) / ‖a‖ ^ (2 : ℕ)) • a) := by
      have hpos : (⟪a, x⟫ - α)⁺ = inner ℝ a x - α := by
        simp [sub_nonneg.mpr hviol.le]
      rw [hpos]
    have hsub :
        (P[halfSpace a α] x).Subsingleton :=
      projection_mapping_subsingleton (halfSpace a α) (convex_halfSpace_owner a α) x
    simpa [hp_eq] using hsub.eq_singleton_of_mem hp_proj

end
