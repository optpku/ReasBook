/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace Pointwise

namespace Set

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Example 6.6: the set determined by a vector `u` is the closed half-space of vectors whose
inner product with `u` is nonpositive. -/
def nonpositiveInnerHalfspace (u : 𝓗) : Set 𝓗 :=
  {x | ⟪x, u⟫_ℝ ≤ 0}

-- Proof sketch: unfold `Set.nonpositiveInnerHalfspace`.
/-- Membership in the nonpositive inner-product half-space means having nonpositive inner product
with the defining vector. -/
theorem mem_nonpositiveInnerHalfspace_iff {u x : 𝓗} :
    x ∈ nonpositiveInnerHalfspace u ↔ ⟪x, u⟫_ℝ ≤ 0 := by
  -- Unfold the defining predicate of the half-space.
  rfl

-- Proof sketch: the inner product is linear in the first variable, so nonpositive inner-product
-- inequalities are preserved under convex combinations.
/-- The nonpositive inner-product half-space is convex. -/
theorem nonpositiveInnerHalfspace_convex (u : 𝓗) :
    Convex ℝ (nonpositiveInnerHalfspace u) := by
  intro x hx y hy a b ha hb hab
  rw [mem_nonpositiveInnerHalfspace_iff] at hx hy ⊢
  -- Expand the inner product of the convex combination and estimate each term separately.
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  exact add_nonpos
    (mul_nonpos_of_nonneg_of_nonpos ha hx)
    (mul_nonpos_of_nonneg_of_nonpos hb hy)

-- Proof sketch: if `⟪x, u⟫ ≤ 0` and `a > 0`, then `⟪a • x, u⟫ = a * ⟪x, u⟫ ≤ 0`, so the
-- half-space is stable under positive dilations.
/-- The nonpositive inner-product half-space is a cone. -/
theorem nonpositiveInnerHalfspace_isCone (u : 𝓗) :
    IsCone (nonpositiveInnerHalfspace u) := by
  ext x
  constructor
  · intro hx
    -- The scalar `1` witnesses that each point is a positive multiple of itself.
    exact Set.mem_smul.mpr ⟨1, by simp, x, hx, by simp⟩
  · intro hx
    rcases Set.mem_smul.mp hx with ⟨a, ha, y, hy, rfl⟩
    rw [mem_nonpositiveInnerHalfspace_iff] at hy ⊢
    -- Positive scaling preserves the defining nonpositivity inequality.
    simpa [real_inner_smul_left] using mul_nonpos_of_nonneg_of_nonpos ha.le hy

/-- Helper for Example 6.6: every point in the ball centered at `-u` with radius `‖u‖` satisfies
the defining half-space inequality. -/
lemma ball_subset_nonpositiveInnerHalfspace_of_ne_zero {u : 𝓗} (hu : u ≠ 0) :
    Metric.ball (-u) ‖u‖ ⊆ nonpositiveInnerHalfspace u := by
  intro x hx
  rw [mem_nonpositiveInnerHalfspace_iff]
  have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hxu_norm : ‖x + u‖ < ‖u‖ := by
    simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hx
  have hmul_lt : ‖x + u‖ * ‖u‖ < ‖u‖ ^ 2 := by
    simpa [pow_two] using mul_lt_mul_of_pos_right hxu_norm hu_norm_pos
  have hinner_lt : ⟪x + u, u⟫_ℝ < ‖u‖ ^ 2 := by
    exact (real_inner_le_norm (x + u) u).trans_lt hmul_lt
  -- Rewrite the shifted inner product and isolate the target term `⟪x, u⟫`.
  rw [inner_add_left, real_inner_self_eq_norm_sq] at hinner_lt
  linarith

/-- Helper for Example 6.6: vectors orthogonal to `u` lie in the half-space and also in its
negative. -/
lemma orthogonal_span_singleton_subset_halfspace_inter_neg (u : 𝓗) :
    ((ℝ ∙ u)ᗮ : Set 𝓗) ⊆ nonpositiveInnerHalfspace u ∩ -nonpositiveInnerHalfspace u := by
  intro x hx
  have hx_orth : ⟪x, u⟫_ℝ = 0 := by
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp hx
  constructor
  · rw [mem_nonpositiveInnerHalfspace_iff]
    exact le_of_eq hx_orth
  · rw [Set.mem_neg, mem_nonpositiveInnerHalfspace_iff]
    -- Negating an orthogonal vector keeps the inner product equal to zero.
    simp [inner_neg_left, hx_orth]

/-- Helper for Example 6.6: in dimension greater than `1`, the orthogonal complement of the line
through a nonzero vector contains a nonzero vector. -/
lemma exists_nonzero_mem_orthogonal_span_singleton_of_rank_gt_one {u : 𝓗} (hu : u ≠ 0)
    (h_dim : 1 < Module.rank ℝ 𝓗) :
    ∃ x : 𝓗, x ≠ 0 ∧ x ∈ (ℝ ∙ u)ᗮ := by
  -- Route correction: instead of a kernel/to-dual argument, orthogonalize a companion vector from
  -- a linearly independent pair with `u`.
  obtain ⟨y, hy⟩ : ∃ y, LinearIndependent ℝ ![u, y] :=
    exists_linearIndependent_pair_of_one_lt_rank h_dim hu
  let c : ℝ := ⟪y, u⟫_ℝ / ‖u‖ ^ 2
  let z : 𝓗 := y - c • u
  have hz_lin : LinearIndependent ℝ ![u, z] := by
    -- Subtracting a scalar multiple of `u` from the second vector preserves independence.
    simpa [z, c, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (LinearIndependent.pair_add_smul_right_iff (x := u) (y := y) (c := -c)).2 hy
  have hz_ne : z ≠ 0 := by
    simpa [z] using hz_lin.ne_zero 1
  have hu_sq_ne : ‖u‖ ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hu)
  have hz_orth : z ∈ (ℝ ∙ u)ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    -- The correction coefficient was chosen so that the residual has zero inner product with `u`.
    rw [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    dsimp [c]
    have hcancel : (⟪y, u⟫_ℝ / ‖u‖ ^ 2) * (‖u‖ ^ 2) = ⟪y, u⟫_ℝ := by
      field_simp [hu_sq_ne]
    rw [hcancel]
    ring
  exact ⟨z, hz_ne, hz_orth⟩

-- Proof sketch: the half-space contains an open ball centered sufficiently far in the `-u`
-- direction, so its interior is nonempty.
/-- The nonpositive inner-product half-space is solid. -/
theorem nonpositiveInnerHalfspace_solid (u : 𝓗) :
    (interior (nonpositiveInnerHalfspace u)).Nonempty := by
  by_cases hu : u = 0
  · -- When `u = 0`, the half-space is all of `𝓗`, whose interior is nonempty.
    simp [nonpositiveInnerHalfspace, hu]
  · have hu_norm_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
    have hball :
        Metric.ball (-u) ‖u‖ ⊆ nonpositiveInnerHalfspace u :=
      ball_subset_nonpositiveInnerHalfspace_of_ne_zero hu
    refine ⟨-u, ?_⟩
    rw [mem_interior_iff_mem_nhds]
    -- The explicit ball around `-u` is contained in the half-space, so `-u` is interior.
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hu_norm_pos) hball

-- Proof sketch: if the rank of `𝓗` is greater than `1`, then there is a nonzero vector orthogonal
-- to `u`; such a vector lies in the half-space and in its negative, so the intersection with its
-- negative is larger than `{0}`.
/-- If the ambient real inner-product space has dimension greater than `1`, then the nonpositive
inner-product half-space is not pointed. -/
theorem nonpositiveInnerHalfspace_not_pointed_of_rank_gt_one (u : 𝓗)
    (h_dim : 1 < Module.rank ℝ 𝓗) :
    ¬ (nonpositiveInnerHalfspace u ∩ -nonpositiveInnerHalfspace u = ({0} : Set 𝓗)) := by
  intro hEq
  by_cases hu : u = 0
  · have h_rank_pos : 0 < Module.rank ℝ 𝓗 := lt_trans (by simp) h_dim
    obtain ⟨x, hx_ne⟩ : ∃ x : 𝓗, x ≠ 0 :=
      rank_pos_iff_exists_ne_zero.mp h_rank_pos
    have hx_mem : x ∈ nonpositiveInnerHalfspace u ∩ -nonpositiveInnerHalfspace u := by
      simp [nonpositiveInnerHalfspace, hu]
    have hx_zero : x = 0 := by
      rw [hEq] at hx_mem
      simpa using hx_mem
    exact hx_ne hx_zero
  · obtain ⟨x, hx_ne, hx_orth⟩ :
      ∃ x : 𝓗, x ≠ 0 ∧ x ∈ (ℝ ∙ u)ᗮ :=
        exists_nonzero_mem_orthogonal_span_singleton_of_rank_gt_one hu h_dim
    have hx_mem :
        x ∈ nonpositiveInnerHalfspace u ∩ -nonpositiveInnerHalfspace u :=
      orthogonal_span_singleton_subset_halfspace_inter_neg u hx_orth
    have hx_zero : x = 0 := by
      rw [hEq] at hx_mem
      simpa using hx_mem
    exact hx_ne hx_zero

end

end Set
