/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_9

-- Declarations for this item will be appended below by the statement pipeline.

open Set AffineMap
open scoped Pointwise

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Proposition 6.16: cone membership in a convex set is equivalent to membership in a
positive dilate of that set. -/
lemma mem_cone_iff_exists_pos_smul_mem {D : Set E} (hD_convex : Convex ℝ D) {z : E} :
    z ∈ cone D ↔ ∃ a : ℝ, 0 < a ∧ z ∈ a • D := by
  -- Rewrite the source-facing cone through the convex-cone hull characterization from mathlib.
  simpa [Set.cone_def] using
    (ConvexCone.mem_hull_of_convex (𝕜 := ℝ) (s := D) (x := z) hD_convex)

/-- Helper for Proposition 6.16: if `0 ∈ C`, then smaller positive dilates of a convex set are
contained in larger positive dilates. -/
lemma smul_set_subset_smul_set_of_convex_zero_mem {C : Set E} (hC_convex : Convex ℝ C)
    (h0C : (0 : E) ∈ C) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    a • C ⊆ b • C := by
  intro x hx
  rcases hx with ⟨y, hy, rfl⟩
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hratio_mem : (a / b) • y ∈ C := by
    -- Contract the point `y` toward the origin inside the convex set.
    have hratio : a / b ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · exact div_nonneg ha.le hb.le
      · exact (div_le_one hb).2 hab
    exact hC_convex.smul_mem_of_zero_mem h0C hy hratio
  refine ⟨(a / b) • y, hratio_mem, ?_⟩
  -- Expanding the larger-scale witness recovers the original point.
  have hscale : b * (a / b) = a := by
    field_simp [hb.ne']
  simp [smul_smul, hscale]

/-- Helper for Proposition 6.16: scaling an interior point toward the origin keeps it in the
interior of a convex set containing the origin. -/
lemma smul_mem_interior_of_mem_interior_of_pos_le_one {C : Set E} (hC_convex : Convex ℝ C)
    (h0C : (0 : E) ∈ C) {y : E} (hy : y ∈ interior C) {t : ℝ} (ht_pos : 0 < t)
    (ht_le : t ≤ 1) :
    t • y ∈ interior C := by
  have h_one_sub_nonneg : 0 ≤ 1 - t := sub_nonneg.mpr ht_le
  have hsum : (1 - t) + t = 1 := by ring
  -- Express `t • y` as a convex combination of `0` and the interior point `y`.
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
    hC_convex.combo_self_interior_mem_interior h0C hy h_one_sub_nonneg ht_pos hsum

/-- Helper for Proposition 6.16: if an interior point and an extrapolated point of a convex set lie
on the same line, then the intermediate point is interior. -/
lemma mem_interior_of_add_smul_sub_mem {C : Set E} (hC_convex : Convex ℝ C)
    {u v : E} (hv : v ∈ interior C) {ε : ℝ} (hw : u + ε • (u - v) ∈ C) (hε : 0 < ε) :
    u ∈ interior C := by
  let t : ℝ := 1 / (1 + ε)
  have ht : t ∈ Set.Ioo (0 : ℝ) 1 := by
    constructor
    · have : 0 < 1 + ε := by positivity
      exact one_div_pos.mpr this
    · have : 1 < 1 + ε := by linarith
      dsimp [t]
      exact (div_lt_one (show 0 < 1 + ε by positivity)).2 (by linarith)
  have hline : lineMap v (u + ε • (u - v)) t = u := by
    -- Choose the segment parameter so the point on the open segment collapses back to `u`.
    have hden : (1 + ε) ≠ 0 := by linarith
    apply smul_right_injective E hden
    change (1 + ε) • lineMap v (u + ε • (u - v)) (1 / (1 + ε) : ℝ) = (1 + ε) • u
    rw [lineMap_apply_module, smul_add, smul_smul, smul_add, smul_add, smul_sub, smul_smul,
      smul_smul]
    field_simp [hden]
    simp only [one_smul]
    abel_nf
    rw [add_smul, one_smul]
  have hu_open : u ∈ openSegment ℝ v (u + ε • (u - v)) := by
    -- Reinterpret `u` as the appropriate point of the open segment joining `v` to the
    -- extrapolated point.
    convert lineMap_mem_openSegment (𝕜 := ℝ) v (u + ε • (u - v)) ht using 1
    exact hline.symm
  -- The open segment from an interior point of a convex set toward another point of the set stays
  -- in the interior.
  exact hC_convex.openSegment_interior_self_subset_interior hv hw hu_open

-- Proof sketch: the inclusion `cone (interior C) ⊆ interior (cone C)` comes from openness of
-- scalar multiplication by positive reals and the inclusion `interior C ⊆ C`. For the reverse
-- inclusion, start from a point in `interior (cone C)`, represent it on a ray through a point of
-- `C`, then use Proposition 3.44 on a segment joining that ray point to an interior point of `C`
-- to show the normalized point lies in `interior C`.
/-- Proposition 6.16: if `C` is a convex subset of a real normed space, contains `0`, and has
nonempty interior, then `interior (cone C) = cone (interior C)`. -/
theorem interior_cone_eq_cone_interior {C : Set E} (hC_convex : Convex ℝ C)
    (h0C : (0 : E) ∈ C)
    (hC_int_nonempty : (interior C).Nonempty) :
    interior (cone C) = cone (interior C) := by
  have hC_int_convex : Convex ℝ (interior C) := hC_convex.interior
  -- Route correction: with the necessary hypothesis `0 ∈ C` present, the textbook proof works by
  -- normalizing all relevant points into one common dilate `μ • C`.
  apply subset_antisymm
  · intro x hx
    -- Start from a point of `interior (cone C)` and put it on a positive ray through `C`.
    rcases (mem_cone_iff_exists_pos_smul_mem hC_convex).1 (interior_subset hx) with
      ⟨γ, hγ, hxγ⟩
    rcases hxγ with ⟨x₁, hx₁, rfl⟩
    rcases hC_int_nonempty with ⟨y₁, hy₁⟩
    by_cases hx₁_int : x₁ ∈ interior C
    · -- If the ray point is already interior, the cone witness is immediate.
      exact (mem_cone_iff_exists_pos_smul_mem hC_int_convex).2 ⟨γ, hγ, ⟨x₁, hx₁_int, rfl⟩⟩
    · let y : E := γ • y₁
      have hcone_nhds : cone C ∈ nhds (γ • x₁) := mem_interior_iff_mem_nhds.mp hx
      rcases Metric.mem_nhds_iff.mp hcone_nhds with ⟨ε₀, hε₀, hball⟩
      have hx₁_ne_y₁ : x₁ ≠ y₁ := by
        intro hxy
        exact hx₁_int (hxy ▸ hy₁)
      have hxy : γ • x₁ ≠ y := by
        dsimp [y]
        intro hxy
        exact hx₁_ne_y₁ ((smul_right_injective E hγ.ne') hxy)
      have hxy_norm : 0 < ‖γ • x₁ - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
      let ε : ℝ := ε₀ / (2 * ‖γ • x₁ - y‖)
      have hε : 0 < ε := by
        dsimp [ε]
        positivity
      have hperturb_ball : γ • x₁ + ε • (γ • x₁ - y) ∈ Metric.ball (γ • x₁) ε₀ := by
        -- Choose a short outward step so the perturbed point stays inside the interior ball.
        rw [Metric.mem_ball, dist_eq_norm]
        have hnorm : ‖(γ • x₁ + ε • (γ • x₁ - y)) - γ • x₁‖ = ε * ‖γ • x₁ - y‖ := by
          rw [add_sub_cancel_left]
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
        rw [hnorm]
        have hcalc : ε * ‖γ • x₁ - y‖ = ε₀ / 2 := by
          dsimp [ε]
          field_simp [hxy_norm.ne']
        rw [hcalc]
        linarith
      have hperturb_cone : γ • x₁ + ε • (γ • x₁ - y) ∈ cone C := hball hperturb_ball
      rcases (mem_cone_iff_exists_pos_smul_mem hC_convex).1 hperturb_cone with
        ⟨ρ, hρ, hρmem⟩
      let μ : ℝ := max γ ρ
      have hμ_pos : 0 < μ := by
        dsimp [μ]
        exact lt_max_iff.mpr (Or.inl hγ)
      have hx_mu : γ • x₁ ∈ μ • C := by
        -- Push the original ray point into the common dilate `μ • C`.
        exact (smul_set_subset_smul_set_of_convex_zero_mem hC_convex h0C hγ (le_max_left _ _))
          ⟨x₁, hx₁, rfl⟩
      have hy_mu : y ∈ μ • C := by
        have hyγ : y ∈ γ • C := by
          refine ⟨y₁, interior_subset hy₁, by simp [y]⟩
        -- The interior comparison point lies in the same common dilate.
        exact (smul_set_subset_smul_set_of_convex_zero_mem hC_convex h0C hγ (le_max_left _ _))
          hyγ
      have hperturb_mu : γ • x₁ + ε • (γ • x₁ - y) ∈ μ • C := by
        -- The perturbed cone point also moves into the common dilate.
        exact (smul_set_subset_smul_set_of_convex_zero_mem hC_convex h0C hρ (le_max_right _ _))
          hρmem
      have hw_mem : μ⁻¹ • (γ • x₁ + ε • (γ • x₁ - y)) ∈ C := by
        rwa [mem_smul_set_iff_inv_smul_mem₀ hμ_pos.ne'] at hperturb_mu
      have hv_int : μ⁻¹ • y ∈ interior C := by
        have hγ_div_pos : 0 < γ / μ := div_pos hγ hμ_pos
        have hγ_div_le_one : γ / μ ≤ 1 := (div_le_one hμ_pos).2 (le_max_left _ _)
        have hy_eq : μ⁻¹ • y = (γ / μ) • y₁ := by
          -- Normalize the comparison point `y = γ • y₁` by the common scale `μ`.
          dsimp [y]
          rw [smul_smul]
          congr 1
          field_simp [hμ_pos.ne']
        rw [hy_eq]
        exact smul_mem_interior_of_mem_interior_of_pos_le_one hC_convex h0C hy₁ hγ_div_pos
          hγ_div_le_one
      have hu_int : μ⁻¹ • (γ • x₁) ∈ interior C := by
        -- The normalized point sits between the normalized interior point and the normalized
        -- extrapolated point, so the segment argument returns it to the interior.
        have hw_eq :
            μ⁻¹ • (γ • x₁ + ε • (γ • x₁ - y)) =
              μ⁻¹ • (γ • x₁) + ε • (μ⁻¹ • (γ • x₁) - μ⁻¹ • y) := by
          simp [smul_add, smul_sub, smul_smul, mul_comm, mul_left_comm, mul_assoc]
        have hw_mem' :
            μ⁻¹ • (γ • x₁) + ε • (μ⁻¹ • (γ • x₁) - μ⁻¹ • y) ∈ C := by
          rw [← hw_eq]
          exact hw_mem
        exact mem_interior_of_add_smul_sub_mem hC_convex hv_int hw_mem' hε
      refine (mem_cone_iff_exists_pos_smul_mem hC_int_convex).2 ⟨μ, hμ_pos, ?_⟩
      -- Rescale the normalized interior point back up to recover the original point.
      simpa [smul_smul, hμ_pos.ne', inv_mul_cancel₀] using
        (smul_mem_smul_set hu_int : μ • (μ⁻¹ • (γ • x₁)) ∈ μ • interior C)
  · intro x hx
    -- A positive dilate of an interior point of `C` is an interior point of the corresponding
    -- positive dilate of `C`, hence belongs to `interior (cone C)`.
    rcases (mem_cone_iff_exists_pos_smul_mem hC_int_convex).1 hx with ⟨γ, hγ, hxγ⟩
    have hx_int : x ∈ interior (γ • C) := by
      rw [interior_smul₀ hγ.ne' C]
      exact hxγ
    have hsubset : γ • C ⊆ cone C := by
      intro z hz
      exact (mem_cone_iff_exists_pos_smul_mem hC_convex).2 ⟨γ, hγ, hz⟩
    exact interior_mono hsubset hx_int
