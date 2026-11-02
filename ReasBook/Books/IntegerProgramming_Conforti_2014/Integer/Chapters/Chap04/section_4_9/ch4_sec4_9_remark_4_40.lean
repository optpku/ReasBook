import Mathlib

open scoped Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: convex geometry of affine lines and convex hulls in `ℝ²`
-- * core/canonical owners: mathlib's `line[ℝ, p₀, p₁]`, `convexHull ℝ`, and `IsClosed`
-- * source-facing data: the horizontal line and the point `(0, 1)`
-- This file therefore uses the canonical affine-line owner directly and keeps only the
-- source-facing lemmas needed for the counterexample.

section Remark440

local notation "p₀" => (![0, 0] : Fin 2 → ℝ)
local notation "p₁" => (![1, 0] : Fin 2 → ℝ)
local notation "q" => (![0, 1] : Fin 2 → ℝ)

/-- Membership in the horizontal affine line through `(0, 0)` and `(1, 0)` means that the second
coordinate is `0`. -/
theorem mem_remark_4_40_line_iff {x : Fin 2 → ℝ} :
    x ∈ line[ℝ, p₀, p₁] ↔ x 1 = 0 := by
  constructor
  · intro hx
    -- Expand line membership through the affine-line parameterization.
    -- Then read off the second coordinate of the resulting line-map point.
    rcases mem_affineSpan_pair_iff_exists_lineMap_eq.mp hx with ⟨r, hr⟩
    have hcoord : AffineMap.lineMap p₀ p₁ r 1 = x 1 := by
      simp [hr]
    simpa [AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module] using hcoord.symm
  · intro hx
    -- A point with second coordinate `0` is reached by the line parameter `x 0`.
    refine mem_affineSpan_pair_iff_exists_lineMap_eq.mpr ?_
    refine ⟨x 0, ?_⟩
    ext i
    fin_cases i
    · simp [AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module]
    · simp [AffineMap.pi_lineMap_apply, hx]

/-- The point `(0, 1)` does not lie on the horizontal affine line through `(0, 0)` and `(1, 0)`.
-/
theorem remark_4_40_off_line_point_not_mem_line :
    q ∉ line[ℝ, p₀, p₁] := by
  -- The second coordinate test immediately excludes `q`.
  rw [mem_remark_4_40_line_iff]
  simp

/-- Helper for Remark 4.40: rewrite the convex hull of the line-point union as a convex join. -/
lemma remark_4_40_convexHull_eq_convexJoin :
    convexHull ℝ (line[ℝ, p₀, p₁] ∪ {q}) =
      convexJoin ℝ (line[ℝ, p₀, p₁] : Set (Fin 2 → ℝ)) {q} := by
  have hp0_mem : p₀ ∈ line[ℝ, p₀, p₁] := left_mem_affineSpan_pair ℝ p₀ p₁
  have hline_nonempty : (line[ℝ, p₀, p₁] : Set (Fin 2 → ℝ)).Nonempty := ⟨p₀, hp0_mem⟩
  have hline_convex : Convex ℝ (line[ℝ, p₀, p₁] : Set (Fin 2 → ℝ)) :=
    AffineSubspace.convex _
  -- Normalize the hull with the canonical convex-hull-of-union formula.
  ext x
  rw [convexHull_union hline_nonempty (Set.singleton_nonempty q), convexHull_singleton]
  rw [mem_convexJoin, mem_convexJoin]
  constructor
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hx' : x ∈ (line[ℝ, p₀, p₁] : Set (Fin 2 → ℝ)) := by
      rw [hline_convex.convexHull_eq] at hx
      exact hx
    exact ⟨x, hx', y, hy, hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    have hx' : x ∈ convexHull ℝ (line[ℝ, p₀, p₁] : Set (Fin 2 → ℝ)) := by
      rw [hline_convex.convexHull_eq]
      exact hx
    exact ⟨x, hx', y, hy, hxy⟩

/-- Helper for Remark 4.40: every point `![a, t]` with `0 ≤ t < 1` lies in the convex hull of the
horizontal line and the point `q`. -/
lemma remark_4_40_verticalPoint_mem_convexHull (a t : ℝ) (ht_nonneg : 0 ≤ t) (ht_lt : t < 1) :
    (![a, t] : Fin 2 → ℝ) ∈ convexHull ℝ (line[ℝ, p₀, p₁] ∪ {q}) := by
  have hden_pos : 0 < 1 - t := by
    linarith
  have hden_ne : 1 - t ≠ 0 := ne_of_gt hden_pos
  have hy_line : (![a / (1 - t), 0] : Fin 2 → ℝ) ∈ line[ℝ, p₀, p₁] := by
    -- The chosen line point lies on the horizontal line because its second coordinate is `0`.
    rw [mem_remark_4_40_line_iff]
    simp
  have hq_mem : q ∈ ({q} : Set (Fin 2 → ℝ)) := by
    simp
  have ht_le : t ≤ 1 := by
    linarith
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := ⟨ht_nonneg, ht_le⟩
  have hlineMap :
      AffineMap.lineMap (![a / (1 - t), 0] : Fin 2 → ℝ) q t = (![a, t] : Fin 2 → ℝ) := by
    -- Compute the segment point coordinatewise.
    ext i
    fin_cases i
    · simp [AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module]
      field_simp [hden_ne]
    · simp [AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module]
  have hsegment :
      AffineMap.lineMap (![a / (1 - t), 0] : Fin 2 → ℝ) q t ∈
        segment ℝ (![a / (1 - t), 0] : Fin 2 → ℝ) q :=
    lineMap_mem_segment ℝ (![a / (1 - t), 0] : Fin 2 → ℝ) q ht_mem
  have htarget :
      (![a, t] : Fin 2 → ℝ) ∈ segment ℝ (![a / (1 - t), 0] : Fin 2 → ℝ) q := hlineMap ▸ hsegment
  -- After rewriting the hull as a convex join, the segment witness finishes the membership proof.
  rw [remark_4_40_convexHull_eq_convexJoin, mem_convexJoin]
  exact ⟨![a / (1 - t), 0], hy_line, q, hq_mem, htarget⟩

/-- Helper for Remark 4.40: the only point of the convex hull whose second coordinate is `1` is
the point `q`. -/
lemma remark_4_40_eq_q_of_mem_convexHull_of_second_eq_one {x : Fin 2 → ℝ}
    (hx : x ∈ convexHull ℝ (line[ℝ, p₀, p₁] ∪ {q})) (hx1 : x 1 = 1) : x = q := by
  rw [remark_4_40_convexHull_eq_convexJoin, mem_convexJoin] at hx
  rcases hx with ⟨y, hy, z, hz, hxseg⟩
  have hzq : z = q := by
    simpa using hz
  subst hzq
  rw [segment_eq_image_lineMap] at hxseg
  rcases hxseg with ⟨t, ht, rfl⟩
  have hy_second_zero : y 1 = 0 := (mem_remark_4_40_line_iff.mp hy)
  have hsecond :
      (AffineMap.lineMap y q t : Fin 2 → ℝ) 1 = 1 := by
    simpa using hx1
  have ht_eq_one : t = 1 := by
    -- The second coordinate along the segment is exactly the parameter `t`.
    simpa [hy_second_zero, AffineMap.pi_lineMap_apply, AffineMap.lineMap_apply_module] using
      hsecond
  subst ht_eq_one
  -- At parameter `1`, the segment endpoint is `q`.
  simp [AffineMap.lineMap_apply_one]

/-- Remark 4.40. The family consisting of a line in `ℝ²` and a point not on that line gives
an example whose convex hull is not closed. -/
theorem remark_4_40_convexHull_line_union_point_not_closed :
    ¬ IsClosed (convexHull ℝ (line[ℝ, p₀, p₁] ∪ {q})) := by
  intro hclosed
  let u : ℕ → Fin 2 → ℝ := fun n ↦ ![1, (n : ℝ) / ((n : ℝ) + 1)]
  have hu_mem : ∀ n, u n ∈ convexHull ℝ (line[ℝ, p₀, p₁] ∪ {q}) := by
    intro n
    have hden_pos : 0 < (n : ℝ) + 1 := by
      positivity
    have hnum_nonneg : 0 ≤ (n : ℝ) := by
      positivity
    have hu_nonneg : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := by
      exact div_nonneg hnum_nonneg hden_pos.le
    have hnum_lt_den : (n : ℝ) < (n : ℝ) + 1 := by
      linarith
    have hu_lt_one : (n : ℝ) / ((n : ℝ) + 1) < 1 := by
      exact (div_lt_one hden_pos).2 hnum_lt_den
    -- Every point on this approximating sequence lies in the hull by the vertical-point helper.
    simpa [u] using remark_4_40_verticalPoint_mem_convexHull 1
      ((n : ℝ) / ((n : ℝ) + 1)) hu_nonneg hu_lt_one
  have hu_tendsto : Filter.Tendsto u Filter.atTop (nhds (![1, 1] : Fin 2 → ℝ)) := by
    have hnat_shift_tendsto : Filter.Tendsto (fun n : ℕ ↦ n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_add_atTop_nat 1
    have hden_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) Filter.atTop Filter.atTop :=
      by
        convert
          (tendsto_natCast_atTop_atTop.comp hnat_shift_tendsto :
            Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) Filter.atTop Filter.atTop) using 1
        funext n
        norm_num
    have hinv_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ (((n : ℝ) + 1)⁻¹)) Filter.atTop (nhds 0) :=
      hden_tendsto.inv_tendsto_atTop
    have hsecond_tendsto :
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) Filter.atTop (nhds 1) := by
      -- Rewrite the second coordinate as `1 - ((n : ℝ) + 1)⁻¹`.
      have hrewrite :
          (fun n : ℕ ↦ (n : ℝ) / ((n : ℝ) + 1)) =
            fun n : ℕ ↦ 1 - (((n : ℝ) + 1)⁻¹) := by
        funext n
        have hden_ne : (n : ℝ) + 1 ≠ 0 := by
          positivity
        calc
          (n : ℝ) / ((n : ℝ) + 1) = (((n : ℝ) + 1) - 1) / ((n : ℝ) + 1) := by ring
          _ = 1 - (((n : ℝ) + 1)⁻¹) := by
            field_simp [hden_ne]
      rw [hrewrite]
      simpa using tendsto_const_nhds.sub hinv_tendsto
    -- Check convergence coordinatewise in the product topology on `Fin 2 → ℝ`.
    refine tendsto_pi_nhds.2 ?_
    intro i
    fin_cases i
    · simp [u]
    · simpa [u] using hsecond_tendsto
  have hlimit_mem :
      (![1, 1] : Fin 2 → ℝ) ∈ convexHull ℝ (line[ℝ, p₀, p₁] ∪ {q}) :=
    hclosed.mem_of_tendsto hu_tendsto (Filter.Eventually.of_forall hu_mem)
  have hlimit_second : ((![1, 1] : Fin 2 → ℝ) 1) = 1 := by
    simp
  have hlimit_eq_q :
      (![1, 1] : Fin 2 → ℝ) = q :=
    remark_4_40_eq_q_of_mem_convexHull_of_second_eq_one hlimit_mem hlimit_second
  have hfirst : ((![1, 1] : Fin 2 → ℝ) 0) = q 0 := by
    simpa using congrArg (fun x : Fin 2 → ℝ ↦ x 0) hlimit_eq_q
  simp at hfirst

end Remark440
