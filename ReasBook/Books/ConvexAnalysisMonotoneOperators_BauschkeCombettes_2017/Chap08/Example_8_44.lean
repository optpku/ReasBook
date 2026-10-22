/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_40
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_14
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Text_8_0_3

-- Declarations for this item will be appended below by the statement pipeline.

open Filter Set
open scoped Topology

-- Proof sketch: let `f` be the displayed piecewise Huber function. Use Proposition 8.14 on the
-- monotone derivative of `f` to obtain convexity on `Set.univ`, then apply Corollary 8.40 to that
-- convexity statement to deduce continuity.
/-- Helper for Example 8.44: on the positive outer branch, the Huber function is affine. -/
private lemma huberFunction_eq_affine_pos (ρ : Set.Ioi (0 : ℝ)) {x : ℝ} (hx : (ρ : ℝ) < x) :
    huberFunction ρ x = (ρ : ℝ) * x - (ρ : ℝ) ^ 2 / 2 := by
  -- On the positive outer region, `|x| = x`, so the affine textbook branch simplifies directly.
  have hx_pos : 0 < x := lt_trans ρ.2 hx
  have hx_abs : (ρ : ℝ) < |x| := by
    simpa [abs_of_pos hx_pos] using hx
  simpa [abs_of_pos hx_pos] using huberFunction_eq_of_lt ρ hx_abs

/-- Helper for Example 8.44: on the negative outer branch, the Huber function is affine. -/
private lemma huberFunction_eq_affine_neg (ρ : Set.Ioi (0 : ℝ)) {x : ℝ} (hx : x < -(ρ : ℝ)) :
    huberFunction ρ x = -(ρ : ℝ) * x - (ρ : ℝ) ^ 2 / 2 := by
  -- On the negative outer region, `|x| = -x`, so the affine textbook branch acquires slope `-ρ`.
  have hρ_neg : -(ρ : ℝ) < 0 := neg_lt_zero.mpr ρ.2
  have hx_neg : x < 0 := lt_trans hx hρ_neg
  have hx_abs : (ρ : ℝ) < |x| := by
    rw [abs_of_neg hx_neg]
    linarith
  simpa [abs_of_neg hx_neg, mul_comm, mul_left_comm, mul_assoc] using
    huberFunction_eq_of_lt ρ hx_abs

/-- Helper for Example 8.44: on the central interval, the Huber function is quadratic. -/
private lemma huberFunction_eq_quadratic (ρ : Set.Ioi (0 : ℝ)) {x : ℝ}
    (hx_left : -(ρ : ℝ) ≤ x) (hx_right : x ≤ (ρ : ℝ)) :
    huberFunction ρ x = x ^ 2 / 2 := by
  -- Inside `[-ρ, ρ]`, the defining piecewise function selects the quadratic branch.
  have hx_abs : |x| ≤ (ρ : ℝ) := by
    exact abs_le.mpr ⟨by linarith, hx_right⟩
  simpa [sq_abs] using huberFunction_eq_of_le ρ hx_abs

/-- Helper for Example 8.44: to the right of `ρ`, the derivative of the Huber function is `ρ`. -/
private lemma hasDerivAt_huberFunction_of_lt_right (ρ : Set.Ioi (0 : ℝ)) {x : ℝ}
    (hx : (ρ : ℝ) < x) :
    HasDerivAt (huberFunction ρ) (ρ : ℝ) x := by
  -- Near such an `x`, the function agrees with its affine positive branch.
  have hmodel : HasDerivAt (fun y : ℝ ↦ (ρ : ℝ) * y - (ρ : ℝ) ^ 2 / 2) (ρ : ℝ) x := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul (ρ : ℝ)).sub_const ((ρ : ℝ) ^ 2 / 2))
  refine hmodel.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact huberFunction_eq_affine_pos ρ hy

/-- Helper for Example 8.44: to the left of `-ρ`, the derivative of the Huber function is `-ρ`. -/
private lemma hasDerivAt_huberFunction_of_lt_left (ρ : Set.Ioi (0 : ℝ)) {x : ℝ}
    (hx : x < -(ρ : ℝ)) :
    HasDerivAt (huberFunction ρ) (-(ρ : ℝ)) x := by
  -- Near such an `x`, the function agrees with its affine negative branch.
  have hmodel : HasDerivAt (fun y : ℝ ↦ -(ρ : ℝ) * y - (ρ : ℝ) ^ 2 / 2) (-(ρ : ℝ)) x := by
    simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using
      (((hasDerivAt_id x).const_mul (-(ρ : ℝ))).sub_const ((ρ : ℝ) ^ 2 / 2))
  refine hmodel.congr_of_eventuallyEq ?_
  filter_upwards [Iio_mem_nhds hx] with y hy
  exact huberFunction_eq_affine_neg ρ hy

/-- Helper for Example 8.44: on the open middle interval, the derivative of the Huber function is
the identity. -/
private lemma hasDerivAt_huberFunction_of_mem_middle (ρ : Set.Ioi (0 : ℝ)) {x : ℝ}
    (hx_left : -(ρ : ℝ) < x) (hx_right : x < (ρ : ℝ)) :
    HasDerivAt (huberFunction ρ) x x := by
  -- Near such an `x`, the function agrees with the quadratic branch `y ↦ y^2 / 2`.
  have hmodel : HasDerivAt (fun y : ℝ ↦ y ^ 2 / 2) x x := by
    simpa [pow_two, two_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
      (((hasDerivAt_id x).pow 2).div_const (2 : ℝ))
  refine hmodel.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hx_left hx_right] with y hy
  exact huberFunction_eq_quadratic ρ hy.1.le hy.2.le

/-- Helper for Example 8.44: the derivative at the switching point `ρ` is still `ρ`. -/
private lemma hasDerivAt_huberFunction_at_right_boundary (ρ : Set.Ioi (0 : ℝ)) :
    HasDerivAt (huberFunction ρ) (ρ : ℝ) (ρ : ℝ) := by
  -- Route correction: the earlier `sup` normalization is false; at the boundary we instead match
  -- the left and right slope limits of the quadratic and affine branches.
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have hslope :
        slope (huberFunction ρ) (ρ : ℝ) =ᶠ[𝓝[<] (ρ : ℝ)] fun y : ℝ ↦ (y + (ρ : ℝ)) / 2 := by
      have hpos : Ioi (0 : ℝ) ∈ 𝓝[<] (ρ : ℝ) := by
        exact mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds ρ.2)
      filter_upwards [self_mem_nhdsWithin, hpos] with y hy_left hy_pos
      have hy_quad : huberFunction ρ y = y ^ 2 / 2 :=
        huberFunction_eq_quadratic ρ (by
          have hρ_neg : -(ρ : ℝ) < 0 := neg_lt_zero.mpr ρ.2
          exact (lt_trans hρ_neg hy_pos).le) hy_left.le
      have hρ_quad : huberFunction ρ (ρ : ℝ) = (ρ : ℝ) ^ 2 / 2 :=
        huberFunction_eq_quadratic ρ (neg_le_self (le_of_lt ρ.2)) le_rfl
      rw [slope_def_field, hy_quad, hρ_quad]
      have hy_ne : y - (ρ : ℝ) ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_lt hy_left)
      field_simp [hy_ne]
      ring
    have hlim : Tendsto (fun y : ℝ ↦ (y + (ρ : ℝ)) / 2) (𝓝[<] (ρ : ℝ)) (𝓝 (ρ : ℝ)) := by
      have hbase :
          Tendsto (fun y : ℝ ↦ (y + (ρ : ℝ)) / 2) (𝓝 (ρ : ℝ)) (𝓝 (((ρ : ℝ) + (ρ : ℝ)) / 2)) :=
        ((continuous_id'.add continuous_const).div_const (2 : ℝ)).continuousAt.tendsto
      simpa [two_mul] using hbase.mono_left nhdsWithin_le_nhds
    exact hlim.congr' hslope.symm
  · have hslope :
        slope (huberFunction ρ) (ρ : ℝ) =ᶠ[𝓝[>] (ρ : ℝ)] fun _ : ℝ ↦ (ρ : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_aff : huberFunction ρ y = (ρ : ℝ) * y - (ρ : ℝ) ^ 2 / 2 :=
        huberFunction_eq_affine_pos ρ hy
      have hρ_quad : huberFunction ρ (ρ : ℝ) = (ρ : ℝ) ^ 2 / 2 :=
        huberFunction_eq_quadratic ρ (neg_le_self (le_of_lt ρ.2)) le_rfl
      rw [slope_def_field, hy_aff, hρ_quad]
      have hy_ne : y - (ρ : ℝ) ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt hy)
      field_simp [hy_ne]
      ring
    exact tendsto_const_nhds.congr' hslope.symm

/-- Helper for Example 8.44: the derivative at the switching point `-ρ` is still `-ρ`. -/
private lemma hasDerivAt_huberFunction_at_left_boundary (ρ : Set.Ioi (0 : ℝ)) :
    HasDerivAt (huberFunction ρ) (-(ρ : ℝ)) (-(ρ : ℝ)) := by
  -- Match the left and right slope limits at the negative switching point.
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · have hslope :
        slope (huberFunction ρ) (-(ρ : ℝ)) =ᶠ[𝓝[<] (-(ρ : ℝ))] fun _ : ℝ ↦ -(ρ : ℝ) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      have hy_aff : huberFunction ρ y = -(ρ : ℝ) * y - (ρ : ℝ) ^ 2 / 2 :=
        huberFunction_eq_affine_neg ρ hy
      have hρ_quad : huberFunction ρ (-(ρ : ℝ)) = (-(ρ : ℝ)) ^ 2 / 2 :=
        huberFunction_eq_quadratic ρ le_rfl (neg_le_self (le_of_lt ρ.2))
      rw [slope_def_field, hy_aff, hρ_quad]
      have hy_ne : y - (-(ρ : ℝ)) ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_lt hy)
      field_simp [hy_ne]
      ring
    exact tendsto_const_nhds.congr' hslope.symm
  · have hslope :
        slope (huberFunction ρ) (-(ρ : ℝ)) =ᶠ[𝓝[>] (-(ρ : ℝ))]
          fun y : ℝ ↦ (y - (ρ : ℝ)) / 2 := by
      have hupper : Iio (ρ : ℝ) ∈ 𝓝[>] (-(ρ : ℝ)) := by
        have hρ_neg : -(ρ : ℝ) < 0 := neg_lt_zero.mpr ρ.2
        exact mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_trans hρ_neg ρ.2))
      filter_upwards [self_mem_nhdsWithin, hupper] with y hy_right hy_upper
      have hy_quad : huberFunction ρ y = y ^ 2 / 2 :=
        huberFunction_eq_quadratic ρ hy_right.le hy_upper.le
      have hρ_quad : huberFunction ρ (-(ρ : ℝ)) = (-(ρ : ℝ)) ^ 2 / 2 :=
        huberFunction_eq_quadratic ρ le_rfl (neg_le_self (le_of_lt ρ.2))
      rw [slope_def_field, hy_quad, hρ_quad]
      have hy_ne : y - (-(ρ : ℝ)) ≠ 0 := by
        exact sub_ne_zero.mpr (ne_of_gt hy_right)
      field_simp [hy_ne]
      ring
    have hlim : Tendsto (fun y : ℝ ↦ (y - (ρ : ℝ)) / 2) (𝓝[>] (-(ρ : ℝ))) (𝓝 (-(ρ : ℝ))) := by
      have hbase :
          Tendsto (fun y : ℝ ↦ (y - (ρ : ℝ)) / 2) (𝓝 (-(ρ : ℝ)))
            (𝓝 (((-(ρ : ℝ)) - (ρ : ℝ)) / 2)) :=
        ((continuous_id'.sub continuous_const).div_const (2 : ℝ)).continuousAt.tendsto
      simpa [sub_eq_add_neg, two_mul] using hbase.mono_left nhdsWithin_le_nhds
    exact hlim.congr' hslope.symm

/-- Helper for Example 8.44: on the closed middle interval `[-ρ, ρ]`, the derivative is `x`. -/
private lemma deriv_huberFunction_eq_self_of_mem_middle (ρ : Set.Ioi (0 : ℝ)) {x : ℝ}
    (hx_left : -(ρ : ℝ) ≤ x) (hx_right : x ≤ (ρ : ℝ)) :
    deriv (huberFunction ρ) x = x := by
  -- Reduce the closed interval to the interior and the two boundary points.
  rcases eq_or_lt_of_le hx_left with rfl | hx_left_strict
  · simpa using (hasDerivAt_huberFunction_at_left_boundary ρ).deriv
  · rcases eq_or_lt_of_le hx_right with rfl | hx_right_strict
    · simpa using (hasDerivAt_huberFunction_at_right_boundary ρ).deriv
    · simpa using (hasDerivAt_huberFunction_of_mem_middle ρ hx_left_strict hx_right_strict).deriv

/-- Helper for Example 8.44: the derivative of the Huber function is the clipped identity map. -/
private lemma deriv_huberFunction_eq_clamp (ρ : Set.Ioi (0 : ℝ)) (x : ℝ) :
    deriv (huberFunction ρ) x = max (-(ρ : ℝ)) (min x (ρ : ℝ)) := by
  -- The three derivative formulas glue into the monotone clamp `max (-ρ) (min x ρ)`.
  by_cases hx_left : x < -(ρ : ℝ)
  · rw [(hasDerivAt_huberFunction_of_lt_left ρ hx_left).deriv]
    have hmin : min x (ρ : ℝ) = x := by
      apply min_eq_left
      have hsplit : -(ρ : ℝ) < (ρ : ℝ) := by
        have hρ_neg : -(ρ : ℝ) < 0 := neg_lt_zero.mpr ρ.2
        exact lt_trans hρ_neg ρ.2
      have hx_lt_ρ : x < (ρ : ℝ) := lt_trans hx_left hsplit
      exact le_of_lt hx_lt_ρ
    rw [hmin, max_eq_left (le_of_lt hx_left)]
  · by_cases hx_right : x ≤ (ρ : ℝ)
    · rw [deriv_huberFunction_eq_self_of_mem_middle ρ (le_of_not_gt hx_left) hx_right]
      rw [min_eq_left hx_right, max_eq_right]
      linarith [le_of_not_gt hx_left]
    · rw [(hasDerivAt_huberFunction_of_lt_right ρ (lt_of_not_ge hx_right)).deriv]
      have hmin : min x (ρ : ℝ) = (ρ : ℝ) :=
        min_eq_right (le_of_lt (lt_of_not_ge hx_right))
      rw [hmin, max_eq_right]
      exact neg_le_self (le_of_lt ρ.2)

/-- Helper for Example 8.44: the Huber derivative is monotone on `ℝ`. -/
private lemma huberFunction_deriv_monotoneOn (ρ : Set.Ioi (0 : ℝ)) :
    MonotoneOn (deriv (huberFunction ρ)) Set.univ := by
  -- The clipped identity `x ↦ max (-ρ) (min x ρ)` is monotone.
  intro x hx y hy hxy
  rw [deriv_huberFunction_eq_clamp ρ x, deriv_huberFunction_eq_clamp ρ y]
  exact max_le_max le_rfl (min_le_min hxy le_rfl)

/-- Helper for Example 8.44: the Huber function is differentiable at every real point. -/
private lemma differentiableAt_huberFunction (ρ : Set.Ioi (0 : ℝ)) (x : ℝ) :
    DifferentiableAt ℝ (huberFunction ρ) x := by
  -- Assemble differentiability from the three regions and the two switching points.
  by_cases hx_left : x < -(ρ : ℝ)
  · exact (hasDerivAt_huberFunction_of_lt_left ρ hx_left).differentiableAt
  · by_cases hx_right : x ≤ (ρ : ℝ)
    · rcases eq_or_lt_of_le (le_of_not_gt hx_left) with rfl | hx_left_strict
      · exact (hasDerivAt_huberFunction_at_left_boundary ρ).differentiableAt
      · rcases eq_or_lt_of_le hx_right with rfl | hx_right_strict
        · exact (hasDerivAt_huberFunction_at_right_boundary ρ).differentiableAt
        · exact
            (hasDerivAt_huberFunction_of_mem_middle ρ hx_left_strict hx_right_strict).differentiableAt
    · exact (hasDerivAt_huberFunction_of_lt_right ρ (lt_of_not_ge hx_right)).differentiableAt

/-- Helper for Example 8.44: the Huber function is convex on all of `ℝ`. -/
private lemma huberFunction_convexOn_univ (ρ : Set.Ioi (0 : ℝ)) :
    ConvexOn ℝ Set.univ (huberFunction ρ) := by
  -- Proposition 8.14 applies on `Set.univ` because the derivative is the monotone clipped identity.
  refine
    convexOn_of_monotoneOn_deriv_openInterval Set.univ (huberFunction ρ)
      (by simpa using convex_univ) isOpen_univ ?_ (huberFunction_deriv_monotoneOn ρ)
  intro x hx
  exact (differentiableAt_huberFunction ρ x).differentiableWithinAt

/-- Example 8.44: for every threshold `ρ ∈ ℝ_{++}`, the Huber function is convex on `ℝ` and
continuous. -/
theorem huberFunction_convexOn_univ_and_continuous (ρ : Set.Ioi (0 : ℝ)) :
    let f : ℝ → ℝ :=
      {x : ℝ | (ρ : ℝ) < |x|}.piecewise
        (fun x ↦ (ρ : ℝ) * |x| - (ρ : ℝ) ^ 2 / 2)
        (fun x ↦ |x| ^ 2 / 2)
    ConvexOn ℝ Set.univ f ∧ Continuous f := by
  -- Route correction: the Huber function is not a supremum of its two displayed branches, so we
  -- follow the source proof and prove convexity from the monotonicity of the derivative instead.
  let f : ℝ → ℝ := huberFunction ρ
  have hconv : ConvexOn ℝ Set.univ f := by
    -- Proposition 8.14 gives convexity once the derivative has been shown monotone.
    simpa [f] using huberFunction_convexOn_univ ρ
  have hcont : Continuous f := by
    -- Corollary 8.40 upgrades global convexity on `ℝ` to continuity.
    simpa [f] using continuous_of_convexOn_univ f hconv
  simpa [f, huberFunction] using And.intro hconv hcont
