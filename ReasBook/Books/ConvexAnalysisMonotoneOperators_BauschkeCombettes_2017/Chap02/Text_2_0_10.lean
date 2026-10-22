/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Text_2_0_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Text 2.0.10: subtracting the normal correction sends `x` onto the closed
hyperplane with normal `u` and offset `η`. -/
private lemma orthogonal_foot_mem_closedHyperplane (x u : H) (η : ℝ) (hu : u ≠ 0) :
    x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u ∈ innerProductLevelSet u η := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  have hu_sq : ‖u‖ ^ 2 ≠ 0 := by
    rw [pow_two]
    exact mul_ne_zero hu_norm hu_norm
  -- Rewrite membership as the defining inner-product equation of the hyperplane.
  rw [mem_innerProductLevelSet_iff]
  -- Compute the inner product of the corrected point with the normal vector.
  calc
    ⟪x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u, u⟫_ℝ
        = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * ⟪u, u⟫_ℝ) := by
            rw [inner_sub_left, real_inner_smul_left]
    _ = ⟪x, u⟫_ℝ - (((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) * (‖u‖ ^ 2)) := by
            rw [real_inner_self_eq_norm_sq]
    _ = ⟪x, u⟫_ℝ - (⟪x, u⟫_ℝ - η) := by
            field_simp [hu_sq]
    _ = η := by
            ring

/-- Helper for Text 2.0.10: the distance from `x` to its orthogonal foot on
`innerProductLevelSet u η` is the normalized absolute inner-product defect. -/
private lemma dist_to_orthogonal_foot_eq_abs_inner_sub_div_norm (x u : H) (η : ℝ) (hu : u ≠ 0) :
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  have hu_norm : ‖u‖ ≠ 0 := by
    simpa using hu
  -- Collapse the distance to the norm of the normal correction vector.
  calc
    dist x (x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u)
        = ‖((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u‖ := by
            rw [dist_eq_norm]
            simp
    _ = |(⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2| * ‖u‖ := by
            rw [norm_smul, Real.norm_eq_abs]
    _ = (|⟪x, u⟫_ℝ - η| / (‖u‖ ^ 2)) * ‖u‖ := by
            rw [abs_div, abs_of_nonneg (sq_nonneg ‖u‖)]
    _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
            field_simp [pow_two, hu_norm]

/-- Helper for Text 2.0.10: every point of `innerProductLevelSet u η` is at least the normalized
inner-product defect away from `x`. -/
private lemma abs_inner_sub_div_norm_le_dist_of_mem_closedHyperplane
    (x y u : H) (η : ℝ) (hu : u ≠ 0) (hy : y ∈ innerProductLevelSet u η) :
    |⟪x, u⟫_ℝ - η| / ‖u‖ ≤ dist x y := by
  have hu_pos : 0 < ‖u‖ := norm_pos_iff.mpr hu
  have hy_eq : ⟪y, u⟫_ℝ = η := mem_innerProductLevelSet_iff.mp hy
  have hinner : ⟪x, u⟫_ℝ - η = ⟪x - y, u⟫_ℝ := by
    calc
      ⟪x, u⟫_ℝ - η = ⟪x, u⟫_ℝ - ⟪y, u⟫_ℝ := by
        rw [hy_eq]
      _ = ⟪x - y, u⟫_ℝ := by
        rw [inner_sub_left]
  have hcs : |⟪x - y, u⟫_ℝ| ≤ ‖x - y‖ * ‖u‖ := abs_real_inner_le_norm (x - y) u
  have hdiv : |⟪x - y, u⟫_ℝ| / ‖u‖ ≤ ‖x - y‖ := by
    exact (div_le_iff₀ hu_pos).2 (by simpa [mul_comm] using hcs)
  -- Replace the inner-product defect by the hyperplane equation and identify distance with a norm.
  simpa [hinner, dist_eq_norm] using hdiv

/-- Text 2.0.10: the distance from a point to the closed hyperplane `innerProductLevelSet u η` is
the absolute value of the inner-product defect `⟪x, u⟫_ℝ - η`, normalized by `‖u‖`. -/
-- Proof sketch: project `x` onto the hyperplane along the normal direction `u`, namely at
-- `x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u`, to get the upper bound, and use Cauchy-Schwarz on
-- `⟪x - y, u⟫_ℝ = ⟪x, u⟫_ℝ - η` for arbitrary `y ∈ innerProductLevelSet u η` to get the lower
-- bound.
theorem infDist_hyperplane_eq_abs_inner_sub_div_norm (x u : H) (η : ℝ) (hu : u ≠ 0) :
    Metric.infDist x (innerProductLevelSet u η) = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
  let p := x - ((⟪x, u⟫_ℝ - η) / ‖u‖ ^ 2) • u
  have hp : p ∈ innerProductLevelSet u η := by
    -- The textbook witness is exactly the orthogonal foot onto the affine hyperplane.
    simpa [p] using orthogonal_foot_mem_closedHyperplane x u η hu
  have hs : (innerProductLevelSet u η).Nonempty := ⟨p, hp⟩
  have hupper : Metric.infDist x (innerProductLevelSet u η) ≤ |⟪x, u⟫_ℝ - η| / ‖u‖ := by
    -- The explicit projection witness gives the required upper bound.
    calc
      Metric.infDist x (innerProductLevelSet u η) ≤ dist x p := Metric.infDist_le_dist_of_mem hp
      _ = |⟪x, u⟫_ℝ - η| / ‖u‖ := by
        simpa [p] using dist_to_orthogonal_foot_eq_abs_inner_sub_div_norm x u η hu
  have hlower : |⟪x, u⟫_ℝ - η| / ‖u‖ ≤ Metric.infDist x (innerProductLevelSet u η) := by
    -- Every point of the hyperplane satisfies the Cauchy-Schwarz lower bound.
    rw [Metric.le_infDist hs]
    intro y hy
    exact abs_inner_sub_div_norm_le_dist_of_mem_closedHyperplane x y u η hu hy
  exact le_antisymm hupper hlower
