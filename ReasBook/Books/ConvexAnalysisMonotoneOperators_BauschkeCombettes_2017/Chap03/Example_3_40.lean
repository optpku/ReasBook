/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Pointwise

/-- The horizontal axis in `ℝ²`, viewed as the set `ℝ × {0}`. -/
def minkowskiCounterexample_horizontalAxis : Set (ℝ × ℝ) :=
  (Set.univ : Set ℝ) ×ˢ ({0} : Set ℝ)

/-- The first-quadrant region on or above the hyperbola `x₁ x₂ = 1`. -/
def minkowskiCounterexample_positiveProductRegion : Set (ℝ × ℝ) :=
  (Set.Ici (0 : ℝ) ×ˢ Set.Ici (0 : ℝ)) ∩ {x | 1 ≤ x.1 * x.2}

-- Proof sketch: unfold `minkowskiCounterexample_horizontalAxis`; membership is definitionally the
-- vanishing of the second coordinate.
/-- Membership in the horizontal-axis set is equivalent to having second coordinate `0`. -/
theorem mem_minkowskiCounterexample_horizontalAxis_iff (x : ℝ × ℝ) :
    x ∈ minkowskiCounterexample_horizontalAxis ↔ x.2 = 0 := by
  -- Unfolding the product-set definition reduces membership to the second-coordinate condition.
  simp [minkowskiCounterexample_horizontalAxis]

-- Proof sketch: unfold `minkowskiCounterexample_positiveProductRegion`; membership is exactly the
-- conjunction of first-quadrant inequalities and the product lower bound.
/-- Membership in the positive-product region means lying in the first quadrant with product at
least `1`. -/
theorem mem_minkowskiCounterexample_positiveProductRegion_iff (x : ℝ × ℝ) :
    x ∈ minkowskiCounterexample_positiveProductRegion ↔
      0 ≤ x.1 ∧ 0 ≤ x.2 ∧ 1 ≤ x.1 * x.2 := by
  -- This is the product-set description of the first quadrant plus the product lower bound.
  rw [minkowskiCounterexample_positiveProductRegion, Set.mem_inter_iff, Set.mem_prod]
  simp [and_assoc]

-- Proof sketch: identify the set as the zero-level set of the continuous map
-- `x ↦ x.2`.
/-- The horizontal axis is a closed subset of `ℝ²`. -/
theorem minkowskiCounterexample_horizontalAxis_isClosed :
    IsClosed minkowskiCounterexample_horizontalAxis := by
  -- `ℝ × {0}` is the product of two closed sets.
  simpa [minkowskiCounterexample_horizontalAxis] using
    (isClosed_univ : IsClosed (Set.univ : Set ℝ)).prod isClosed_singleton

-- Proof sketch: this set is a linear subspace, hence convex.
/-- The horizontal axis is convex. -/
theorem minkowskiCounterexample_horizontalAxis_convex :
    Convex ℝ minkowskiCounterexample_horizontalAxis := by
  -- `ℝ × {0}` is the product of two convex sets.
  simpa [minkowskiCounterexample_horizontalAxis] using
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)).prod (convex_singleton (0 : ℝ))

-- Proof sketch: write the region as the intersection of the closed first quadrant with the closed
-- superlevel set of the continuous map `x ↦ x.1 * x.2`.
/-- The positive-product region is closed in `ℝ²`. -/
theorem minkowskiCounterexample_positiveProductRegion_isClosed :
    IsClosed minkowskiCounterexample_positiveProductRegion := by
  have hquadrant : IsClosed ((Set.Ici (0 : ℝ) : Set ℝ) ×ˢ Set.Ici (0 : ℝ)) := by
    exact isClosed_Ici.prod isClosed_Ici
  have hprod :
      IsClosed {x : ℝ × ℝ | 1 ≤ x.1 * x.2} := by
    simpa using isClosed_le continuous_const (continuous_fst.mul continuous_snd)
  -- The region is the intersection of the closed first quadrant with a closed superlevel set.
  simpa [minkowskiCounterexample_positiveProductRegion] using hquadrant.inter hprod

/-- Helper for Example 3.40: every point in the positive-product region has strictly positive
second coordinate. -/
private lemma minkowskiCounterexample_positiveProductRegion_snd_pos (x : ℝ × ℝ)
    (hx : x ∈ minkowskiCounterexample_positiveProductRegion) :
    0 < x.2 := by
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff x).1 hx with
    ⟨hx1, hx2, hxprod⟩
  -- The product bound rules out `x.2 = 0`, while first-quadrant membership gives `x.2 ≥ 0`.
  by_contra h_not_pos
  have hx2eq : x.2 = 0 := by
    linarith
  nlinarith [hxprod, hx1, hx2eq]

/-- Helper for Example 3.40: the mixed cross term in the convexity computation is at least `2`. -/
private lemma minkowskiCounterexample_positiveProductRegion_cross_term_two_le
    (x y : ℝ × ℝ)
    (hx : x ∈ minkowskiCounterexample_positiveProductRegion)
    (hy : y ∈ minkowskiCounterexample_positiveProductRegion) :
    2 ≤ x.1 * y.2 + y.1 * x.2 := by
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff x).1 hx with
    ⟨hx1, hx2, hxprod⟩
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff y).1 hy with
    ⟨hy1, hy2, hyprod⟩
  have hcross_prod : 1 ≤ (x.1 * y.2) * (y.1 * x.2) := by
    nlinarith [hxprod, hyprod]
  have hleft_nonneg : 0 ≤ x.1 * y.2 := mul_nonneg hx1 hy2
  have hright_nonneg : 0 ≤ y.1 * x.2 := mul_nonneg hy1 hx2
  have hsquare : 0 ≤ (x.1 * y.2 - (y.1 * x.2)) ^ 2 := sq_nonneg _
  -- Apply AM-GM in polynomial form to the two nonnegative mixed terms.
  nlinarith

-- Proof sketch: use the standard convexity argument for the epigraph of `x ↦ 1 / x` on the
-- positive ray, equivalently the arithmetic-geometric-mean estimate in the textbook proof.
/-- The positive-product region is convex. -/
theorem minkowskiCounterexample_positiveProductRegion_convex :
    Convex ℝ minkowskiCounterexample_positiveProductRegion := by
  intro x hx y hy a b ha hb hab
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff x).1 hx with
    ⟨hx1, hx2, hxprod⟩
  rcases (mem_minkowskiCounterexample_positiveProductRegion_iff y).1 hy with
    ⟨hy1, hy2, hyprod⟩
  rw [mem_minkowskiCounterexample_positiveProductRegion_iff]
  refine ⟨add_nonneg (mul_nonneg ha hx1) (mul_nonneg hb hy1),
    add_nonneg (mul_nonneg ha hx2) (mul_nonneg hb hy2), ?_⟩
  have hcross :
      2 ≤ x.1 * y.2 + y.1 * x.2 :=
    minkowskiCounterexample_positiveProductRegion_cross_term_two_le x y hx hy
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
  have ha_sq_nonneg : 0 ≤ a ^ 2 := sq_nonneg a
  have hb_sq_nonneg : 0 ≤ b ^ 2 := sq_nonneg b
  -- Expand the product of the convex-combination coordinates and bound each summand below.
  calc
    1 = a ^ 2 * 1 + (a * b) * 2 + b ^ 2 * 1 := by
      nlinarith [hab]
    _ ≤ a ^ 2 * (x.1 * x.2)
          + (a * b) * (x.1 * y.2 + y.1 * x.2)
          + b ^ 2 * (y.1 * y.2) := by
      nlinarith [hxprod, hyprod, hcross, hab_nonneg, ha_sq_nonneg, hb_sq_nonneg]
    _ = (a * x.1 + b * y.1) * (a * x.2 + b * y.2) := by
      ring

/-- Helper for Example 3.40: every point in the open upper half-plane splits as a point on the
horizontal axis plus a point in the positive-product region. -/
private lemma upperHalfPlane_subset_minkowskiCounterexample_sum (p : ℝ × ℝ)
    (hp : p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ)) :
    p ∈ minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion := by
  rcases p with ⟨a, b⟩
  rcases Set.mem_prod.mp hp with ⟨_, hb_mem⟩
  rw [Set.mem_Ioi] at hb_mem
  rw [Set.mem_add]
  have hb_ne : b ≠ 0 := ne_of_gt hb_mem
  have hrecip_mul : b⁻¹ * b = 1 := by
    simpa [one_div] using one_div_mul_cancel hb_ne
  have haxis : (a - 1 / b, 0) ∈ minkowskiCounterexample_horizontalAxis := by
    -- The first summand lies on the horizontal axis by construction.
    simp [mem_minkowskiCounterexample_horizontalAxis_iff]
  have hregion : (1 / b, b) ∈ minkowskiCounterexample_positiveProductRegion := by
    -- The second summand lies in the region because `b > 0` and `(1 / b) * b = 1`.
    rw [mem_minkowskiCounterexample_positiveProductRegion_iff]
    refine ⟨le_of_lt (one_div_pos.mpr hb_mem), le_of_lt hb_mem, ?_⟩
    simp [one_div, hrecip_mul]
  have hsum : (a - 1 / b, 0) + (1 / b, b) = (a, b) := by
    -- This is the explicit decomposition used in the textbook proof.
    simp
  exact ⟨(a - 1 / b, 0), haxis, (1 / b, b), hregion, hsum⟩

/-- Helper for Example 3.40: every point in the Minkowski sum has strictly positive second
coordinate. -/
private lemma minkowskiCounterexample_sum_subset_upperHalfPlane (p : ℝ × ℝ)
    (hp : p ∈ minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion) :
    p ∈ (Set.univ : Set ℝ) ×ˢ Set.Ioi (0 : ℝ) := by
  rcases Set.mem_add.mp hp with ⟨c, hc, d, hd, rfl⟩
  rw [Set.mem_prod, Set.mem_Ioi]
  constructor
  · simp
  · have hd2 : 0 < d.2 :=
      minkowskiCounterexample_positiveProductRegion_snd_pos d hd
    rw [mem_minkowskiCounterexample_horizontalAxis_iff] at hc
    -- Adding a horizontal-axis point leaves the second coordinate unchanged.
    simpa [hc] using hd2

-- Proof sketch: for `b > 0`, decompose `(a, b)` as `(a - 1 / b, 0) + (1 / b, b)`, and conversely
-- observe that every point of the Minkowski sum has strictly positive second coordinate because
-- every point of the positive-product region does, yielding exactly `Set.univ ×ˢ Set.Ioi 0`.
/-- Example 3.40: for `C = ℝ × {0}` and
`D = {(ξ₁, ξ₂) ∈ ℝ² | 0 ≤ ξ₁ ∧ 0 ≤ ξ₂ ∧ 1 ≤ ξ₁ * ξ₂}`, the Minkowski sum is the open upper
half-plane `ℝ × ℝ_{++}`, i.e. `Set.univ ×ˢ Set.Ioi (0 : ℝ)`. -/
theorem minkowskiCounterexample_sum_eq_upperHalfPlane :
    minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion =
      Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
  -- Route correction: compute the sum by explicit two-sided inclusion, not by topological
  -- properties of the sum itself.
  ext p
  constructor
  · exact minkowskiCounterexample_sum_subset_upperHalfPlane p
  · exact upperHalfPlane_subset_minkowskiCounterexample_sum p

-- Proof sketch: rewrite the sum using `minkowskiCounterexample_sum_eq_upperHalfPlane` and use that
-- `Set.univ ×ˢ Set.Ioi (0 : ℝ)` is open as the product of the open sets `Set.univ` and `Set.Ioi 0`.
/-- The Minkowski sum in Example 3.40 is an open subset of `ℝ²`. -/
theorem minkowskiCounterexample_sum_isOpen :
    IsOpen
      (minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion) :=
  by
  -- Rewrite the sum as the open upper half-plane.
  rw [minkowskiCounterexample_sum_eq_upperHalfPlane]
  simpa using isOpen_univ.prod isOpen_Ioi

-- Proof sketch: combine `minkowskiCounterexample_sum_eq_upperHalfPlane` with the fact that the
-- open upper half-plane is not closed in `ℝ²`.
/-- The Minkowski sum in Example 3.40 is not closed. -/
theorem minkowskiCounterexample_sum_not_isClosed :
    ¬ IsClosed
      (minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion) :=
  by
  intro hClosed
  have hclosure :
      closure
          (minkowskiCounterexample_horizontalAxis
            + minkowskiCounterexample_positiveProductRegion) =
        (Set.univ : Set ℝ) ×ˢ Set.Ici (0 : ℝ) := by
    -- The closure of the open upper half-plane is the closed upper half-plane.
    rw [minkowskiCounterexample_sum_eq_upperHalfPlane, closure_prod_eq, closure_univ, closure_Ioi]
  have horigin_closure :
      ((0 : ℝ), (0 : ℝ)) ∈
        closure
          (minkowskiCounterexample_horizontalAxis
            + minkowskiCounterexample_positiveProductRegion) := by
    rw [hclosure]
    simp
  have horigin :
      ((0 : ℝ), (0 : ℝ)) ∈
        minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion := by
    rw [← hClosed.closure_eq]
    exact horigin_closure
  have horigin_not :
      ((0 : ℝ), (0 : ℝ)) ∉
        minkowskiCounterexample_horizontalAxis + minkowskiCounterexample_positiveProductRegion := by
    rw [minkowskiCounterexample_sum_eq_upperHalfPlane]
    simp
  exact horigin_not horigin
