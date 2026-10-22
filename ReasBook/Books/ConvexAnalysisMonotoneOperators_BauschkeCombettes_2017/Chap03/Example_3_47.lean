/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open ERealFunction

/-- The function `x ↦ 1 / (1 + |x|)` used in Example 3.47. -/
def inv_one_add_abs (x : ℝ) : ℝ :=
  1 / (1 + |x|)

/-- The set `C = {(x, r) ∈ ℝ² | 1 / (1 + |x|) ≤ r}` from Example 3.47, written as the canonical
epigraph of `x ↦ 1 / (1 + |x|)`. -/
abbrev epigraph_inv_one_add_abs : Set (ℝ × ℝ) :=
  epigraph fun x : ℝ ↦ (inv_one_add_abs x : EReal)

/-- Membership in the epigraph means that the second coordinate dominates `1 / (1 + |x|)`. -/
@[simp]
theorem mem_epigraph_inv_one_add_abs_iff (p : ℝ × ℝ) :
    p ∈ epigraph_inv_one_add_abs ↔ 1 / (1 + |p.1|) ≤ p.2 := by
  simpa [epigraph_inv_one_add_abs, inv_one_add_abs] using
    (mem_epigraph_iff (fun x : ℝ ↦ (inv_one_add_abs x : EReal)) p.1 p.2)

-- Proof sketch: the function `x ↦ 1 / (1 + |x|)` is continuous on `ℝ`, and the epigraph of a
-- continuous real-valued function over a closed domain is closed.
/-- The set `C = {(x, r) ∈ ℝ² | 1 / (1 + |x|) ≤ r}` from Example 3.47 is closed. -/
theorem isClosed_epigraph_inv_one_add_abs :
    IsClosed epigraph_inv_one_add_abs := by
  -- View the epigraph as a closed superlevel set of two continuous coordinate maps.
  have hcont :
      Continuous fun p : ℝ × ℝ ↦ 1 / (1 + |p.1|) := by
    simpa [one_div] using
      (continuous_const.add continuous_fst.abs).inv₀ (by
        intro p
        have hpos : 0 < 1 + |p.1| := by positivity
        exact ne_of_gt hpos)
  have hclosed : IsClosed {p : ℝ × ℝ | 1 / (1 + |p.1|) ≤ p.2} :=
    isClosed_le hcont continuous_snd
  convert hclosed using 1
  ext p
  exact mem_epigraph_inv_one_add_abs_iff p

/-- Helper for Example 3.47: every point of the epigraph has strictly positive second coordinate. -/
private lemma snd_pos_of_mem_epigraph_inv_one_add_abs (p : ℝ × ℝ)
    (hp : p ∈ epigraph_inv_one_add_abs) :
    0 < p.2 := by
  rw [mem_epigraph_inv_one_add_abs_iff] at hp
  have hden_pos : 0 < 1 + |p.1| := by positivity
  have hinv_pos : 0 < 1 / (1 + |p.1|) := by
    exact one_div_pos.mpr hden_pos
  -- The epigraph inequality bounds `p.2` below by a strictly positive quantity.
  linarith

/-- Helper for Example 3.47: every point of the open upper half-plane belongs to the convex hull of
the epigraph. -/
private lemma openUpperHalfPlane_subset_convexHull_epigraph_inv_one_add_abs (p : ℝ × ℝ)
    (hp : p ∈ Set.univ ×ˢ Set.Ioi (0 : ℝ)) :
    p ∈ convexHull ℝ epigraph_inv_one_add_abs := by
  rcases p with ⟨x, r⟩
  rcases Set.mem_prod.mp hp with ⟨_, hr_mem⟩
  rw [Set.mem_Ioi] at hr_mem
  let M : ℝ := max (|x| + 1) (1 / r)
  let t : ℝ := (M - x) / (2 * M)
  have hr : 0 < r := hr_mem
  have hMr : 1 / r ≤ M := by
    exact le_max_right (|x| + 1) (1 / r)
  have hM_pos : 0 < M := by
    have hr_inv_pos : 0 < 1 / r := one_div_pos.mpr hr
    exact lt_of_lt_of_le hr_inv_pos hMr
  have hx_abs_lt_M : |x| < M := by
    have hleft : |x| + 1 ≤ M := le_max_left (|x| + 1) (1 / r)
    linarith
  have hx_left : -M < x := by
    exact (abs_lt.mp hx_abs_lt_M).1
  have hx_right : x < M := by
    exact (abs_lt.mp hx_abs_lt_M).2
  have ht_mem : t ∈ Set.Icc (0 : ℝ) 1 := by
    have htwoM_pos : 0 < 2 * M := by positivity
    have hnum_nonneg : 0 ≤ M - x := by linarith
    have hnum_le : M - x ≤ 2 * M := by linarith
    refine ⟨?_, ?_⟩
    · exact div_nonneg hnum_nonneg (le_of_lt htwoM_pos)
    · exact (div_le_iff₀ htwoM_pos).2 (by simpa using hnum_le)
  have hsmall : 1 / (1 + M) < r := by
    have hden_pos : 0 < 1 + M := by linarith
    refine (one_div_lt hden_pos hr).2 ?_
    linarith
  have hM_abs : |M| = M := abs_of_nonneg (le_of_lt hM_pos)
  have hM_mem : (M, r) ∈ epigraph_inv_one_add_abs := by
    rw [mem_epigraph_inv_one_add_abs_iff]
    -- The right endpoint sits above the graph because `M` was chosen far enough out.
    exact le_of_lt (by
      simpa [hM_abs] using hsmall)
  have hnegM_mem : (-M, r) ∈ epigraph_inv_one_add_abs := by
    rw [mem_epigraph_inv_one_add_abs_iff]
    -- Symmetry of `|x|` gives the same estimate at `-M`.
    exact le_of_lt (by
      simpa [abs_neg, hM_abs] using hsmall)
  have hline :
      AffineMap.lineMap (M, r) (-M, r) t = (x, r) := by
    -- The chosen parameter places `(x, r)` on the segment joining `(M, r)` and `(-M, r)`.
    ext <;> simp [AffineMap.lineMap_apply_module, t]
    · field_simp [hM_pos.ne']
      ring
    · ring
  have hsegment :
      AffineMap.lineMap (M, r) (-M, r) t ∈ convexHull ℝ epigraph_inv_one_add_abs := by
    -- Convexity of the hull keeps the whole segment between the two epigraph points.
    exact
      (convex_convexHull ℝ epigraph_inv_one_add_abs).lineMap_mem
        (subset_convexHull ℝ epigraph_inv_one_add_abs hM_mem)
        (subset_convexHull ℝ epigraph_inv_one_add_abs hnegM_mem)
        ht_mem
  simpa [hline] using hsegment

-- Proof sketch: every point of the epigraph has strictly positive second coordinate, so the convex
-- hull lies in the open upper half-plane. Conversely, for `(x, r)` with `r > 0`, combine two
-- far-out epigraph points above `±M` to obtain a convex-hull point with second coordinate below
-- `r`, then use the upward-closed nature of the epigraph in the second coordinate.
/-- The convex hull of the closure of the epigraph is the open upper half-plane. -/
theorem convexHull_closure_epigraph_inv_one_add_abs_eq_openUpperHalfPlane :
    convexHull ℝ (closure epigraph_inv_one_add_abs) = Set.univ ×ˢ Set.Ioi (0 : ℝ) := by
  -- Route correction: identify the convex hull by two inclusions, using closedness first and
  -- then the explicit symmetric segment construction.
  apply le_antisymm
  · rw [isClosed_epigraph_inv_one_add_abs.closure_eq]
    refine convexHull_min ?_ ?_
    · intro p hp
      rw [Set.mem_prod, Set.mem_Ioi]
      exact ⟨by simp, snd_pos_of_mem_epigraph_inv_one_add_abs p hp⟩
    · exact convex_univ.prod (convex_Ioi (0 : ℝ))
  · intro p hp
    rw [isClosed_epigraph_inv_one_add_abs.closure_eq]
    exact openUpperHalfPlane_subset_convexHull_epigraph_inv_one_add_abs p hp

-- Proof sketch: identify the convex hull using the previous theorem and take closures; the closure
-- of the open upper half-plane is the closed upper half-plane.
/-- The closure of the convex hull of the epigraph is the closed upper half-plane. -/
theorem closure_convexHull_epigraph_inv_one_add_abs_eq_closedUpperHalfPlane :
    closure (convexHull ℝ epigraph_inv_one_add_abs) = Set.univ ×ˢ Set.Ici (0 : ℝ) := by
  -- Rewrite the convex hull using the previous theorem and then close the open upper half-plane.
  calc
    closure (convexHull ℝ epigraph_inv_one_add_abs)
        = closure (convexHull ℝ (closure epigraph_inv_one_add_abs)) := by
            rw [isClosed_epigraph_inv_one_add_abs.closure_eq]
    _ = closure (Set.univ ×ˢ Set.Ioi (0 : ℝ)) := by
          rw [convexHull_closure_epigraph_inv_one_add_abs_eq_openUpperHalfPlane]
    _ = Set.univ ×ˢ Set.Ici (0 : ℝ) := by
          rw [closure_prod_eq, closure_univ, closure_Ioi]

-- Proof sketch: combine the explicit descriptions of the two sets above and note that
-- `Set.univ ×ˢ Set.Ioi (0 : ℝ)` and `Set.univ ×ˢ Set.Ici (0 : ℝ)` are different.
/-- Example 3.47: for the closed set
`C = {(x, r) ∈ ℝ² | 1 / (1 + |x|) ≤ r}`, one has
`convexHull ℝ (closure C) ≠ closure (convexHull ℝ C)`. -/
theorem convexHull_closure_ne_closure_convexHull_of_epigraph_inv_one_add_abs :
    convexHull ℝ (closure epigraph_inv_one_add_abs) ≠
      closure (convexHull ℝ epigraph_inv_one_add_abs) := by
  intro hEq
  have horigin_mem :
      ((0 : ℝ), (0 : ℝ)) ∈ closure (convexHull ℝ epigraph_inv_one_add_abs) := by
    -- The origin lies in the closed upper half-plane description of the closure.
    rw [closure_convexHull_epigraph_inv_one_add_abs_eq_closedUpperHalfPlane]
    simp
  have horigin_mem_left :
      ((0 : ℝ), (0 : ℝ)) ∈ convexHull ℝ (closure epigraph_inv_one_add_abs) := by
    simpa [hEq] using horigin_mem
  have horigin_not_mem :
      ((0 : ℝ), (0 : ℝ)) ∉ convexHull ℝ (closure epigraph_inv_one_add_abs) := by
    -- The origin is excluded from the open upper half-plane description of the convex hull.
    rw [convexHull_closure_epigraph_inv_one_add_abs_eq_openUpperHalfPlane]
    simp
  exact horigin_not_mem horigin_mem_left

end
