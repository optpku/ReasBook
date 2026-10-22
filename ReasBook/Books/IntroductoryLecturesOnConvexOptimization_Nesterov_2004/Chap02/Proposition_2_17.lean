/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_26

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open PointedCone
open scoped Pointwise

local notation "Q" => reciprocalEpigraphOnPositiveRay

/-- The reciprocal epigraph owner set is convex. -/
theorem reciprocalEpigraphOnPositiveRay_convex : Convex ℝ reciprocalEpigraphOnPositiveRay := by
  intro x hx y hy a b ha hb hab
  rcases (mem_reciprocalEpigraphOnPositiveRay_iff x).1 hx with ⟨hx1, hx2⟩
  rcases (mem_reciprocalEpigraphOnPositiveRay_iff y).1 hy with ⟨hy1, hy2⟩
  refine (mem_reciprocalEpigraphOnPositiveRay_iff (a • x + b • y)).2 ?_
  constructor
  · have hpos : 0 < a * x.1 + b * y.1 := by
      by_cases ha0 : a = 0
      · have hb1 : b = 1 := by linarith
        simp [ha0, hb1, hy1]
      · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
        exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx1) (mul_nonneg hb hy1.le)
    simpa using hpos
  · have hrecip : 1 / (a * x.1 + b * y.1) ≤ a / x.1 + b / y.1 := by
      have hden : 0 < a * x.1 + b * y.1 := by
        by_cases ha0 : a = 0
        · have hb1 : b = 1 := by linarith
          simp [ha0, hb1, hy1]
        · have ha_pos : 0 < a := lt_of_le_of_ne ha (by simpa [eq_comm] using ha0)
          exact add_pos_of_pos_of_nonneg (mul_pos ha_pos hx1) (mul_nonneg hb hy1.le)
      field_simp [hden.ne', hx1.ne', hy1.ne']
      ring_nf
      have hsq : 2 * x.1 * y.1 ≤ x.1 ^ 2 + y.1 ^ 2 := by
        nlinarith [sq_nonneg (x.1 - y.1)]
      have hab_nonneg : 0 ≤ a * b := mul_nonneg ha hb
      have hpoly :
          x.1 * y.1 ≤
            x.1 * y.1 * a ^ 2 + x.1 * y.1 * b ^ 2 + x.1 ^ 2 * a * b + y.1 ^ 2 * a * b := by
        calc
          x.1 * y.1 = x.1 * y.1 * 1 := by ring
          _ = x.1 * y.1 * (a ^ 2 + 2 * (a * b) + b ^ 2) := by
                have hab_sq : a ^ 2 + 2 * (a * b) + b ^ 2 = 1 := by
                  nlinarith [hab]
                rw [hab_sq]
          _ =
              x.1 * y.1 * a ^ 2 + 2 * x.1 * y.1 * (a * b) + x.1 * y.1 * b ^ 2 := by
                ring
          _ ≤ x.1 * y.1 * a ^ 2 + (x.1 ^ 2 + y.1 ^ 2) * (a * b) + x.1 * y.1 * b ^ 2 := by
                gcongr
          _ =
              x.1 * y.1 * a ^ 2 + x.1 * y.1 * b ^ 2 + x.1 ^ 2 * a * b + y.1 ^ 2 * a * b := by
                ring
      exact hpoly
    have hbound : a / x.1 + b / y.1 ≤ a * x.2 + b * y.2 := by
      have hax : a / x.1 ≤ a * x.2 := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hx2 ha
      have hby : b / y.1 ≤ b * y.2 := by
        simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          mul_le_mul_of_nonneg_left hy2 hb
      exact add_le_add hax hby
    simpa [smul_add, add_comm, add_left_comm, add_assoc, smul_eq_mul] using
      le_trans hrecip hbound

/-- Helper for Proposition 2.17: the reciprocal epigraph contains the point `(1, 1)`. -/
private theorem reciprocalEpigraphOnPositiveRay_nonempty : Set.Nonempty Q := by
  -- We use the obvious point on the reciprocal graph to witness nonemptiness.
  exact ⟨(1, 1), (mem_reciprocalEpigraphOnPositiveRay_iff (1, 1)).2 ⟨zero_lt_one, by norm_num⟩⟩

/-- Helper for Proposition 2.17: a point of `convexHull ℝ (insert 0 Q)` lies on a segment from the
origin to a point of `Q`, hence is a scalar multiple `t • y` with `0 ≤ t ≤ 1`. -/
private theorem mem_convexHull_zero_insert_reciprocalEpigraph_iff (x : ℝ × ℝ) :
    x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) ↔
      ∃ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 ∧ x ∈ t • Q := by
  -- Rewrite the convex hull of `{0} ∪ Q` as the join of `{0}` with the convex set `Q`.
  rw [convexHull_insert reciprocalEpigraphOnPositiveRay_nonempty,
    reciprocalEpigraphOnPositiveRay_convex.convexHull_eq, convexJoin_singleton_left]
  simp only [mem_iUnion, exists_prop]
  constructor
  · rintro ⟨y, hy, hx⟩
    -- Unpack the segment description into the coefficient of `y`.
    rcases hx with ⟨a, t, ha, ht, hat, rfl⟩
    refine ⟨t, ⟨ht, by linarith⟩, y, hy, ?_⟩
    simp
  · rintro ⟨t, ht, y, hy, rfl⟩
    -- Conversely, every coefficient `t ∈ [0, 1]` gives a point on the segment `[0, y]`.
    refine ⟨y, hy, 1 - t, t, sub_nonneg.mpr ht.2, ht.1, by linarith, ?_⟩
    simp

/-- Helper for Proposition 2.17: scaling a point of `Q` by a factor at least `1` keeps it in `Q`.
-/
private theorem smul_mem_reciprocalEpigraphOnPositiveRay_of_one_le {t : ℝ} {y : ℝ × ℝ}
    (hy : y ∈ Q) (ht : 1 ≤ t) : t • y ∈ Q := by
  rcases (mem_reciprocalEpigraphOnPositiveRay_iff y).1 hy with ⟨hy1, hy2⟩
  have ht_pos : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have hy2_nonneg : 0 ≤ y.2 := le_trans (by positivity) hy2
  refine (mem_reciprocalEpigraphOnPositiveRay_iff (t • y)).2 ?_
  constructor
  · -- The first coordinate stays positive under a positive scaling.
    simpa [smul_eq_mul] using mul_pos ht_pos hy1
  · -- Compare reciprocals after scaling the first coordinate and use `t ≥ 1`.
    rw [show (t • y).1 = t * y.1 by simp [smul_eq_mul],
      show (t • y).2 = t * y.2 by simp [smul_eq_mul]]
    have h_inv_t : 1 / t ≤ 1 := by
      rw [div_le_iff₀ ht_pos]
      nlinarith
    have h_step : (1 / t) * (1 / y.1) ≤ 1 / y.1 := by
      nlinarith [h_inv_t, one_div_nonneg.mpr hy1.le]
    have h_mul : y.2 ≤ t * y.2 := by
      simpa [one_mul] using mul_le_mul_of_nonneg_right ht hy2_nonneg
    calc
      1 / (t * y.1) = (1 / t) * (1 / y.1) := by
        field_simp [ht_pos.ne', hy1.ne']
      _ ≤ 1 / y.1 := h_step
      _ ≤ y.2 := hy2
      _ ≤ t * y.2 := h_mul

/-- Helper for Proposition 2.17: every positive multiple of a point of `Q` belongs to
`convexHull ℝ (insert 0 Q)`. -/
private theorem positive_smul_mem_convexHull_zero_insert_of_mem_reciprocalEpigraph
    {t : ℝ} {y : ℝ × ℝ} (ht : 0 < t) (hy : y ∈ Q) :
    t • y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
  by_cases ht_one : t ≤ 1
  · -- When `t ≤ 1`, this is the segment from `0` to `y`.
    exact (mem_convexHull_zero_insert_reciprocalEpigraph_iff (t • y)).2
      ⟨t, ⟨ht.le, ht_one⟩, y, hy, rfl⟩
  · -- When `t ≥ 1`, first show `t • y ∈ Q`, then include it into the convex hull.
    have h_one_le : 1 ≤ t := le_of_not_ge ht_one
    exact subset_convexHull ℝ _ (mem_insert_of_mem _
      (smul_mem_reciprocalEpigraphOnPositiveRay_of_one_le hy h_one_le))

/-- Helper for Proposition 2.17: `convexHull ℝ (insert 0 Q)` is closed under nonnegative scalar
multiplication. -/
private theorem smul_mem_convexHull_zero_insert_reciprocalEpigraph_of_nonneg
    {x : ℝ × ℝ} {r : ℝ} (hx : x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q)) (hr : 0 ≤ r) :
    r • x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
  rcases (mem_convexHull_zero_insert_reciprocalEpigraph_iff x).1 hx with ⟨t, ht, y, hy, rfl⟩
  rw [smul_smul]
  by_cases hrt : r * t ≤ 1
  · -- If the new coefficient is still at most `1`, stay on the same segment.
    exact (mem_convexHull_zero_insert_reciprocalEpigraph_iff ((r * t) • y)).2
      ⟨r * t, ⟨mul_nonneg hr ht.1, hrt⟩, y, hy, rfl⟩
  · -- Otherwise the product coefficient is at least `1`, so the ray enters `Q` itself.
    have hrt_pos : 0 < r * t := lt_of_lt_of_le zero_lt_one (le_of_not_ge hrt)
    simpa [mul_assoc] using
      positive_smul_mem_convexHull_zero_insert_of_mem_reciprocalEpigraph hrt_pos hy

/-- Helper for Proposition 2.17: `convexHull ℝ (insert 0 Q)` is closed under conical combinations,
so it can be used as a pointed cone containing `Q`. -/
private theorem convexHull_zero_insert_reciprocalEpigraph_cone_comb
    {x y : ℝ × ℝ}
    (hx : x ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q))
    (hy : y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q))
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a • x + b • y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
  let s : ℝ := a + b
  by_cases hs : s = 0
  · -- If the total weight vanishes, both coefficients are zero.
    have ha_zero : a = 0 := by linarith
    have hb_zero : b = 0 := by linarith
    simpa [ha_zero, hb_zero] using
      (subset_convexHull ℝ (insert (0 : ℝ × ℝ) Q) (by simp : (0 : ℝ × ℝ) ∈ insert (0 : ℝ × ℝ) Q))
  · -- Otherwise normalize to a convex combination, then scale back by `s`.
    have hs_pos : 0 < s := by
      have hs_ne : a + b ≠ 0 := by
        simpa [s] using hs
      dsimp [s]
      exact lt_of_le_of_ne (add_nonneg ha hb) hs_ne.symm
    have hs_nonneg : 0 ≤ s := hs_pos.le
    have hconv :
        (a / s) • x + (b / s) • y ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) := by
      refine (convex_convexHull ℝ _ ) hx hy (div_nonneg ha hs_nonneg) (div_nonneg hb hs_nonneg) ?_
      have hsum : a / s + b / s = 1 := by
        dsimp [s]
        field_simp [hs_pos.ne']
        exact div_self hs_pos.ne'
      exact hsum
    have hsmul :
        s • ((a / s) • x + (b / s) • y) ∈ convexHull ℝ (insert (0 : ℝ × ℝ) Q) :=
      smul_mem_convexHull_zero_insert_reciprocalEpigraph_of_nonneg hconv hs_nonneg
    have hs_mul_a : s * (a / s) = a := by
      field_simp [hs_pos.ne']
    have hs_mul_b : s * (b / s) = b := by
      field_simp [hs_pos.ne']
    simpa [s, smul_add, smul_smul, hs_mul_a, hs_mul_b] using hsmul

/-- Proposition 2.17: the convex hull of `{(0, 0)} ∪ Q` equals the canonical cone hull of `Q`,
where `Q = reciprocalEpigraphOnPositiveRay`. -/
theorem convexHull_zero_union_reciprocalEpigraphOnPositiveRay_eq_conicHull :
    convexHull ℝ (insert (0 : ℝ × ℝ) reciprocalEpigraphOnPositiveRay) =
      (hull ℝ reciprocalEpigraphOnPositiveRay : Set (ℝ × ℝ)) := by
  -- Route correction: avoid the later Definition 2.28 shortcut and prove cone closure of the
  -- convex hull directly from its segment description.
  refine Subset.antisymm ?_ ?_
  · intro x hx
    -- Every convex-hull point has the form `t • y` with `0 ≤ t ≤ 1` and `y ∈ Q`.
    rcases (mem_convexHull_zero_insert_reciprocalEpigraph_iff x).1 hx with ⟨t, ht, y, hy, rfl⟩
    exact (hull ℝ Q).smul_mem ht.1 (subset_hull hy)
  · let C : PointedCone ℝ (ℝ × ℝ) :=
      PointedCone.ofConeComb
        (convexHull ℝ (insert (0 : ℝ × ℝ) Q))
        (by
          refine ⟨0, ?_⟩
          exact subset_convexHull ℝ _ (mem_insert 0 Q))
        (fun x hx y hy a ha b hb ↦
          convexHull_zero_insert_reciprocalEpigraph_cone_comb hx hy ha hb)
    have hQ : Q ⊆ C := by
      -- The convex hull contains `Q`, so the pointed hull of `Q` lies inside this cone.
      intro y hy
      exact subset_convexHull ℝ _ (mem_insert_of_mem _ hy)
    have hHull : hull ℝ Q ≤ C := Submodule.span_le.mpr hQ
    intro x hx
    exact hHull hx
