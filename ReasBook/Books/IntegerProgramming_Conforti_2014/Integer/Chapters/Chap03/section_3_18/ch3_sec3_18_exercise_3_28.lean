/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_5.ch3_sec3_5_definition_3_5_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_11.ch3_sec3_11_definition_3_11_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

-- The exercise below is source-facing in the chapter owner `polytope_skeleton`; its supporting
-- edge criterion is already owned upstream by `polytope_skeleton_adj_iff`, so this file keeps no
-- duplicate ambient-point wrapper.

/-- Helper for Exercise 3.28: a finite system of linear inequalities defines a convex set. -/
lemma polyhedron_le_set_convex
    {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Convex ℝ (polyhedron_le_set A b) := by
  -- Each defining inequality is preserved by convex combinations, so the whole feasible region is.
  intro x hx y hy a c ha hc hac
  intro i
  have hx_i : (Matrix.mulVec A x) i ≤ b i := hx i
  have hy_i : (Matrix.mulVec A y) i ≤ b i := hy i
  calc
    (Matrix.mulVec A (a • x + c • y)) i = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
      calc
        ∑ j, A i j * (a * x j + c * y j)
            = ∑ j, (a * (A i j * x j) + c * (A i j * y j)) := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                ring
        _ = (∑ j, a * (A i j * x j)) + ∑ j, c * (A i j * y j) := by
              rw [Finset.sum_add_distrib]
        _ = a * (Matrix.mulVec A x) i + c * (Matrix.mulVec A y) i := by
              simp [Matrix.mulVec, dotProduct, Finset.mul_sum]
    _ ≤ a * b i + c * b i := by
      exact add_le_add (mul_le_mul_of_nonneg_left hx_i ha) (mul_le_mul_of_nonneg_left hy_i hc)
    _ = b i := by
      rw [← add_mul, hac, one_mul]

/-- Helper for Exercise 3.28: every polyhedron is convex. -/
lemma convex_of_is_polyhedron
    {n : ℕ} {P : Set (Fin n → ℝ)} (hP : is_polyhedron P) :
    Convex ℝ P := by
  -- Unfold the polyhedral presentation and apply the matrix-inequality convexity lemma.
  rcases hP with ⟨m, A, b, rfl⟩
  exact polyhedron_le_set_convex A b

/-- Helper for Exercise 3.28: an extreme segment cannot have its midpoint on a chord whose
endpoints both lie in `P` outside that segment. -/
lemma midpoint_not_mem_segment_of_points_outside_of_isExtreme_segment
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w : Fin n → ℝ}
    (hExtreme : IsExtreme ℝ P (segment ℝ v w)) :
    ∀ x ∈ P \ segment ℝ v w, ∀ y ∈ P \ segment ℝ v w, midpoint ℝ v w ∉ segment ℝ x y := by
  intro x hx y hy hmid_xy
  rcases hx with ⟨hxP, hxOutside⟩
  rcases hy with ⟨hyP, hyOutside⟩
  have hmid_seg : midpoint ℝ v w ∈ segment ℝ v w := midpoint_mem_segment (𝕜 := ℝ) v w
  have hx_ne : x ≠ midpoint ℝ v w := by
    intro hx_mid
    exact hxOutside (hx_mid ▸ hmid_seg)
  have hy_ne : y ≠ midpoint ℝ v w := by
    intro hy_mid
    exact hyOutside (hy_mid ▸ hmid_seg)
  -- The midpoint lies strictly between `x` and `y`, so extremality forces `x` into the segment.
  have hmid_open : midpoint ℝ v w ∈ openSegment ℝ x y :=
    mem_openSegment_of_ne_left_right hx_ne hy_ne hmid_xy
  have hx_seg : x ∈ segment ℝ v w :=
    hExtreme.left_mem_of_mem_openSegment hxP hyP hmid_seg hmid_open
  exact hxOutside hx_seg

/-- Helper for Exercise 3.28: among `r` and `1 - r`, one lies across `1 / 2` from `t`, so the
midpoint parameter `1 / 2` belongs to the scalar segment from `t` to that chosen coefficient. -/
lemma midpoint_parameter_of_open_segment_coefficients
    {r t : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) 1) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ q s : ℝ, (q = r ∨ q = 1 - r) ∧ s ∈ Set.Icc (0 : ℝ) 1 ∧
      AffineMap.lineMap t q s = (1 / 2 : ℝ) := by
  rcases hr with ⟨hr0, hr1⟩
  rcases ht with ⟨ht0, ht1⟩
  -- Choose whichever of `r` or `1 - r` puts `1 / 2` in the unordered interval with `t`.
  by_cases ht_half : t ≤ (1 / 2 : ℝ)
  · by_cases hr_half : (1 / 2 : ℝ) ≤ r
    · have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t r := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_le ht_half hr_half
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t r] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨r, s, Or.inl rfl, hs, hs_eq⟩
    · have hr_half' : r < (1 / 2 : ℝ) := lt_of_not_ge hr_half
      have hhalf_one_sub : (1 / 2 : ℝ) ≤ 1 - r := by linarith
      have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t (1 - r) := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_le ht_half hhalf_one_sub
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t (1 - r)] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨1 - r, s, Or.inr rfl, hs, hs_eq⟩
  · have ht_half' : (1 / 2 : ℝ) < t := lt_of_not_ge ht_half
    by_cases hr_half : r ≤ (1 / 2 : ℝ)
    · have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t r := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_ge hr_half ht_half'.le
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t r] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨r, s, Or.inl rfl, hs, hs_eq⟩
    · have hr_half' : (1 / 2 : ℝ) < r := lt_of_not_ge hr_half
      have hone_sub_le : 1 - r ≤ (1 / 2 : ℝ) := by linarith
      have hmid_seg : (1 / 2 : ℝ) ∈ segment ℝ t (1 - r) := by
        rw [segment_eq_uIcc]
        exact Set.mem_uIcc_of_ge hone_sub_le ht_half'.le
      rw [segment_eq_image_lineMap (𝕜 := ℝ) t (1 - r)] at hmid_seg
      rcases hmid_seg with ⟨s, hs, hs_eq⟩
      exact ⟨1 - r, s, Or.inr rfl, hs, hs_eq⟩

/-- Helper for Exercise 3.28: sliding both endpoints of a chord toward the same target commutes
with taking the same chord parameter. -/
lemma lineMap_lineMap_same_target
    {n : ℕ} (x y a : Fin n → ℝ) (r s : ℝ) :
    AffineMap.lineMap (AffineMap.lineMap x a s) (AffineMap.lineMap y a s) r =
      AffineMap.lineMap (AffineMap.lineMap x y r) a s := by
  -- Reassociate the affine combinations so the common target `a` is factored out.
  ext i
  simp [AffineMap.lineMap_apply_module]
  ring

/-- Helper for Exercise 3.28: an extreme edge has no further points of `P` on the extension of
its supporting line beyond either endpoint. -/
lemma extreme_endpoints_forbid_outside_collinear_point
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w u : Fin n → ℝ}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w)
    (huP : u ∈ P) {a : ℝ} (hu : u = AffineMap.lineMap v w a) (ha : a < 0 ∨ 1 < a) :
    False := by
  rcases ha with ha | ha
  · -- A negative coefficient puts `v` strictly between `u` and `w`, contradicting extremality.
    have hs : -a / (1 - a) ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · have hden : 0 < 1 - a := by linarith
        exact div_pos (by linarith) hden
      · have hden : 0 < 1 - a := by linarith
        have hne : 1 - a ≠ 0 := ne_of_gt hden
        have hlt : -a / (1 - a) < 1 := by
          field_simp [hne]
          linarith
        exact hlt
    have hv_open : v ∈ openSegment ℝ u w := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨-a / (1 - a), hs, ?_⟩
      rw [hu, AffineMap.lineMap_lineMap_left]
      have hne : 1 - a ≠ 0 := by linarith
      have hparam : 1 - (1 - -a / (1 - a)) * (1 - a) = (0 : ℝ) := by
        field_simp [hne]
        ring
      rw [hparam, AffineMap.lineMap_apply_zero]
    have hu_eq_v : u = v := (mem_extremePoints_iff_left.mp hv).2 u huP w hw.1 hv_open
    have hu_line_eq : AffineMap.lineMap v w a = v := by
      rw [← hu, hu_eq_v]
    have ha_zero : a = 0 :=
      (AffineMap.lineMap_eq_left_iff.mp hu_line_eq).resolve_left hvw
    linarith
  · -- A coefficient beyond `1` puts `w` strictly between `v` and `u`, contradicting extremality.
    have hs : 1 / a ∈ Set.Ioo (0 : ℝ) 1 := by
      constructor
      · have ha_pos : 0 < a := by linarith
        exact one_div_pos.mpr ha_pos
      · have ha_pos : 0 < a := by linarith
        have hlt : 1 / a < 1 := by
          field_simp [ha_pos.ne']
          linarith
        exact hlt
    have hw_open : w ∈ openSegment ℝ v u := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨1 / a, hs, ?_⟩
      rw [hu, AffineMap.lineMap_lineMap_right]
      have hne : a ≠ 0 := by linarith
      have hparam : (1 / a) * a = (1 : ℝ) := by
        field_simp [hne]
      rw [hparam, AffineMap.lineMap_apply_one]
    have hv_eq_w : v = w := (mem_extremePoints_iff_left.mp hw).2 v hv.1 u huP hw_open
    exact hvw hv_eq_w

/-- Helper for Exercise 3.28: a point of `P` outside the edge segment is not collinear with the
edge, so together with the edge direction it forms a linearly independent pair. -/
lemma outside_point_linearIndependent_with_edge
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w u : Fin n → ℝ}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w)
    (huP : u ∈ P) (huOutside : u ∉ segment ℝ v w) :
    LinearIndependent ℝ ![u - v, w - v] := by
  -- Route correction: instead of unfolding a large intersection argument immediately, first rule
  -- out every collinear outside point by extremality and then package the result as linear
  -- independence.
  have hpair : LinearIndependent ℝ ![w - v, u - v] := by
    apply (LinearIndependent.pair_iff' (by simpa using sub_ne_zero.mpr hvw.symm)).2
    intro a ha
    have hu_line : u = AffineMap.lineMap v w a := by
      ext i
      have hai := congrArg (fun p => p i) ha
      simp [AffineMap.lineMap_apply_module] at hai ⊢
      linarith
    have haOutside : a < 0 ∨ 1 < a := by
      by_contra haIcc
      have haIcc' : a ∈ Set.Icc (0 : ℝ) 1 := by
        constructor
        · by_contra ha0
          exact haIcc (Or.inl (lt_of_not_ge ha0))
        · by_contra ha1
          exact haIcc (Or.inr (lt_of_not_ge ha1))
      exact huOutside (hu_line ▸ lineMap_mem_segment (𝕜 := ℝ) v w haIcc')
    exact
      (extreme_endpoints_forbid_outside_collinear_point
        hv hw hvw huP hu_line haOutside).elim
  simpa using (LinearIndependent.pair_symm_iff.mp hpair)

/-- Helper for Exercise 3.28: a strict slide from an outside point toward an endpoint of the edge
cannot land back on the edge in the transverse case. -/
lemma slid_endpoint_outside_segment_of_transverse_point
    {n : ℕ} {v w u : Fin n → ℝ} (huOutside : u ∉ segment ℝ v w)
    (hlin : LinearIndependent ℝ ![u - v, w - v]) {s : ℝ} (hs : s ∈ Set.Ioo (0 : ℝ) 1) :
    AffineMap.lineMap u v s ∉ segment ℝ v w := by
  intro hSeg
  -- The slid point lies on both segments `[v, u]` and `[v, w]`, so linear independence forces it
  -- to be the common endpoint `v`.
  have huv_seg : AffineMap.lineMap u v s ∈ segment ℝ v u := by
    simpa [segment_symm] using
      (openSegment_subset_segment (𝕜 := ℝ) u v
        (lineMap_mem_openSegment (𝕜 := ℝ) u v hs))
  have hmem :
      AffineMap.lineMap u v s ∈ segment ℝ v u ∩ segment ℝ v w := ⟨huv_seg, hSeg⟩
  have hEq : AffineMap.lineMap u v s = v := by
    have hInter :
        segment ℝ v u ∩ segment ℝ v w = ({v} : Set (Fin n → ℝ)) :=
      segment_inter_eq_endpoint_of_linearIndependent_sub (𝕜 := ℝ) (c := v) (x := u) (y := w) hlin
    have hsingleton : AffineMap.lineMap u v s ∈ ({v} : Set (Fin n → ℝ)) := by
      simpa [hInter] using hmem
    simpa using hsingleton
  have hu_ne_v : u ≠ v := by
    intro hu_eq
    exact huOutside (hu_eq ▸ left_mem_segment ℝ v w)
  have hs_one : s = 1 := (AffineMap.lineMap_eq_right_iff.mp hEq).resolve_left hu_ne_v
  exact hs.2.ne hs_one

/-- Helper for Exercise 3.28: if an interior chord of `P` meets the edge at an interior point and
one endpoint lies outside the edge segment, then the other endpoint must lie outside as well. -/
lemma other_endpoint_outside_segment_of_interior_chord
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w x y z : Fin n → ℝ}
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w)
    (hzSeg : z ∈ openSegment ℝ v w) (hzChord : z ∈ openSegment ℝ x y)
    (hxP : x ∈ P) (hyP : y ∈ P) (hxOutside : x ∉ segment ℝ v w) :
    y ∉ segment ℝ v w := by
  intro hySeg
  -- If `y` were on the edge, then the chord equality would force `x` onto the same line, which
  -- the extreme-point obstruction forbids.
  rw [openSegment_eq_image_lineMap] at hzSeg hzChord
  rw [segment_eq_image_lineMap] at hySeg
  rcases hzSeg with ⟨t, ht, hzvw⟩
  rcases hzChord with ⟨r, hr, hzxy⟩
  rcases hySeg with ⟨b, hb, hyLine⟩
  have hr_ne : 1 - r ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hr.2))
  let a : ℝ := (t - r * b) / (1 - r)
  have hxLine : x = AffineMap.lineMap v w a := by
    ext i
    have hzvw_i : (1 - t) * v i + t * w i = z i := by
      simpa [AffineMap.lineMap_apply_module] using congrArg (fun p => p i) hzvw
    have hzxy_i : (1 - r) * x i + r * y i = z i := by
      simpa [AffineMap.lineMap_apply_module] using congrArg (fun p => p i) hzxy
    have hy_i : y i = (1 - b) * v i + b * w i := by
      simpa [AffineMap.lineMap_apply_module] using (congrArg (fun p => p i) hyLine).symm
    have hz_eq :
        (1 - r) * x i + r * ((1 - b) * v i + b * w i) = (1 - t) * v i + t * w i := by
      calc
        (1 - r) * x i + r * ((1 - b) * v i + b * w i)
            = (1 - r) * x i + r * y i := by rw [hy_i]
        _ = z i := hzxy_i
        _ = (1 - t) * v i + t * w i := hzvw_i.symm
    have hMul :
        (1 - r) * x i = ((1 - r) - (t - r * b)) * v i + (t - r * b) * w i := by
      nlinarith [hz_eq]
    have hLineMul :
        (AffineMap.lineMap v w a) i * (1 - r) =
          ((1 - r) - (t - r * b)) * v i + (t - r * b) * w i := by
      simp [AffineMap.lineMap_apply_module, a]
      field_simp [a, hr_ne]
    have hEqMul : x i * (1 - r) = (AffineMap.lineMap v w a) i * (1 - r) := by
      calc
        x i * (1 - r) = ((1 - r) - (t - r * b)) * v i + (t - r * b) * w i := by
          simpa [mul_comm] using hMul
        _ = (AffineMap.lineMap v w a) i * (1 - r) := hLineMul.symm
    have hEqMulLeft : (1 - r) * x i = (1 - r) * (AffineMap.lineMap v w a) i := by
      simpa [mul_comm] using hEqMul
    exact (mul_right_inj' hr_ne).mp hEqMulLeft
  have haOutside : a < 0 ∨ 1 < a := by
    by_contra haIcc
    have haIcc' : a ∈ Set.Icc (0 : ℝ) 1 := by
      constructor
      · by_contra ha0
        exact haIcc (Or.inl (lt_of_not_ge ha0))
      · by_contra ha1
        exact haIcc (Or.inr (lt_of_not_ge ha1))
    exact hxOutside (hxLine ▸ lineMap_mem_segment (𝕜 := ℝ) v w haIcc')
  exact
    extreme_endpoints_forbid_outside_collinear_point
      hv hw hvw hxP hxLine haOutside

/-- Helper for Exercise 3.28: an interior witness chord can be slid toward the appropriate edge
endpoint until it passes through the midpoint, while the new endpoints remain outside the edge. -/
lemma midpoint_witness_of_interior_chord
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w x y z : Fin n → ℝ}
    (hconvexP : Convex ℝ P) (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hvw : v ≠ w) (hzSeg : z ∈ openSegment ℝ v w) (hzChord : z ∈ openSegment ℝ x y)
    (hxP : x ∈ P) (hyP : y ∈ P) (hxOutside : x ∉ segment ℝ v w) (hyOutside : y ∉ segment ℝ v w) :
    ∃ x' y', x' ∈ P \ segment ℝ v w ∧ y' ∈ P \ segment ℝ v w ∧
      midpoint ℝ v w ∈ segment ℝ x' y' := by
  rw [openSegment_eq_image_lineMap] at hzSeg hzChord
  rcases hzSeg with ⟨t, ht, hzvw⟩
  rcases hzChord with ⟨r, hr, hzxy⟩
  by_cases ht_half : t = (1 / 2 : ℝ)
  · -- If `z` is already the midpoint of the edge, the original outside chord is enough.
    refine ⟨x, y, ⟨hxP, hxOutside⟩, ⟨hyP, hyOutside⟩, ?_⟩
    have hhalf : (⅟2 : ℝ) = (1 / 2 : ℝ) := by norm_num
    have hmid_eq : midpoint ℝ v w = z := by
      simpa [midpoint, hhalf, ht_half] using hzvw
    rw [hmid_eq]
    rw [segment_eq_image_lineMap]
    exact ⟨r, ⟨hr.1.le, hr.2.le⟩, hzxy⟩
  · have ht_lt_or_gt : t < (1 / 2 : ℝ) ∨ (1 / 2 : ℝ) < t := lt_or_gt_of_ne ht_half
    rcases ht_lt_or_gt with ht_lt | ht_gt
    · -- Slide both endpoints toward `w`, because the midpoint lies strictly between `z` and `w`.
      have hhalf_open : (1 / 2 : ℝ) ∈ openSegment ℝ t 1 := by
        rw [openSegment_eq_Ioo ht.2]
        exact ⟨ht_lt, by norm_num⟩
      rw [openSegment_eq_image_lineMap] at hhalf_open
      rcases hhalf_open with ⟨s, hs, hs_eq⟩
      let x' : Fin n → ℝ := AffineMap.lineMap x w s
      let y' : Fin n → ℝ := AffineMap.lineMap y w s
      have hmid_eq : midpoint ℝ v w = AffineMap.lineMap z w s := by
        have hhalf : (⅟2 : ℝ) = (1 / 2 : ℝ) := by norm_num
        have hs_map := congrArg (AffineMap.lineMap v w) hs_eq
        simpa [midpoint, hhalf, hzvw] using hs_map.symm
      have hx'P : x' ∈ P := by
        exact hconvexP.segment_subset hxP hw.1
          (lineMap_mem_segment (𝕜 := ℝ) x w ⟨hs.1.le, hs.2.le⟩)
      have hy'P : y' ∈ P := by
        exact hconvexP.segment_subset hyP hw.1
          (lineMap_mem_segment (𝕜 := ℝ) y w ⟨hs.1.le, hs.2.le⟩)
      have hxLin :
          LinearIndependent ℝ ![x - w, v - w] := by
        simpa [segment_symm] using
          (outside_point_linearIndependent_with_edge
            (v := w) (w := v) hw hv (Ne.symm hvw) hxP (by simpa [segment_symm] using hxOutside))
      have hyLin :
          LinearIndependent ℝ ![y - w, v - w] := by
        simpa [segment_symm] using
          (outside_point_linearIndependent_with_edge
            (v := w) (w := v) hw hv (Ne.symm hvw) hyP (by simpa [segment_symm] using hyOutside))
      have hx'Outside : x' ∉ segment ℝ v w := by
        have hx'Outside' :
            x' ∉ segment ℝ w v :=
          slid_endpoint_outside_segment_of_transverse_point
            (v := w) (w := v) (u := x) (by simpa [segment_symm] using hxOutside) hxLin hs
        simpa [segment_symm, x'] using hx'Outside'
      have hy'Outside : y' ∉ segment ℝ v w := by
        have hy'Outside' :
            y' ∉ segment ℝ w v :=
          slid_endpoint_outside_segment_of_transverse_point
            (v := w) (w := v) (u := y) (by simpa [segment_symm] using hyOutside) hyLin hs
        simpa [segment_symm, y'] using hy'Outside'
      refine ⟨x', y', ⟨hx'P, hx'Outside⟩, ⟨hy'P, hy'Outside⟩, ?_⟩
      rw [segment_eq_image_lineMap]
      refine ⟨r, ⟨hr.1.le, hr.2.le⟩, ?_⟩
      calc
        AffineMap.lineMap x' y' r = AffineMap.lineMap z w s := by
          simpa [x', y', hzxy] using (lineMap_lineMap_same_target x y w r s)
        _ = midpoint ℝ v w := hmid_eq.symm
    · -- Slide both endpoints toward `v`, because the midpoint lies strictly between `z` and `v`.
      have hhalf_open : (1 / 2 : ℝ) ∈ openSegment ℝ t 0 := by
        rw [openSegment_symm, openSegment_eq_Ioo ht.1]
        exact ⟨by norm_num, ht_gt⟩
      rw [openSegment_eq_image_lineMap] at hhalf_open
      rcases hhalf_open with ⟨s, hs, hs_eq⟩
      let x' : Fin n → ℝ := AffineMap.lineMap x v s
      let y' : Fin n → ℝ := AffineMap.lineMap y v s
      have hmid_eq : midpoint ℝ v w = AffineMap.lineMap z v s := by
        have hhalf : (⅟2 : ℝ) = (1 / 2 : ℝ) := by norm_num
        have hs_map := congrArg (AffineMap.lineMap v w) hs_eq
        simpa [midpoint, hhalf, hzvw] using hs_map.symm
      have hx'P : x' ∈ P := by
        exact hconvexP.segment_subset hxP hv.1
          (lineMap_mem_segment (𝕜 := ℝ) x v ⟨hs.1.le, hs.2.le⟩)
      have hy'P : y' ∈ P := by
        exact hconvexP.segment_subset hyP hv.1
          (lineMap_mem_segment (𝕜 := ℝ) y v ⟨hs.1.le, hs.2.le⟩)
      have hxLin :
          LinearIndependent ℝ ![x - v, w - v] :=
        outside_point_linearIndependent_with_edge hv hw hvw hxP hxOutside
      have hyLin :
          LinearIndependent ℝ ![y - v, w - v] :=
        outside_point_linearIndependent_with_edge hv hw hvw hyP hyOutside
      have hx'Outside : x' ∉ segment ℝ v w := by
        simpa [x'] using
          (slid_endpoint_outside_segment_of_transverse_point
            (v := v) (w := w) (u := x) hxOutside hxLin hs)
      have hy'Outside : y' ∉ segment ℝ v w := by
        simpa [y'] using
          (slid_endpoint_outside_segment_of_transverse_point
            (v := v) (w := w) (u := y) hyOutside hyLin hs)
      refine ⟨x', y', ⟨hx'P, hx'Outside⟩, ⟨hy'P, hy'Outside⟩, ?_⟩
      rw [segment_eq_image_lineMap]
      refine ⟨r, ⟨hr.1.le, hr.2.le⟩, ?_⟩
      calc
        AffineMap.lineMap x' y' r = AffineMap.lineMap z v s := by
          simpa [x', y', hzxy] using (lineMap_lineMap_same_target x y v r s)
        _ = midpoint ℝ v w := hmid_eq.symm

/-- Helper for Exercise 3.28: for the segment joining two distinct vertices of a convex set,
extremality implies the midpoint obstruction, and the converse reduces to the source proof's
interior-chord reparameterization step. -/
lemma isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w : Fin n → ℝ}
    (hconvexP : Convex ℝ P) (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ)
    (hvw : v ≠ w) :
    IsExtreme ℝ P (segment ℝ v w) ↔
      ∀ x ∈ P \ segment ℝ v w, ∀ y ∈ P \ segment ℝ v w, midpoint ℝ v w ∉ segment ℝ x y := by
  constructor
  · intro hExtreme
    -- The forward implication is the direct extremality contradiction at the midpoint.
    exact midpoint_not_mem_segment_of_points_outside_of_isExtreme_segment hExtreme
  · intro hmidpoint
    refine ⟨hconvexP.segment_subset hv.1 hw.1, ?_⟩
    intro x hxP y hyP z hzSeg hzOpen
    rw [← insert_endpoints_openSegment (𝕜 := ℝ) v w, Set.mem_insert_iff, Set.mem_insert_iff] at hzSeg
    rcases hzSeg with hzv | hzSeg
    · -- If the witness point is `v`, extremality of the vertex forces the left endpoint to be `v`.
      subst z
      have hx_eq : x = v := (mem_extremePoints_iff_left.mp hv).2 x hxP y hyP <| by
        simpa using hzOpen
      simpa [hx_eq] using left_mem_segment (𝕜 := ℝ) v w
    rcases hzSeg with hzw | hzInterior
    · -- The symmetric endpoint case is handled by the same extreme-point criterion at `w`.
      subst z
      have hx_eq : x = w := (mem_extremePoints_iff_left.mp hw).2 x hxP y hyP <| by
        simpa using hzOpen
      simpa [hx_eq, segment_symm] using left_mem_segment (𝕜 := ℝ) w v
    · -- TODO: follow the source route. Parameterize the two open segments by `lineMap`, use
      -- the interior witness point to build a new outside chord through the midpoint, then
      -- contradict the midpoint obstruction.
      -- Route correction: the failing earlier route bundled all geometric cases into one slide.
      -- Here we first show the second endpoint is outside, then slide both endpoints toward the
      -- appropriate edge endpoint according to the position of `z`.
      by_contra hxOutside
      have hyOutside :
          y ∉ segment ℝ v w :=
        other_endpoint_outside_segment_of_interior_chord
          hv hw hvw hzInterior hzOpen hxP hyP hxOutside
      rcases
          midpoint_witness_of_interior_chord
            hconvexP hv hw hvw hzInterior hzOpen hxP hyP hxOutside hyOutside with
        ⟨x', y', hx', hy', hmid⟩
      exact hmidpoint x' hx' y' hy' hmid

/-- Exercise 3.28. Two distinct vertices `v` and `w` of a polyhedron `P` are adjacent if and only
if the midpoint of `v` and `w` is not contained in any segment joining two points of `P` that
both lie outside the segment joining `v` and `w`. -/
theorem adjacent_vertices_iff_midpoint_not_mem_segment_of_points_outside_segment
    {n : ℕ} {P : Set (Fin n → ℝ)} {v w : Fin n → ℝ} (hP : is_polyhedron P)
    (hv : v ∈ P.extremePoints ℝ) (hw : w ∈ P.extremePoints ℝ) (hvw : v ≠ w) :
    (polytope_skeleton P).Adj ⟨v, hv⟩ ⟨w, hw⟩ ↔
      ∀ x ∈ P \ segment ℝ v w, ∀ y ∈ P \ segment ℝ v w, midpoint ℝ v w ∉ segment ℝ x y := by
  have hconvexP : Convex ℝ P := convex_of_is_polyhedron hP
  rw [polytope_skeleton_adj_iff]
  constructor
  · rintro ⟨_, hEdge⟩
    -- Rewrite adjacency to an extreme-segment statement, then apply the midpoint obstruction.
    have hExtreme : IsExtreme ℝ P (segment ℝ v w) := (isEdgeOf_segment_iff hvw).1 hEdge
    exact
      (isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
        hconvexP hv hw hvw).1 hExtreme
  · intro hmidpoint
    -- The converse uses the packaged midpoint-obstruction-to-extremality implication.
    refine ⟨?_, ?_⟩
    · intro hEq
      exact hvw (congrArg Subtype.val hEq)
    · have hExtreme : IsExtreme ℝ P (segment ℝ v w) :=
        (isExtreme_segment_iff_midpoint_not_mem_segment_of_points_outside_segment
          hconvexP hv hw hvw).2 hmidpoint
      exact (isEdgeOf_segment_iff hvw).2 hExtreme
