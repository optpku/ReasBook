import Mathlib.Analysis.Convex.Join
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1

open scoped BigOperators Matrix

-- Domain-style sampling for this refine pass:
-- * primary domain: integral split disjunctions for matrix polyhedra;
-- * core/canonical owners inspected in Chapter 5: `split_branch_lower`, `split_branch_upper`,
--   and `split_hull`;
-- * bridge/view owner used here: `split_polyhedron`;
-- * source-facing content kept here: Lemma 5.3 itself.

section Lemma53

variable {m n : ℕ} {I : Finset (Fin n)}

/-- Helper for Lemma 5.3: `split_dot` is affine along line segments. -/
lemma splitDot_lineMap
    (s : Split I)
    (x y : Fin n → ℝ)
    (t : ℝ) :
    split_dot s (AffineMap.lineMap x y t) =
      (1 - t) * split_dot s x + t * split_dot s y := by
  -- Rewrite the split dot product coordinatewise so the line-map coefficients factor through
  -- the finite sum.
  rw [split_dot_eq_sum, split_dot_eq_sum, split_dot_eq_sum]
  calc
    ∑ j : Fin n, (s j : ℝ) * (AffineMap.lineMap x y t) j
        = ∑ j : Fin n, ((1 - t) * ((s j : ℝ) * x j) + t * ((s j : ℝ) * y j)) := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [AffineMap.lineMap_apply_module]
            ring
    _ = ∑ j : Fin n, (1 - t) * ((s j : ℝ) * x j) + ∑ j : Fin n, t * ((s j : ℝ) * y j) := by
          rw [Finset.sum_add_distrib]
    _ = (1 - t) * split_dot s x + t * split_dot s y := by
          rw [← Finset.mul_sum, ← Finset.mul_sum, split_dot_eq_sum, split_dot_eq_sum]

/-- Helper for Lemma 5.3: the lower split branch of a matrix polyhedron is convex. -/
lemma splitBranchLowerConvex
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Split I) :
    Convex ℝ (split_branch_lower (polyhedron_le_set A b) s s.π0) := by
  intro x hx y hy a c ha hc hac
  rcases (mem_split_branch_lower_iff.mp hx) with ⟨hxP, hxlower⟩
  rcases (mem_split_branch_lower_iff.mp hy) with ⟨hyP, hylower⟩
  have haeq : a = 1 - c := by
    linarith
  have hline :
      a • x + c • y = AffineMap.lineMap x y c := by
    ext i
    simp [AffineMap.lineMap_apply_module, haeq]
  refine (mem_split_branch_lower_iff).2 ⟨?_, ?_⟩
  · -- The ambient matrix polyhedron is convex.
    exact (polyhedron_le_set_convex A b) hxP hyP ha hc hac
  · -- The split-dot lower inequality is preserved by convex combinations.
    rw [hline, splitDot_lineMap]
    have hsplit :
        (1 - c) * split_dot s x + c * split_dot s y ≤
          (1 - c) * (s.π0 : ℝ) + c * (s.π0 : ℝ) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxlower (sub_nonneg.mpr (by linarith)))
        (mul_le_mul_of_nonneg_left hylower hc)
    have hπ : (1 - c) * (s.π0 : ℝ) + c * (s.π0 : ℝ) = (s.π0 : ℝ) := by
      nlinarith
    exact hsplit.trans_eq hπ

/-- Helper for Lemma 5.3: the upper split branch of a matrix polyhedron is convex. -/
lemma splitBranchUpperConvex
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Split I) :
    Convex ℝ (split_branch_upper (polyhedron_le_set A b) s s.π0) := by
  intro x hx y hy a c ha hc hac
  rcases (mem_split_branch_upper_iff.mp hx) with ⟨hxP, hxupper⟩
  rcases (mem_split_branch_upper_iff.mp hy) with ⟨hyP, hyupper⟩
  have haeq : a = 1 - c := by
    linarith
  have hline :
      a • x + c • y = AffineMap.lineMap x y c := by
    ext i
    simp [AffineMap.lineMap_apply_module, haeq]
  refine (mem_split_branch_upper_iff).2 ⟨?_, ?_⟩
  · -- The ambient matrix polyhedron is convex.
    exact (polyhedron_le_set_convex A b) hxP hyP ha hc hac
  · -- The split-dot upper inequality is preserved by convex combinations.
    rw [hline, splitDot_lineMap]
    have hsplit :
        (1 - c) * ((s.π0 : ℝ) + 1) + c * ((s.π0 : ℝ) + 1) ≤
          (1 - c) * split_dot s x + c * split_dot s y := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hxupper (sub_nonneg.mpr (by linarith)))
        (mul_le_mul_of_nonneg_left hyupper hc)
    have hπ : (1 - c) * ((s.π0 : ℝ) + 1) + c * ((s.π0 : ℝ) + 1) = (s.π0 : ℝ) + 1 := by
      nlinarith
    simpa [hπ] using hsplit

/-- Helper for Lemma 5.3: a strip point of the split polyhedron lies on a boundary-normalized
segment joining the lower and upper split branches. -/
lemma existsRawBranchChord_of_memSplitPolyhedron_strip
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Split I)
    (xbar : Fin n → ℝ)
    (hxbar_strip : xbar ∈ split_strip s s.π0)
    (hxbar : xbar ∈ split_polyhedron A b s) :
    ∃ xlower0 xupper0 : Fin n → ℝ,
      ∃ t : ℝ,
        xlower0 ∈ split_branch_lower (polyhedron_le_set A b) s s.π0 ∧
        xupper0 ∈ split_branch_upper (polyhedron_le_set A b) s s.π0 ∧
        t ∈ Set.Ioo (0 : ℝ) 1 ∧
        xbar = AffineMap.lineMap xlower0 xupper0 t := by
  let L := split_branch_lower (polyhedron_le_set A b) s s.π0
  let U := split_branch_upper (polyhedron_le_set A b) s s.π0
  have hL_convex : Convex ℝ L := by
    simpa [L] using splitBranchLowerConvex A b s
  have hU_convex : Convex ℝ U := by
    simpa [U] using splitBranchUpperConvex A b s
  have hxbar_not_lower : xbar ∉ L := by
    intro hx
    rcases (mem_split_strip_iff.mp hxbar_strip) with ⟨hgt, _⟩
    have hlower : split_dot s xbar ≤ (s.π0 : ℝ) := by
      simpa [L] using (mem_split_branch_lower_iff.mp hx).2
    linarith
  have hxbar_not_upper : xbar ∉ U := by
    intro hx
    rcases (mem_split_strip_iff.mp hxbar_strip) with ⟨_, hlt⟩
    have hupper : (s.π0 : ℝ) + 1 ≤ split_dot s xbar := by
      simpa [U] using (mem_split_branch_upper_iff.mp hx).2
    linarith
  have hL_nonempty : L.Nonempty := by
    by_contra hL_empty
    have hxbar_hull : xbar ∈ convexHull ℝ (L ∪ U) := by
      simpa [split_polyhedron, split_hull, L, U] using hxbar
    have hUnion : L ∪ U = U := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact False.elim (hL_empty ⟨x, hx⟩)
        · exact hx
      · intro hx
        exact Or.inr hx
    have hxbar_upper : xbar ∈ U := by
      have : xbar ∈ convexHull ℝ U := by
        simpa [hUnion] using hxbar_hull
      simpa [convexHull_eq_self.2 hU_convex] using this
    exact hxbar_not_upper hxbar_upper
  have hU_nonempty : U.Nonempty := by
    by_contra hU_empty
    have hxbar_hull : xbar ∈ convexHull ℝ (L ∪ U) := by
      simpa [split_polyhedron, split_hull, L, U] using hxbar
    have hUnion : L ∪ U = L := by
      ext x
      constructor
      · intro hx
        rcases hx with hx | hx
        · exact hx
        · exact False.elim (hU_empty ⟨x, hx⟩)
      · intro hx
        exact Or.inl hx
    have hxbar_lower : xbar ∈ L := by
      have : xbar ∈ convexHull ℝ L := by
        simpa [hUnion] using hxbar_hull
      simpa [convexHull_eq_self.2 hL_convex] using this
    exact hxbar_not_lower hxbar_lower
  have hxbar_join : xbar ∈ convexJoin ℝ L U := by
    have hxbar_hull : xbar ∈ convexHull ℝ (L ∪ U) := by
      simpa [split_polyhedron, split_hull, L, U] using hxbar
    rw [hL_convex.convexHull_union hU_convex hL_nonempty hU_nonempty] at hxbar_hull
    exact hxbar_hull
  rcases mem_convexJoin.mp hxbar_join with ⟨xlower0, hxlower0, xupper0, hxupper0, hxbar_seg⟩
  rw [segment_eq_image_lineMap] at hxbar_seg
  rcases hxbar_seg with ⟨t, ht, hline⟩
  have ht_ne_zero : t ≠ 0 := by
    intro ht0
    have hxbar_eq : xbar = xlower0 := by
      simpa [ht0] using hline.symm
    apply hxbar_not_lower
    simpa [hxbar_eq, L] using hxlower0
  have ht_ne_one : t ≠ 1 := by
    intro ht1
    have hxbar_eq : xbar = xupper0 := by
      simpa [ht1] using hline.symm
    apply hxbar_not_upper
    simpa [hxbar_eq, U] using hxupper0
  have ht_pos : 0 < t := by
    exact lt_of_le_of_ne ht.1 (by simpa using ht_ne_zero.symm)
  have ht_lt_one : t < 1 := by
    exact lt_of_le_of_ne ht.2 (by simpa using ht_ne_one)
  exact ⟨xlower0, xupper0, t, by
    simpa [L] using hxlower0, by
    simpa [U] using hxupper0, ⟨ht_pos, ht_lt_one⟩, hline.symm⟩

/-- Helper for Lemma 5.3: the slack vector of a matrix system is affine along line segments. -/
lemma slackLineMap
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (x y : Fin n → ℝ)
    (t : ℝ) :
    b - A *ᵥ (AffineMap.lineMap x y t) =
      (1 - t) • (b - A *ᵥ x) + t • (b - A *ᵥ y) := by
  -- Push the matrix action through the affine combination, then collect the rowwise slacks.
  calc
    b - A *ᵥ (AffineMap.lineMap x y t)
        = b - ((1 - t) • (A *ᵥ x) + t • (A *ᵥ y)) := by
            rw [AffineMap.lineMap_apply_module, Matrix.mulVec_add, Matrix.mulVec_smul,
              Matrix.mulVec_smul]
    _ = (1 - t) • (b - A *ᵥ x) + t • (b - A *ᵥ y) := by
          ext i
          simp
          ring

/-- Helper for Lemma 5.3: a lower-branch point on the boundary chord controls the upper slack. -/
lemma upperSlackBound_of_boundaryBranchPair
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Split I)
    (xbar xlower xtilde : Fin n → ℝ)
    (δ : ℝ)
    (hδ_pos : 0 < δ)
    (hδ_lt_one : δ < 1)
    (hxlower : xlower ∈ split_branch_lower (polyhedron_le_set A b) s s.π0)
    (hxbar_repr :
      xbar = (1 - δ) • xlower + δ • xtilde) :
    b - A *ᵥ xtilde ≤ δ⁻¹ • (b - A *ᵥ xbar) := by
  have hxbar_line : xbar = AffineMap.lineMap xlower xtilde δ := by
    simpa [AffineMap.lineMap_apply_module] using hxbar_repr
  have hxlower_poly : A *ᵥ xlower ≤ b := by
    exact mem_polyhedron_le_set_iff.mp (mem_split_branch_lower_iff.mp hxlower).1
  have hslack :
      b - A *ᵥ xbar =
        (1 - δ) • (b - A *ᵥ xlower) + δ • (b - A *ᵥ xtilde) := by
    rw [hxbar_line]
    exact slackLineMap A b xlower xtilde δ
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  intro i
  have hlower_nonneg : 0 ≤ (b - A *ᵥ xlower) i := by
    simpa using sub_nonneg.mpr (hxlower_poly i)
  have hscaled : δ * (b - A *ᵥ xtilde) i ≤ (b - A *ᵥ xbar) i := by
    have hrow := congrFun hslack i
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] at hrow
    have hOneMinus_nonneg : 0 ≤ 1 - δ := by
      linarith
    have hnonneg_term : 0 ≤ (1 - δ) * (b - A *ᵥ xlower) i := by
      exact mul_nonneg hOneMinus_nonneg hlower_nonneg
    have hdiff_nonneg : 0 ≤ (b - A *ᵥ xbar) i - δ * (b - A *ᵥ xtilde) i := by
      calc
        0 ≤ (1 - δ) * (b - A *ᵥ xlower) i := hnonneg_term
        _ = (b - A *ᵥ xbar) i - δ * (b - A *ᵥ xtilde) i := by
              rw [hrow]
              ring
    exact sub_nonneg.mp hdiff_nonneg
  have hmul := mul_le_mul_of_nonneg_left hscaled (inv_nonneg.mpr hδ_pos.le)
  simpa [Pi.smul_apply, hδ_ne, mul_assoc, mul_left_comm, mul_comm] using hmul

/-- Helper for Lemma 5.3: a strip point of the split polyhedron lies on a boundary-normalized
segment joining the lower and upper split branches. -/
lemma existsBoundaryBranchPair_of_memSplitPolyhedron_strip
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Split I)
    (xbar : Fin n → ℝ)
    (hxbar_strip : xbar ∈ split_strip s s.π0)
    (hxbar : xbar ∈ split_polyhedron A b s) :
    ∃ xlower xtilde : Fin n → ℝ,
      xlower ∈ split_branch_lower (polyhedron_le_set A b) s s.π0 ∧
      split_dot s xlower = (s.π0 : ℝ) ∧
      xtilde ∈ split_branch_upper (polyhedron_le_set A b) s s.π0 ∧
      split_dot s xtilde = (s.π0 : ℝ) + 1 ∧
      xbar =
        (1 - (split_dot s xbar - (s.π0 : ℝ))) • xlower +
          (split_dot s xbar - (s.π0 : ℝ)) • xtilde := by
  -- Route correction: first extract a raw lower-upper chord from the split hull, then move its
  -- endpoints to the boundary levels `π₀` and `π₀ + 1` on the same line.
  rcases existsRawBranchChord_of_memSplitPolyhedron_strip A b s xbar hxbar_strip hxbar with
    ⟨xlower0, xupper0, t, hxlower0, hxupper0, ht, hxbar_line⟩
  let δ : ℝ := split_dot s xbar - (s.π0 : ℝ)
  let α : ℝ :=
    ((s.π0 : ℝ) - split_dot s xlower0) /
      (split_dot s xupper0 - split_dot s xlower0)
  let β : ℝ :=
    (((s.π0 : ℝ) + 1) - split_dot s xlower0) /
      (split_dot s xupper0 - split_dot s xlower0)
  let xlower : Fin n → ℝ := AffineMap.lineMap xlower0 xupper0 α
  let xtilde : Fin n → ℝ := AffineMap.lineMap xlower0 xupper0 β
  have hxlower0_poly : xlower0 ∈ polyhedron_le_set A b := (mem_split_branch_lower_iff.mp hxlower0).1
  have hxupper0_poly : xupper0 ∈ polyhedron_le_set A b := (mem_split_branch_upper_iff.mp hxupper0).1
  have hxlower0_split : split_dot s xlower0 ≤ (s.π0 : ℝ) :=
    (mem_split_branch_lower_iff.mp hxlower0).2
  have hxupper0_split : (s.π0 : ℝ) + 1 ≤ split_dot s xupper0 :=
    (mem_split_branch_upper_iff.mp hxupper0).2
  have hδ_bounds : 0 < δ ∧ δ < 1 := by
    rcases mem_split_strip_iff.mp hxbar_strip with ⟨hleft, hright⟩
    constructor
    · dsimp [δ]
      linarith
    · dsimp [δ]
      linarith
  have hden_pos : 0 < split_dot s xupper0 - split_dot s xlower0 := by
    linarith
  have hden_ne : split_dot s xupper0 - split_dot s xlower0 ≠ 0 := ne_of_gt hden_pos
  have hα_nonneg : 0 ≤ α := by
    dsimp [α]
    exact div_nonneg (by linarith) hden_pos.le
  have hα_le_one : α ≤ 1 := by
    dsimp [α]
    have hnum_le :
        (s.π0 : ℝ) - split_dot s xlower0 ≤
          split_dot s xupper0 - split_dot s xlower0 := by
      linarith
    exact (div_le_iff₀ hden_pos).2 (by simpa using hnum_le)
  have hβ_nonneg : 0 ≤ β := by
    dsimp [β]
    exact div_nonneg (by linarith) hden_pos.le
  have hβ_le_one : β ≤ 1 := by
    dsimp [β]
    have hnum_le :
        ((s.π0 : ℝ) + 1) - split_dot s xlower0 ≤
          split_dot s xupper0 - split_dot s xlower0 := by
      linarith
    exact (div_le_iff₀ hden_pos).2 (by simpa using hnum_le)
  have hxlower_poly : xlower ∈ polyhedron_le_set A b := by
    -- The boundary lower point stays in the ambient polyhedron because it lies on the raw chord.
    dsimp [xlower]
    simpa [AffineMap.lineMap_apply_module] using
      (polyhedron_le_set_convex A b) hxlower0_poly hxupper0_poly
        (sub_nonneg.mpr hα_le_one) hα_nonneg (by linarith)
  have hxtilde_poly : xtilde ∈ polyhedron_le_set A b := by
    -- The boundary upper point is another convex combination of the same raw chord endpoints.
    dsimp [xtilde]
    simpa [AffineMap.lineMap_apply_module] using
      (polyhedron_le_set_convex A b) hxlower0_poly hxupper0_poly
        (sub_nonneg.mpr hβ_le_one) hβ_nonneg (by linarith)
  have hxlower_split_eq : split_dot s xlower = (s.π0 : ℝ) := by
    -- Evaluating the split functional along the chord fixes the lower boundary point at `π₀`.
    dsimp [xlower, α]
    rw [splitDot_lineMap]
    field_simp [hden_ne]
    ring
  have hxtilde_split_eq : split_dot s xtilde = (s.π0 : ℝ) + 1 := by
    -- The same one-dimensional normalization fixes the upper boundary point at `π₀ + 1`.
    dsimp [xtilde, β]
    rw [splitDot_lineMap]
    field_simp [hden_ne]
    ring
  have hxbar_split_line :
      split_dot s xbar =
        (1 - t) * split_dot s xlower0 + t * split_dot s xupper0 := by
    simpa [hxbar_line] using splitDot_lineMap s xlower0 xupper0 t
  have hδ_formula :
      δ = t * (split_dot s xupper0 - split_dot s xlower0) +
        (split_dot s xlower0 - (s.π0 : ℝ)) := by
    dsimp [δ]
    rw [hxbar_split_line]
    ring
  have ht_formula : (1 - δ) * α + δ * β = t := by
    calc
      (1 - δ) * α + δ * β
          = (((s.π0 : ℝ) - split_dot s xlower0) + δ) /
              (split_dot s xupper0 - split_dot s xlower0) := by
              dsimp [α, β]
              field_simp [hden_ne]
              ring
      _ = t := by
            rw [hδ_formula]
            field_simp [hden_ne]
            ring
  have hxbar_boundary :
      xbar = AffineMap.lineMap xlower xtilde δ := by
    -- The boundary points stay on the original line, and the strip value `δ` is exactly the new
    -- line parameter between them.
    calc
      xbar = AffineMap.lineMap xlower0 xupper0 t := hxbar_line
      _ = AffineMap.lineMap xlower0 xupper0 ((1 - δ) * α + δ * β) := by
            rw [ht_formula]
      _ = AffineMap.lineMap xlower xtilde δ := by
            ext i
            simp [xlower, xtilde, AffineMap.lineMap_apply_module]
            ring_nf
  have hxlower_mem : xlower ∈ split_branch_lower (polyhedron_le_set A b) s s.π0 := by
    refine (mem_split_branch_lower_iff).2 ⟨hxlower_poly, ?_⟩
    simp [hxlower_split_eq]
  have hxtilde_mem : xtilde ∈ split_branch_upper (polyhedron_le_set A b) s s.π0 := by
    refine (mem_split_branch_upper_iff).2 ⟨hxtilde_poly, ?_⟩
    simp [hxtilde_split_eq]
  refine ⟨xlower, xtilde, hxlower_mem, hxlower_split_eq, hxtilde_mem, hxtilde_split_eq, ?_⟩
  simpa [δ, AffineMap.lineMap_apply_module] using hxbar_boundary

/-- Lemma 5.3. For `x̄` in the split strip `π₀ < π x̄ < π₀ + 1`, the point `x̄` belongs to
`P^(π, π₀)` if and only if there exists `x̃ ∈ Π₂` such that
`b - A x̃ ≤ (π x̄ - π₀)⁻¹ • (b - A x̄)`. -/
theorem mem_split_polyhedron_iff_exists_upper_point
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (s : Split I)
    (xbar : Fin n → ℝ)
    (hxbar_strip : xbar ∈ split_strip s s.π0) :
    xbar ∈ split_polyhedron A b s ↔
      ∃ xtilde : Fin n → ℝ,
        xtilde ∈ split_branch_upper (polyhedron_le_set A b) s s.π0 ∧
          b - A *ᵥ xtilde ≤ (split_dot s xbar - (s.π0 : ℝ))⁻¹ • (b - A *ᵥ xbar) := by
  let δ : ℝ := split_dot s xbar - (s.π0 : ℝ)
  have hδ_pos : 0 < δ := by
    simpa [δ] using (mem_split_strip_iff.mp hxbar_strip).1
  have hδ_lt_one : δ < 1 := by
    rcases mem_split_strip_iff.mp hxbar_strip with ⟨hleft, hright⟩
    dsimp [δ]
    linarith
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
  constructor
  · intro hxbar
    -- The reverse source direction now runs through the normalized boundary chord and the
    -- separate slack lemma, so the main theorem only assembles those two interfaces.
    rcases existsBoundaryBranchPair_of_memSplitPolyhedron_strip A b s xbar hxbar_strip hxbar with
      ⟨xlower, xtilde, hxlower, _, hxtilde, _, hxbar_repr⟩
    refine ⟨xtilde, hxtilde, ?_⟩
    exact upperSlackBound_of_boundaryBranchPair A b s xbar xlower xtilde δ
      hδ_pos hδ_lt_one hxlower (by simpa [δ] using hxbar_repr)
  · rintro ⟨xtilde, hxtilde, hxtilde_slack⟩
    let xlower : Fin n → ℝ := xbar + (δ / (1 - δ)) • (xbar - xtilde)
    have hxtilde_slack' : b - A *ᵥ xtilde ≤ δ⁻¹ • (b - A *ᵥ xbar) := by
      simpa [δ] using hxtilde_slack
    have hOneMinus_pos : 0 < 1 - δ := by
      linarith
    have hxbar_repr : xbar = (1 - δ) • xlower + δ • xtilde := by
      -- The source construction places `xbar` on the chord from the new lower point to `xtilde`.
      ext i
      dsimp [xlower]
      field_simp [hδ_ne, sub_ne_zero.mpr (ne_of_gt hOneMinus_pos)]
      ring
    have hxbar_line : xbar = AffineMap.lineMap xlower xtilde δ := by
      simpa [AffineMap.lineMap_apply_module] using hxbar_repr
    have hxtilde_split : (s.π0 : ℝ) + 1 ≤ split_dot s xtilde :=
      (mem_split_branch_upper_iff.mp hxtilde).2
    have hxbar_split_eq : split_dot s xbar = (s.π0 : ℝ) + δ := by
      dsimp [δ]
      ring
    have hxbar_split_line :
        split_dot s xbar = (1 - δ) * split_dot s xlower + δ * split_dot s xtilde := by
      simpa [hxbar_line] using splitDot_lineMap s xlower xtilde δ
    have hxlower_split : split_dot s xlower ≤ (s.π0 : ℝ) := by
      nlinarith [hxbar_split_line, hxtilde_split]
    have hslack_line :
        b - A *ᵥ xbar =
          (1 - δ) • (b - A *ᵥ xlower) + δ • (b - A *ᵥ xtilde) := by
      rw [hxbar_line]
      exact slackLineMap A b xlower xtilde δ
    have hxlower_poly : xlower ∈ polyhedron_le_set A b := by
      -- The slack inequality says the residual left after removing the `δ`-fraction of `xtilde`
      -- is nonnegative, so the constructed lower point is feasible.
      rw [mem_polyhedron_le_set_iff]
      intro i
      have hscaled : δ * (b - A *ᵥ xtilde) i ≤ (b - A *ᵥ xbar) i := by
        have hmul := mul_le_mul_of_nonneg_left (hxtilde_slack' i) hδ_pos.le
        simpa [Pi.smul_apply, hδ_ne, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hrow := congrFun hslack_line i
      rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply] at hrow
      have hnonneg_mul : 0 ≤ (1 - δ) * (b - A *ᵥ xlower) i := by
        have hdiff_nonneg : 0 ≤ (b - A *ᵥ xbar) i - δ * (b - A *ᵥ xtilde) i := by
          exact sub_nonneg.mpr hscaled
        calc
          0 ≤ (b - A *ᵥ xbar) i - δ * (b - A *ᵥ xtilde) i := hdiff_nonneg
          _ = (1 - δ) * (b - A *ᵥ xlower) i := by
                rw [hrow]
                ring
      have hlower_nonneg : 0 ≤ (b - A *ᵥ xlower) i := by
        by_contra hneg
        have hneg' : (b - A *ᵥ xlower) i < 0 := lt_of_not_ge hneg
        have hmul_neg : (1 - δ) * (b - A *ᵥ xlower) i < 0 := by
          exact mul_neg_of_pos_of_neg hOneMinus_pos hneg'
        linarith
      exact sub_nonneg.mp hlower_nonneg
    have hxlower_mem : xlower ∈ split_branch_lower (polyhedron_le_set A b) s s.π0 := by
      exact (mem_split_branch_lower_iff).2 ⟨hxlower_poly, hxlower_split⟩
    have hxbar_seg : xbar ∈ segment ℝ xlower xtilde := by
      rw [segment_eq_image_lineMap]
      exact ⟨δ, ⟨le_of_lt hδ_pos, le_of_lt hδ_lt_one⟩, hxbar_line.symm⟩
    rw [mem_split_polyhedron_iff, split_hull]
    exact
      (segment_subset_convexHull
        (s := split_branch_lower (polyhedron_le_set A b) s s.π0 ∪
          split_branch_upper (polyhedron_le_set A b) s s.π0)
        (x := xlower) (y := xtilde) (Or.inl hxlower_mem) (Or.inr hxtilde)) hxbar_seg

end Lemma53
