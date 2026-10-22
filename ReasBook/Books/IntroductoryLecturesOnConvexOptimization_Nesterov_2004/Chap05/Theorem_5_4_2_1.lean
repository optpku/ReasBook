/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Corollary_3_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Theorem 5.4.2.1 lies in the chapter's based-polar-set / finite-dimensional convex-geometry
domain.

Sampled owner-style declarations:
- project `polarSet`
- project `mem_polarSetAt_iff`
- mathlib `NormedSpace.isClosed_polar`
- mathlib `NormedSpace.isBounded_polar_of_mem_nhds_zero`

Best owner abstraction:
- source-facing: the compact-convex conclusion for the based polar body `polarSetAt Q xBar`
- core/canonical: the chapter owner `polarSet`
- bridge/view: the based displacement-set owner `polarSetAt`

Primitive data:
- a set `Q : Set E`
- a base point `xBar : E`
- for compactness and boundedness: `xBar ∈ interior Q`
- for the separate interior-nonemptiness companion: `Convex ℝ Q` together with the chapter
  no-affine-line hypothesis on `Q`

Derived API:
- unconditional closedness and convexity of `polarSetAt Q xBar`
- compactness and boundedness from the interior-point hypothesis
- nonempty interior under the extra source-facing convex/no-affine-line assumptions
- the trivial base-point-free fact `0 ∈ polarSetAt Q xBar`

This theorem file should not be tied to the display model `EuclideanSpace ℝ (Fin n)`: the owner
`polarSetAt` already lives on real inner-product spaces, and the proof sketch only uses finite
dimensionality. The correct public surface is therefore a finite-dimensional real inner-product
space. The owner-level geometry also separates cleanly into two layers: `polarSetAt Q xBar` is
always an intersection of closed convex half-spaces, so its closedness and convexity are
unconditional, while compactness and boundedness use only the interior ball around `xBar`. The
chapter’s convexity and no-affine-line assumptions remain only on the separate interior-nonempty
companion theorem, where they belong.
-/

section RealInnerProduct

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {Q : Set E} {xBar : E}

/-- Helper for Theorem 5.4.2.1: the based polar is exactly the intersection of its defining
inner-product half-spaces. -/
lemma polarSetAt_eq_iInter_inner_halfspaces :
    polarSetAt Q xBar = ⋂ x ∈ Q, {s : E | inner ℝ s (x - xBar) ≤ 1} := by
  ext s
  rw [mem_polarSetAt_iff]
  simp

-- Proof sketch: each defining inequality `inner ℝ s (x - xBar) ≤ 1` cuts out a convex
-- half-space, and arbitrary intersections of convex sets are convex.
/-- The based polar set is convex. -/
theorem polarSetAt_convex :
    Convex ℝ (polarSetAt Q xBar) := by
  intro s₁ hs₁ s₂ hs₂ a b ha hb hab
  rw [mem_polarSetAt_iff] at hs₁ hs₂ ⊢
  intro x hx
  -- The defining inequalities are preserved by convex combinations in the polar variable.
  calc
    inner ℝ (a • s₁ + b • s₂) (x - xBar)
        = a * inner ℝ s₁ (x - xBar) + b * inner ℝ s₂ (x - xBar) := by
            simp [inner_add_left, inner_smul_left]
    _ ≤ a * 1 + b * 1 := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left (hs₁ x hx) ha)
            (mul_le_mul_of_nonneg_left (hs₂ x hx) hb)
    _ = 1 := by nlinarith

-- Proof sketch: each defining inequality `inner ℝ s (x - xBar) ≤ 1` cuts out a closed
-- half-space, and arbitrary intersections of closed sets are closed.
/-- The based polar set is closed. -/
theorem polarSetAt_isClosed :
    IsClosed (polarSetAt Q xBar) := by
  -- Rewrite the based polar as the intersection of its defining half-spaces.
  rw [polarSetAt_eq_iInter_inner_halfspaces (Q := Q) (xBar := xBar)]
  refine isClosed_iInter fun x ↦ isClosed_iInter fun hx ↦ ?_
  -- Each defining inequality is closed because the inner-product slice is continuous.
  exact isClosed_le (continuous_id.inner continuous_const) continuous_const

/-- Helper for Theorem 5.4.2.1: an interior ball around `xBar` bounds the whole based polar by a
centered closed ball. -/
lemma polarSetAt_subset_closedBall_of_ball_subset
    {r : ℝ} (hr : 0 < r) (hball : Metric.ball xBar r ⊆ Q) :
    polarSetAt Q xBar ⊆ Metric.closedBall (0 : E) (2 / r) := by
  intro s hs
  by_cases hs0 : s = 0
  · simpa [hs0, Metric.mem_closedBall, hr.le] using (show (0 : ℝ) ≤ 2 / r by positivity)
  have hs_norm_pos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  let y : E := xBar + ((r / 2) / ‖s‖) • s
  have hy_sub : y - xBar = ((r / 2) / ‖s‖) • s := by
    simp [y]
  have hy_norm : ‖y - xBar‖ = r / 2 := by
    calc
      ‖y - xBar‖ = ‖((r / 2) / ‖s‖) • s‖ := by rw [hy_sub]
      _ = |(r / 2) / ‖s‖| * ‖s‖ := norm_smul _ _
      _ = ((r / 2) / ‖s‖) * ‖s‖ := by
            rw [abs_of_nonneg]
            positivity
      _ = r / 2 := by
            field_simp [hs_norm_pos.ne']
  have hy_ball : y ∈ Metric.ball xBar r := by
    rw [Metric.mem_ball, dist_eq_norm, hy_norm]
    linarith
  have hyQ : y ∈ Q := hball hy_ball
  have hy_polar : inner ℝ s (y - xBar) ≤ 1 := (mem_polarSetAt_iff.mp hs) y hyQ
  have hbound : ((r / 2) / ‖s‖) * ‖s‖ ^ (2 : ℕ) ≤ 1 := by
    calc
      ((r / 2) / ‖s‖) * ‖s‖ ^ (2 : ℕ) = inner ℝ s (y - xBar) := by
        rw [hy_sub, inner_smul_right, real_inner_self_eq_norm_sq]
      _ ≤ 1 := hy_polar
  have hscaled : (r / 2) * ‖s‖ ≤ 1 := by
    calc
      (r / 2) * ‖s‖ = ((r / 2) / ‖s‖) * ‖s‖ ^ (2 : ℕ) := by
        field_simp [hs_norm_pos.ne']
      _ ≤ 1 := hbound
  have hs_le : ‖s‖ ≤ 2 / r := by
    have hr2_pos : 0 < r / 2 := by linarith
    have hs_le' : ‖s‖ ≤ 1 / (r / 2) := by
      rw [le_div_iff₀ hr2_pos]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled
    have hrewrite : 1 / (r / 2) = 2 / r := by
      field_simp [hr.ne']
    simpa [hrewrite] using hs_le'
  simpa [Metric.mem_closedBall, dist_eq_norm] using hs_le

-- Proof sketch: if `xBar ∈ interior Q`, then some ball around `xBar` lies in `Q`; evaluating the
-- defining inequalities on that ball gives a uniform norm bound on every `s ∈ polarSetAt Q xBar`.
/-- The polar set of an interior point is bounded. -/
theorem polarSetAt_isBounded
    (hxBar : xBar ∈ interior Q) :
    Bornology.IsBounded (polarSetAt Q xBar) := by
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hxBar) with ⟨r, hr, hball⟩
  -- The interior ball gives a uniform norm bound on the entire based polar.
  refine Bornology.IsBounded.subset
    (Metric.isBounded_closedBall : Bornology.IsBounded (Metric.closedBall (0 : E) (2 / r))) ?_
  exact polarSetAt_subset_closedBall_of_ball_subset (Q := Q) (xBar := xBar) hr hball

-- Proof sketch: for every `x ∈ Q`, the defining inequality for `polarSetAt Q xBar` at `s = 0`
-- reduces to `0 ≤ 1`.
/-- The origin belongs to every polar set. -/
theorem zero_mem_polarSetAt {Q : Set E} {xBar : E} :
    (0 : E) ∈ polarSetAt Q xBar := by
  rw [polarSetAt, mem_polarSet_iff]
  intro x hx
  simp

end RealInnerProduct

section FiniteDimensionalReal

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {Q : Set E} {xBar : E}

-- Proof sketch: `polarSetAt Q xBar` is convex unconditionally. If `xBar ∈ interior Q`, the
-- interior ball around `xBar` gives boundedness, and in finite-dimensional real inner-product
-- space boundedness plus closedness gives compactness by Heine-Borel.
/-- Theorem 5.4.2.1, at the intrinsic owner level: if `xBar` is an interior point of `Q`, then
the based polar set `P(xBar) = polarSetAt Q xBar` is compact and convex. The textbook convexity
and no-affine-line assumptions are redundant for this conclusion. -/
theorem polarSetAt_isCompact_convex
    (hxBar : xBar ∈ interior Q) :
    IsCompact (polarSetAt Q xBar) ∧ Convex ℝ (polarSetAt Q xBar) := by
  -- Compactness comes from the finite-dimensional Heine-Borel theorem, while convexity is
  -- unconditional from the defining half-spaces.
  exact ⟨
    Metric.isCompact_of_isClosed_isBounded
      (polarSetAt_isClosed (Q := Q) (xBar := xBar))
      (polarSetAt_isBounded (Q := Q) (xBar := xBar) hxBar),
    polarSetAt_convex (Q := Q) (xBar := xBar)
  ⟩

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 5.4.2.1: if a whole line through `xBar` lies in `closure Q`, then convexity
and the interior-point hypothesis upgrade that line to `interior Q`. -/
lemma closure_line_through_interior_point_subset_interior
    (hQ_convex : Convex ℝ Q) (hxBar : xBar ∈ interior Q) {h : E}
    (hline : ∀ τ : ℝ, xBar + τ • h ∈ closure Q) :
    ∀ τ : ℝ, xBar + τ • h ∈ interior Q := by
  intro τ
  -- Express the target point as the midpoint of an interior point and a closure point on the
  -- same affine line.
  have hmid :
      (1 / 2 : ℝ) • (xBar + (2 * τ) • h) + (1 / 2 : ℝ) • xBar ∈ interior Q := by
    refine hQ_convex.combo_closure_interior_mem_interior (hline (2 * τ)) hxBar ?_ ?_ ?_
    · norm_num
    · norm_num
    · norm_num
  have hEq :
      (1 / 2 : ℝ) • (xBar + (2 * τ) • h) + (1 / 2 : ℝ) • xBar = xBar + τ • h := by
    have hx :
        (1 / 2 : ℝ) • xBar + (1 / 2 : ℝ) • xBar = xBar := by
      rw [← add_smul, show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_smul]
    have hh :
        ((1 / 2 : ℝ) * (2 * τ)) • h = τ • h := by
      congr 1
      ring
    calc
      (1 / 2 : ℝ) • (xBar + (2 * τ) • h) + (1 / 2 : ℝ) • xBar
          = (1 / 2 : ℝ) • xBar + (((1 / 2 : ℝ) * (2 * τ)) • h + (1 / 2 : ℝ) • xBar) := by
              simp [smul_add, smul_smul, add_assoc]
      _ = ((1 / 2 : ℝ) • xBar + (1 / 2 : ℝ) • xBar) + (((1 / 2 : ℝ) * (2 * τ)) • h) := by
            simp [add_left_comm, add_comm]
      _ = xBar + (((1 / 2 : ℝ) * (2 * τ)) • h) := by rw [hx]
      _ = xBar + τ • h := by rw [hh]
  exact hEq ▸ hmid

/-- Helper for Theorem 5.4.2.1: if the based polar had empty interior, then some nonzero direction
would generate a whole affine line through `xBar` inside `closure Q`. -/
lemma line_in_closure_of_empty_interior_polarSetAt [Nontrivial E]
    (hQ_convex : Convex ℝ Q) (hxBar : xBar ∈ interior Q)
    (hEmpty : interior (polarSetAt Q xBar) = ∅) :
    ∃ h : E, h ≠ 0 ∧ ∀ τ : ℝ, xBar + τ • h ∈ closure Q := by
  classical
  let P : Set E := polarSetAt Q xBar
  have hP_convex : Convex ℝ P := polarSetAt_convex (Q := Q) (xBar := xBar)
  have hP_zero : (0 : E) ∈ P := zero_mem_polarSetAt (Q := Q) (xBar := xBar)
  have hP_affine_ne_top : affineSpan ℝ P ≠ ⊤ := by
    intro htop
    have hnonempty : (interior P).Nonempty :=
      (hP_convex.interior_nonempty_iff_affineSpan_eq_top).2 htop
    simp [P, hEmpty] at hnonempty
  have hP_span_ne_top : Submodule.span ℝ P ≠ ⊤ := by
    intro htop
    apply hP_affine_ne_top
    have hinsert : (affineSpan ℝ (insert 0 P) : Set E) = Submodule.span ℝ P :=
      affineSpan_insert_zero (k := ℝ) P
    have hset : (affineSpan ℝ P : Set E) = Submodule.span ℝ P := by
      exact
        (congrArg (fun s : Set E => (affineSpan ℝ s : Set E))
          (Set.insert_eq_of_mem hP_zero)).symm.trans hinsert
    have htop_set : (affineSpan ℝ P : Set E) = Set.univ := by
      rw [hset, htop]
      rfl
    ext x
    exact ⟨fun _ ↦ by simp, fun _ ↦ by
      change x ∈ (affineSpan ℝ P : Set E)
      rw [htop_set]
      simp⟩
  have hperp_ne_bot : (Submodule.span ℝ P)ᗮ ≠ ⊥ := by
    intro hbot
    exact hP_span_ne_top ((Submodule.orthogonal_eq_bot_iff).mp hbot)
  obtain ⟨h, hh_mem, hh_ne⟩ := (Submodule.ne_bot_iff _).mp hperp_ne_bot
  refine ⟨h, hh_ne, ?_⟩
  intro τ
  by_contra hτ
  let y : E := xBar + τ • h
  have hy_not : y ∉ closure Q := by
    simpa [y] using hτ
  obtain ⟨g, γ, hsep, hγlt⟩ :=
    exists_strictlySeparating_hyperplane_of_nonmem_closed_convex
      (closure Q) isClosed_closure hQ_convex.closure hy_not
  let δ : ℝ := γ - inner ℝ g xBar
  let κ : ℝ := if hδ : δ = 0 then 1 else δ⁻¹
  let s : E := κ • g
  have hxBar_closure : xBar ∈ closure Q := subset_closure (interior_subset hxBar)
  have hδ_nonneg : 0 ≤ δ := by
    dsimp [δ]
    exact sub_nonneg.mpr (hsep.le_offset hxBar_closure)
  have hs_mem : s ∈ P := by
    rw [mem_polarSetAt_iff]
    intro x hx
    have hx_le : inner ℝ g x ≤ γ := hsep.le_offset (subset_closure hx)
    have hshift : inner ℝ g (x - xBar) ≤ δ := by
      dsimp [δ]
      calc
        inner ℝ g (x - xBar) = inner ℝ g x - inner ℝ g xBar := by
          rw [inner_sub_right]
        _ ≤ γ - inner ℝ g xBar := sub_le_sub_right hx_le _
    by_cases hδ : δ = 0
    · have hshift_nonpos : inner ℝ g (x - xBar) ≤ 0 := by simpa [hδ] using hshift
      calc
        inner ℝ s (x - xBar) = inner ℝ g (x - xBar) := by
          simp [s, κ, hδ]
        _ ≤ 0 := hshift_nonpos
        _ ≤ 1 := by norm_num
    · calc
        inner ℝ s (x - xBar) = δ⁻¹ * inner ℝ g (x - xBar) := by
          simp [s, κ, hδ, inner_smul_left]
        _ ≤ δ⁻¹ * δ := by
          exact mul_le_mul_of_nonneg_left hshift (inv_nonneg.mpr hδ_nonneg)
        _ = 1 := by rw [inv_mul_cancel₀ hδ]
  have hs_span : s ∈ Submodule.span ℝ P := Submodule.subset_span hs_mem
  have hs_orth : inner ℝ s h = 0 :=
    Submodule.inner_right_of_mem_orthogonal (K := Submodule.span ℝ P) hs_span hh_mem
  have hy_strict : δ < inner ℝ g (y - xBar) := by
    dsimp [δ]
    calc
      γ - inner ℝ g xBar < inner ℝ g y - inner ℝ g xBar := sub_lt_sub_right hγlt _
      _ = inner ℝ g (y - xBar) := by rw [inner_sub_right]
  have hs_strict : 0 < inner ℝ s (y - xBar) := by
    by_cases hδ : δ = 0
    · have hy_pos : 0 < inner ℝ g (y - xBar) := by simpa [hδ] using hy_strict
      calc
        0 < inner ℝ g (y - xBar) := hy_pos
        _ = inner ℝ s (y - xBar) := by simp [s, κ, hδ]
    · have hδ_pos : 0 < δ := lt_of_le_of_ne hδ_nonneg (Ne.symm hδ)
      have hy_pos : 0 < inner ℝ g (y - xBar) := lt_of_le_of_lt hδ_nonneg hy_strict
      calc
        0 < δ⁻¹ * inner ℝ g (y - xBar) := by
          exact mul_pos (inv_pos.mpr hδ_pos) hy_pos
        _ = inner ℝ s (y - xBar) := by simp [s, κ, hδ, inner_smul_left]
  have hs_nonorth : inner ℝ s h ≠ 0 := by
    intro hs_zero
    have : inner ℝ s (y - xBar) = 0 := by
      calc
        inner ℝ s (y - xBar) = inner ℝ s (τ • h) := by simp [y]
        _ = τ * inner ℝ s h := by rw [inner_smul_right]
        _ = 0 := by simp [hs_zero]
    exact (lt_irrefl 0) (this ▸ hs_strict)
  exact hs_nonorth hs_orth

-- Proof sketch: use the interior ball around `xBar` together with the absence of affine lines in
-- `Q` to show that a small Euclidean ball around the origin satisfies the defining inequalities of
-- `polarSetAt Q xBar`.
/-- The polar set of an interior point has nonempty interior. -/
theorem polarSetAt_interior_nonempty
    (hQ_convex : Convex ℝ Q)
    (hQ_noAffineLine : ∀ ⦃x h : E⦄, h ≠ 0 → ¬ ∀ τ : ℝ, x + τ • h ∈ Q)
    (hxBar : xBar ∈ interior Q) :
    (interior (polarSetAt Q xBar)).Nonempty := by
  by_cases hE : Subsingleton E
  · letI : Subsingleton E := hE
    have hpolar_univ : polarSetAt Q xBar = Set.univ := by
      ext s
      simpa [Subsingleton.elim s 0] using (zero_mem_polarSetAt (Q := Q) (xBar := xBar))
    simp [hpolar_univ]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    by_contra hEmpty
    have hEmpty_eq : interior (polarSetAt Q xBar) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp hEmpty
    -- Route correction: empty interior of the polar would force a full affine line in `Q`,
    -- contradicting the chapter's no-affine-line hypothesis.
    obtain ⟨h, hh_ne, hline_closure⟩ :=
      line_in_closure_of_empty_interior_polarSetAt
        (Q := Q) (xBar := xBar) hQ_convex hxBar hEmpty_eq
    have hline_interior :
        ∀ τ : ℝ, xBar + τ • h ∈ interior Q :=
      closure_line_through_interior_point_subset_interior
        (Q := Q) (xBar := xBar) hQ_convex hxBar hline_closure
    have hline_Q : ∀ τ : ℝ, xBar + τ • h ∈ Q := fun τ ↦ interior_subset (hline_interior τ)
    exact (hQ_noAffineLine hh_ne) hline_Q

end FiniteDimensionalReal

end
