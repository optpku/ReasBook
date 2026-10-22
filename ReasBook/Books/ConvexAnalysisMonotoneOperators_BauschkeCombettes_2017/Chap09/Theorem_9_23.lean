/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Corollary_7_6
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap07.Definition_7_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Corollary_8_39
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_18

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped InnerProductSpace
open WithLp

universe u

namespace ERealFunction

noncomputable section

attribute [-instance] Prod.toNorm Prod.seminormedAddCommGroup Prod.normedAddCommGroup
attribute [-instance] Prod.normedSpace Prod.pseudoMetricSpaceMax
attribute [local instance] prod_pseudoMetricSpace_l2 prod_normedAddCommGroup_l2
  prod_normedSpace_l2 prod_completeSpace_l2 prod_innerProductSpace_l2

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 9.23: every effective-domain point gives its canonical real-height epigraph
point. -/
private lemma mem_real_epigraph_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) :
    (x, (f x : EReal).toReal) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
  -- Finiteness of `f x` places the graph point on the real-height epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hx))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 9.23: outside the effective domain, the value of `f` is `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∉ effectiveDomain f) :
    (f y : EReal) = ⊤ := by
  -- A finite value would put `y` back into the effective domain.
  by_contra htop
  exact hy (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 9.23: a real point strictly below the finite value of `f` cannot lie in
the real-height epigraph. -/
private theorem point_below_value_not_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} {ξ : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal) :
    (x, ξ) ∉ epigraph (fun y : H ↦ (f y : EReal)) := by
  -- Epigraph membership would force the forbidden inequality `(f x).toReal ≤ ξ`.
  intro hxξ
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hfx_le_ξ : (f x : EReal) ≤ (ξ : EReal) := (mem_epigraph_iff _ _ _).mp hxξ
  have hcast : (((f x : EReal).toReal : ℝ) : EReal) ≤ (ξ : EReal) := by
    simpa [EReal.coe_toReal hx_top hx_bot] using hfx_le_ξ
  exact not_le_of_gt hξ (by exact_mod_cast hcast)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Theorem 9.23: a real-height epigraph point has base point in the effective domain,
and its ordinate dominates the finite real value there. -/
private lemma mem_effectiveDomain_and_toReal_le_of_mem_real_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph (fun z : H ↦ (f z : EReal))) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- Epigraph membership bounds `f y` by a finite real height.
  have hfy_le : (f y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).mp hyη
  have hy : y ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfy_le (EReal.coe_lt_top η)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hη_top : (η : EReal) ≠ ⊤ := EReal.coe_ne_top η
  have htoReal : (f y : EReal).toReal ≤ ((η : EReal)).toReal := by
    simpa using EReal.toReal_le_toReal hfy_le hfy_bot hη_top
  simpa using ⟨hy, htoReal⟩

/-- Helper for Theorem 9.23: if `(p, π)` is the projection of `(x, ξ)` onto the real-height
epigraph of `f`, then `π` is exactly the finite value `f p` and lies strictly above `ξ`. -/
private theorem strict_lt_value_and_value_eq_height_of_eq_projectionPoint_epigraph_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ}
    (hx : x ∈ effectiveDomain f) (hξ : ξ < (f x : EReal).toReal) :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) →
      ξ < (f p : EReal).toReal ∧ (f p : EReal).toReal = π := by
  intro hproj
  rcases
      (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp
        hproj with
    ⟨hmax, hvar⟩
  have hp_mem :
      (p, π) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
    -- The projection point itself belongs to the epigraph.
    simpa [hproj] using
      projectionPoint_mem (epigraph (fun y : H ↦ (f y : EReal)))
        (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ)
  rcases mem_effectiveDomain_and_toReal_le_of_mem_real_epigraph (f := f) hp_mem with
    ⟨hp, hfp_le_pi⟩
  have hξ_le_pi : ξ ≤ π := by
    exact_mod_cast
      (le_trans (show (ξ : EReal) ≤ max (ξ : EReal) (f p : EReal) from le_max_left _ _) hmax :
        (ξ : EReal) ≤ (π : EReal))
  have hscalar : ((f p : EReal).toReal - π) * (ξ - π) ≤ 0 := by
    -- Evaluating the variational inequality at `y = p` removes the Hilbert term.
    simpa using hvar p hp
  have hξ_lt_fp : ξ < (f p : EReal).toReal := by
    by_contra hfp_le_ξ_false
    have hfp_le_ξ : (f p : EReal).toReal ≤ ξ := not_lt.mp hfp_le_ξ_false
    have hsq_le :
        (ξ - π) * (ξ - π) ≤ ((f p : EReal).toReal - π) * (ξ - π) := by
      exact
        mul_le_mul_of_nonpos_right (sub_le_sub_right hfp_le_ξ π)
          (sub_nonpos.mpr hξ_le_pi)
    have hπ_eq_ξ : π = ξ := by
      have hsq_nonneg : 0 ≤ (ξ - π) * (ξ - π) := by nlinarith
      nlinarith [hsq_nonneg, hsq_le, hscalar]
    have hvarx : ⟪x - p, x - p⟫_ℝ ≤ 0 := by
      have hvarx_raw :
          ⟪x - p, x - p⟫_ℝ + ((f x : EReal).toReal - π) * (ξ - π) ≤ 0 :=
        hvar x hx
      rw [hπ_eq_ξ, sub_self, mul_zero, add_zero] at hvarx_raw
      exact hvarx_raw
    have hinner_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ := by
      simpa using (real_inner_self_nonneg : 0 ≤ ⟪x - p, x - p⟫_ℝ)
    have hinner_eq_zero : ⟪x - p, x - p⟫_ℝ = 0 := by
      nlinarith [hinner_nonneg, hvarx]
    have hxp : x = p := by
      have hsub : x - p = 0 := by
        simpa using inner_self_eq_zero.mp hinner_eq_zero
      exact sub_eq_zero.mp hsub
    have hxξ_mem :
        (x, ξ) ∈ epigraph (fun y : H ↦ (f y : EReal)) := by
      simpa [hxp, hπ_eq_ξ] using hp_mem
    exact point_below_value_not_mem_real_epigraph (f := f) hx hξ hxξ_mem
  have hξ_lt_pi : ξ < π := lt_of_lt_of_le hξ_lt_fp hfp_le_pi
  have hfp_eq_pi : (f p : EReal).toReal = π := by
    by_contra hne
    have hfp_lt_pi : (f p : EReal).toReal < π := lt_of_le_of_ne hfp_le_pi hne
    have hprod_pos : 0 < ((f p : EReal).toReal - π) * (ξ - π) := by
      exact mul_pos_of_neg_of_neg (sub_neg.mpr hfp_lt_pi) (sub_neg.mpr hξ_lt_pi)
    linarith
  exact ⟨hξ_lt_fp, hfp_eq_pi⟩

/-- Helper for Theorem 9.23: the variational-inequality component of the epigraph projection
criterion. -/
private theorem variational_inequality_of_eq_projectionPoint_epigraph_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x p : H} {ξ π : ℝ} :
    (p, π) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (x, ξ) →
      ∀ y ∈ effectiveDomain f,
        ⟪y - p, x - p⟫_ℝ + ((f y : EReal).toReal - π) * (ξ - π) ≤ 0 := by
  intro hproj
  exact
    (eq_projectionPoint_epigraph_iff_max_le_and_variational_inequality_of_mem_gammaZero hf).mp
      hproj |>.2

omit [CompleteSpace H] in
/-- Helper for Theorem 9.23: a support point yields a nonzero supporting direction with the usual
translated inner-product inequality. -/
private theorem exists_nonzero_inner_sub_right_nonpos_of_mem_supportPoint
    {C : Set H} {x : H} (hx : x ∈ spts C) :
    ∃ u : H, u ≠ 0 ∧ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
  rcases Set.mem_supportPoints_iff.mp hx with ⟨hxC, u, hu_ne, hu_support⟩
  refine ⟨u, hu_ne, ?_⟩
  intro y hy
  have hy_le : (⟪y, u⟫_ℝ : EReal) ≤ innerSupremumOn C u := by
    rw [innerSupremumOn_eq_sSup_image]
    exact le_sSup ⟨y, hy, rfl⟩
  have hyx_le : (⟪y, u⟫_ℝ : EReal) ≤ (⟪x, u⟫_ℝ : EReal) := le_trans hy_le hu_support
  have hyx_le' : ⟪y, u⟫_ℝ ≤ ⟪x, u⟫_ℝ := by
    exact_mod_cast hyx_le
  simpa [inner_sub_left] using sub_nonpos.mpr hyx_le'

/-- Helper for Theorem 9.23: the projection onto a nonempty closed convex set stays fixed along
the ray starting at the projection point and pointing toward the original source. -/
private theorem projectionPoint_ray_fixed_of_nonempty_isClosed_convex_local
    {C : Set H} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    (x : H) {t : ℝ} (ht : 0 ≤ t) :
    projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
        (projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x +
          t •
            (x -
              projectionPoint C
                (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x)) =
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
  let p :=
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  have hp :
      p ∈ C ∧ ∀ y ∈ C, ⟪y - p, x - p⟫_ℝ ≤ 0 := by
    simpa [p] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mp rfl
  have hray :
      p =
        projectionPoint C
          (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
          (p + t • (x - p)) := by
    refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr ?_
    refine ⟨hp.1, ?_⟩
    intro y hy
    calc
      ⟪y - p, (p + t • (x - p)) - p⟫_ℝ = ⟪y - p, t • (x - p)⟫_ℝ := by
          abel_nf
      _ = t * ⟪y - p, x - p⟫_ℝ := by rw [inner_smul_right]
      _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht (hp.2 y hy)
  simpa [p] using hray.symm

/-- Helper for Theorem 9.23: an interior point of the effective domain yields nonempty interior in
the real-height epigraph. -/
private theorem interior_real_epigraph_nonempty_of_mem_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    (interior (epigraph (fun y : H ↦ (f y : EReal)))).Nonempty := by
  have hx_cont :
      x ∈ {y : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball y ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun z : H ↦ (f z : EReal).toReal) y} := by
    rw
      [continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
        (f := f) hf.2 (Or.inr (Or.inl hf.1))]
    exact hx
  rcases hx_cont with ⟨ρ, hρ, hball_dom, hcont⟩
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hδprop⟩ := hcont 1 zero_lt_one
  let r : ℝ := min ρ δ
  have hr : 0 < r := by
    dsimp [r]
    exact lt_min hρ hδ
  have hball_bound :
      ∀ y ∈ Metric.ball x r, (f y : EReal) ≤ (((f x : EReal).toReal + 1 : ℝ) : EReal) := by
    intro y hy
    have hyρ : y ∈ Metric.ball x ρ := by
      rw [Metric.mem_ball] at hy ⊢
      exact lt_of_lt_of_le hy (min_le_left _ _)
    have hyδ : dist y x < δ := by
      rw [Metric.mem_ball] at hy
      exact lt_of_lt_of_le hy (min_le_right _ _)
    have hy_dom : y ∈ effectiveDomain f := hball_dom hyρ
    have hdist : dist ((f y : EReal).toReal) ((f x : EReal).toReal) < 1 := hδprop hyδ
    have hreal : (f y : EReal).toReal ≤ (f x : EReal).toReal + 1 := by
      have habs : |(f y : EReal).toReal - (f x : EReal).toReal| < 1 := by
        simpa [Real.dist_eq] using hdist
      linarith [(abs_lt.mp habs).2]
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    rw [show (f y : EReal) = (((f y : EReal).toReal : ℝ) : EReal) by
      exact (EReal.coe_toReal hy_top hy_bot).symm]
    exact_mod_cast hreal
  let U : Set (H × ℝ) :=
    Metric.ball x r ×ˢ Set.Ioi (((f x : EReal).toReal + 1 : ℝ))
  refine ⟨(x, (f x : EReal).toReal + 2), ?_⟩
  rw [mem_interior_iff_mem_nhds]
  have hUx : (x, (f x : EReal).toReal + 2) ∈ U := by
    refine ⟨Metric.mem_ball_self hr, ?_⟩
    change (((f x : EReal).toReal + 1 : ℝ) < (f x : EReal).toReal + 2)
    have hone_lt_two : (1 : ℝ) < 2 := by norm_num
    linarith
  have hU_open : IsOpen U := by
    dsimp [U]
    exact IsOpen.prod Metric.isOpen_ball isOpen_Ioi
  refine Filter.mem_of_superset (hU_open.mem_nhds hUx) ?_
  rintro ⟨y, η⟩ hyη
  rcases hyη with ⟨hy_ball, hη_gt⟩
  rw [mem_epigraph_iff]
  exact le_of_lt <|
    lt_of_le_of_lt (hball_bound y hy_ball)
      (show (((f x : EReal).toReal + 1 : ℝ) : EReal) < (η : EReal) by
        exact_mod_cast hη_gt)

/-- Helper for Theorem 9.23: a support point on the real-height epigraph can be realized as the
projection of an exterior point whose base coordinate still lies in the interior effective domain.
-/
private theorem exists_projection_source_outside_epigraph_with_base_in_interior_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ∃ z : H, ∃ ζ : ℝ,
      z ∈ interior (effectiveDomain f) ∧
      ζ < (f z : EReal).toReal ∧
      (z, ζ) ∉ epigraph (fun y : H ↦ (f y : EReal)) ∧
      (x, (f x : EReal).toReal) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (z, ζ) := by
  let C : Set (H × ℝ) := epigraph (fun y : H ↦ (f y : EReal))
  let p : H × ℝ := (x, (f x : EReal).toReal)
  have hx_dom : x ∈ effectiveDomain f := interior_subset hx
  have hpC : p ∈ C := by
    -- The candidate support point is the canonical graph point above `x`.
    simpa [C, p] using mem_real_epigraph_of_mem_effectiveDomain (f := f) hx_dom
  have hp_frontier : p ∈ frontier C := by
    rw [mem_frontier_iff_notMem_interior hpC]
    intro hp_int
    let ι : ℝ → H × ℝ := fun η ↦ (x, η)
    have hι_open : IsOpen (ι ⁻¹' interior C) := isOpen_interior.preimage (by continuity)
    have hι_mem : (f x : EReal).toReal ∈ ι ⁻¹' interior C := by
      simpa [ι, p] using hp_int
    rcases Metric.mem_nhds_iff.mp (hι_open.mem_nhds hι_mem) with ⟨ε, hε, hball_subset⟩
    have hbelow_int : (x, (f x : EReal).toReal - ε / 2) ∈ interior C := by
      apply hball_subset
      rw [Metric.mem_ball, Real.dist_eq]
      have habs : |(f x : EReal).toReal - ε / 2 - (f x : EReal).toReal| = ε / 2 := by
        rw [show (f x : EReal).toReal - ε / 2 - (f x : EReal).toReal = -(ε / 2) by ring]
        rw [abs_of_neg]
        · ring
        · linarith
      rw [habs]
      linarith
    have hbelowC : (x, (f x : EReal).toReal - ε / 2) ∈ C := interior_subset hbelow_int
    have hbelow_not :
        (x, (f x : EReal).toReal - ε / 2) ∉ epigraph (fun y : H ↦ (f y : EReal)) :=
      point_below_value_not_mem_real_epigraph (f := f) hx_dom (by linarith)
    exact hbelow_not (by simpa [C] using hbelowC)
  have hC_int_nonempty : (interior C).Nonempty := by
    simpa [C] using
      interior_real_epigraph_nonempty_of_mem_interior_effectiveDomain (f := f) hf hx
  have hC_nonempty : C.Nonempty := ⟨p, hpC⟩
  have hC_closed : IsClosed C := by
    -- Lower semicontinuity is equivalent to closedness of the real-height epigraph.
    simpa [C] using
      (lowerSemicontinuous_iff_isClosed_epigraph (fun y : H ↦ (f y : EReal))).1 hf.1
  have hC_convex : Convex ℝ C := by
    -- Proposition 9.18 already packages convexity of the real-height epigraph.
    simpa [C] using convex_epigraph_of_mem_gammaZero hf
  have hp_support : p ∈ spts C := by
    -- Route correction: prove the Chapter 7 frontier-to-support implication directly through the
    -- normal-cone criterion, avoiding the unavailable packaged theorem symbol.
    have hN_ne : N[C] p ≠ ({0} : Set (H × ℝ)) := by
      intro hN
      exact hp_frontier.2 <|
        (mem_interior_iff_normalCone_eq_singleton_zero_of_convex
          hC_convex hC_int_nonempty hpC).2 hN
    have hzero : (0 : H × ℝ) ∈ N[C] p := by
      rw [normalCone_of_mem hpC]
      simp only [Set.mem_setOf_eq]
      rw [innerSupremumOn_eq_sSup_image]
      refine sSup_le ?_
      rintro _ ⟨y, hy, rfl⟩
      simp
    rw [supportPoints_eq_setOf_nontrivial_normalCone]
    intro hdiff
    apply hN_ne
    refine Subset.antisymm ?_ (singleton_subset_iff.mpr hzero)
    rw [diff_eq_empty] at hdiff
    exact hdiff
  rcases exists_nonzero_inner_sub_right_nonpos_of_mem_supportPoint (C := C) hp_support with
    ⟨u₀, hu₀_ne, hu₀_nonpos⟩
  let w₀ : H × ℝ := p + u₀
  have hw₀_out : w₀ ∉ C := by
    intro hw₀C
    have hnonpos : ⟪w₀ - p, u₀⟫_ℝ ≤ 0 := hu₀_nonpos w₀ hw₀C
    have hrewrite : ⟪w₀ - p, u₀⟫_ℝ = ⟪u₀, u₀⟫_ℝ := by
      dsimp [w₀]
      congr 1
      abel_nf
    rw [hrewrite] at hnonpos
    have hpositive : 0 < ⟪u₀, u₀⟫_ℝ := by
      simpa using (real_inner_self_pos.mpr hu₀_ne)
    linarith
  have hw₀_proj :
      projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)
        w₀ = p := by
    have hp_proj :
        p =
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) w₀ := by
      refine
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨hpC, ?_⟩
      intro q hq
      have hq_nonpos : ⟪q - p, u₀⟫_ℝ ≤ 0 := hu₀_nonpos q hq
      simpa [w₀] using hq_nonpos
    exact hp_proj.symm
  rcases w₀ with ⟨z₀, ζ₀⟩
  let γ : ℝ → H := fun t ↦ x + t • (z₀ - x)
  have hγ_open : IsOpen (γ ⁻¹' interior (effectiveDomain f)) := by
    exact isOpen_interior.preimage (by continuity)
  have hγ_zero : (0 : ℝ) ∈ γ ⁻¹' interior (effectiveDomain f) := by
    simpa [γ] using hx
  rcases Metric.mem_nhds_iff.mp (hγ_open.mem_nhds hγ_zero) with ⟨ε, hε, hεball⟩
  let t : ℝ := ε / 2
  have ht_pos : 0 < t := by
    dsimp [t]
    positivity
  have ht_nonneg : 0 ≤ t := ht_pos.le
  have hz_int : γ t ∈ interior (effectiveDomain f) := by
    apply hεball
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg]
    · dsimp [t]
      linarith
    · dsimp [t]
      linarith
  let w : H × ℝ := p + t • ((z₀, ζ₀) - p)
  have hw_proj :
      projectionPoint C (isChebyshev_epigraph_of_mem_gammaZero hf) w = p := by
    -- The local ray lemma keeps the projection fixed while we move the exterior point back above
    -- an interior base point.
    simpa [C, p, w, hw₀_proj] using
      projectionPoint_ray_fixed_of_nonempty_isClosed_convex_local hC_nonempty hC_closed hC_convex
        (z₀, ζ₀) ht_nonneg
  have hw_out : w ∉ C := by
    intro hwC
    have hw_self :
        w = projectionPoint C (isChebyshev_epigraph_of_mem_gammaZero hf) w := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨hwC, ?_⟩
      intro q hq
      simp
    have hwp : w = p := hw_self.trans hw_proj
    have hzero : t • ((z₀, ζ₀) - p) = 0 := by
      simpa [w] using congrArg (fun q : H × ℝ ↦ q - p) hwp
    have hdiff : ((z₀, ζ₀) - p : H × ℝ) = 0 := by
      rcases smul_eq_zero.mp hzero with ht_zero | hdiff
      · exact (ht_pos.ne' ht_zero).elim
      · exact hdiff
    have hw₀_eq : (z₀, ζ₀) = p := sub_eq_zero.mp hdiff
    have hw₀_mem : (z₀, ζ₀) ∈ C := by
      simpa [hw₀_eq] using hpC
    exact hw₀_out hw₀_mem
  have hz_dom : w.1 ∈ effectiveDomain f := interior_subset (by simpa [w, p, γ] using hz_int)
  have hζ_lt : w.2 < (f w.1 : EReal).toReal := by
    by_contra hle
    have hw_mem : w ∈ C := by
      have hw_top : (f w.1 : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom)
      have hw_bot : (f w.1 : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f w.1 : EReal) from (f w.1).2)
      have hcast : (f w.1 : EReal) = (((f w.1 : EReal).toReal : ℝ) : EReal) := by
        exact (EReal.coe_toReal hw_top hw_bot).symm
      change (f w.1 : EReal) ≤ (w.2 : EReal)
      rw [hcast]
      exact_mod_cast not_lt.mp hle
    exact hw_out hw_mem
  refine ⟨w.1, w.2, ?_, hζ_lt, ?_, ?_⟩
  · -- The ray adjustment keeps the base point inside the interior effective domain.
    simpa [w, p, γ] using hz_int
  · -- The moved point is still outside the epigraph.
    simpa [C] using hw_out
  · -- Repackage the moved point in coordinates expected by Proposition 9.19.
    simpa [C] using hw_proj.symm

/-- Helper for Theorem 9.23: a projection contact with an exterior real-height epigraph point
produces the desired supporting continuous affine minorant. -/
private theorem supporting_affine_minorant_of_projection_contact
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x z : H} {ζ : ℝ}
    (hz : z ∈ effectiveDomain f) (hζ : ζ < (f z : EReal).toReal)
    (hproj :
      (x, (f x : EReal).toReal) =
        projectionPoint (epigraph (fun y : H ↦ (f y : EReal)))
          (isChebyshev_epigraph_of_mem_gammaZero hf) (z, ζ)) :
    ∃ g : H →ᴬ[ℝ] ℝ,
      g x = (f x : EReal).toReal ∧ ∀ y : H, (g y : EReal) ≤ (f y : EReal) := by
  let p : ℝ := (f x : EReal).toReal
  have hstrict :
      ζ < (f x : EReal).toReal ∧ (f x : EReal).toReal = p := by
    simpa [p] using
      strict_lt_value_and_value_eq_height_of_eq_projectionPoint_epigraph_of_mem_gammaZero
        (f := f) hf hz hζ hproj
  have hvar :
      ∀ y ∈ effectiveDomain f,
        ⟪y - x, z - x⟫_ℝ + ((f y : EReal).toReal - p) * (ζ - p) ≤ 0 := by
    intro y hy
    simpa [p] using
      variational_inequality_of_eq_projectionPoint_epigraph_of_mem_gammaZero
        (f := f) hf hproj y hy
  have hgap_pos : 0 < p - ζ := by
    -- Proposition 9.19 forces the projection height to lie strictly above `ζ`.
    linarith [hstrict.1]
  let u : H := (p - ζ)⁻¹ • (z - x)
  let gAffine : H →ᵃ[ℝ] ℝ :=
    AffineMap.mk'
      (fun y : H ↦ ⟪y, u⟫_ℝ + (p - ⟪x, u⟫_ℝ))
      ((InnerProductSpace.toDual ℝ H u).toLinearMap)
      (0 : H)
      (fun y ↦ by
        simp [vsub_eq_sub, vadd_eq_add, sub_eq_add_neg, InnerProductSpace.toDual_apply_apply,
          real_inner_comm])
  let g : H →ᴬ[ℝ] ℝ := ContinuousAffineMap.mk gAffine (by continuity)
  refine ⟨g, ?_, ?_⟩
  · -- The affine map was normalized so that it meets `f` at `x`.
    change ⟪x, u⟫_ℝ + (p - ⟪x, u⟫_ℝ) = p
    ring
  · intro y
    by_cases hy : y ∈ effectiveDomain f
    · have hraw :
          ⟪y - x, z - x⟫_ℝ + ((f y : EReal).toReal - p) * (ζ - p) ≤ 0 :=
        hvar y hy
      have hinner_le :
          ⟪y - x, z - x⟫_ℝ ≤ ((f y : EReal).toReal - p) * (p - ζ) := by
        -- Rewrite the Proposition 9.19 inequality so the positive gap `p - ζ` appears explicitly.
        nlinarith
      have hscaled : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - p := by
        -- Divide by the positive gap to isolate the support slope.
        have hdiv : ⟪y - x, z - x⟫_ℝ / (p - ζ) ≤ (f y : EReal).toReal - p := by
          refine (div_le_iff₀ hgap_pos).2 ?_
          simpa [mul_comm, mul_left_comm, mul_assoc] using hinner_le
        simpa [u, div_eq_mul_inv, real_inner_smul_right, mul_comm, mul_left_comm, mul_assoc] using
          hdiv
      have hreal : ⟪y - x, u⟫_ℝ + p ≤ (f y : EReal).toReal := by
        linarith
      have hg_eq : g y = ⟪y - x, u⟫_ℝ + p := by
        change ⟪y, u⟫_ℝ + (p - ⟪x, u⟫_ℝ) = ⟪y - x, u⟫_ℝ + p
        calc
          ⟪y, u⟫_ℝ + (p - ⟪x, u⟫_ℝ) = (⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ) + p := by ring
          _ = ⟪y - x, u⟫_ℝ + p := by rw [inner_sub_left]
      have hfy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
      have hfy_bot : (f y : EReal) ≠ ⊥ := by
        exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
      have hcast :
          ((g y : ℝ) : EReal) ≤ (((f y : EReal).toReal : ℝ) : EReal) := by
        exact_mod_cast (show g y ≤ (f y : EReal).toReal by rw [hg_eq]; exact hreal)
      simpa [EReal.coe_toReal hfy_top hfy_bot] using hcast
    · -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
      simp [value_eq_top_of_not_mem_effectiveDomain hy]

-- Proof sketch: view `(x, (f x).toReal)` as a boundary point of the real-height epigraph of `f`.
-- The interior-domain hypothesis and the Chapter 8 continuity results give enough interior
-- epigraph geometry to apply the supporting-point projection argument from Chapter 7, and
-- Proposition 9.19 then turns the projection inequality into a supporting continuous affine
-- minorant through that point.
/-- Theorem 9.23: if `f ∈ Γ₀(H)` and `x` lies in the interior of its effective domain, then `f`
admits a supporting continuous affine minorant through `(x, f x)`; equivalently, in coordinates,
one may write this affine minorant as `y ↦ ⟪y - x, u⟫_ℝ + (f x).toReal` for some `u : H`. -/
theorem exists_supporting_affine_minorant_of_mem_interior_effectiveDomain_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {x : H}
    (hx : x ∈ interior (effectiveDomain f)) :
    ∃ g : H →ᴬ[ℝ] ℝ,
      g x = (f x : EReal).toReal ∧ ∀ y : H, (g y : EReal) ≤ (f y : EReal) := by
  rcases
      exists_projection_source_outside_epigraph_with_base_in_interior_effectiveDomain
        (f := f) hf hx with
    ⟨z, ζ, hz_int, hζ, _, hproj⟩
  -- Route correction: keep the source proof's projection geometry, then normalize Proposition 9.19
  -- into the affine support map.
  exact
    supporting_affine_minorant_of_projection_contact
      (f := f) hf (interior_subset hz_int) hζ hproj

end

end ERealFunction
