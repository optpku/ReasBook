/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Filter
open scoped Topology
open scoped WithTopConvexAnalysis

private theorem convexOn_right_secant_bound
    {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    {x z t : ℝ} (hx : x ∈ s) (hz : z ∈ s) (hxt : x ≤ t) (htz : t < z) :
    g t ≤ g x + ((t - x) / (z - x)) * (g z - g x) := by
  rcases eq_or_lt_of_le hxt with rfl | hxt
  · simp
  have hxz : x < z := lt_trans hxt htz
  have hzx0 : 0 < z - x := sub_pos.mpr hxz
  have hsec :
      (z - x) * g t ≤ (z - t) * g x + (t - x) * g z :=
    hg.secant_mono_aux1 hx hz hxt htz
  refine le_of_mul_le_mul_left ?_ hzx0
  calc
    (z - x) * g t ≤ (z - t) * g x + (t - x) * g z := hsec
    _ = (z - x) * (g x + ((t - x) / (z - x)) * (g z - g x)) := by
      field_simp [hzx0.ne']
      ring

private theorem convexOn_left_secant_bound
    {s : Set ℝ} {g : ℝ → ℝ} (hg : ConvexOn ℝ s g)
    {z x t : ℝ} (hz : z ∈ s) (hx : x ∈ s) (hzt : z < t) (htx : t ≤ x) :
    g t ≤ g x + ((x - t) / (x - z)) * (g z - g x) := by
  rcases eq_or_lt_of_le htx with rfl | htx
  · simp
  have hzx : z < x := lt_trans hzt htx
  have hxz0 : 0 < x - z := sub_pos.mpr hzx
  have hsec :
      (x - z) * g t ≤ (x - t) * g z + (t - z) * g x :=
    hg.secant_mono_aux1 hz hx hzt htx
  refine le_of_mul_le_mul_left ?_ hxz0
  calc
    (x - z) * g t ≤ (x - t) * g z + (t - z) * g x := hsec
    _ = (x - z) * (g x + ((x - t) / (x - z)) * (g z - g x)) := by
      field_simp [hxz0.ne']
      ring

private theorem coeff_mul_abs_lt_half
    {num den diff ε : ℝ}
    (hnum_nonneg : 0 ≤ num) (hden_pos : 0 < den)
    (hnum_lt : num < den * ε / (2 * (|diff| + 1))) (hε : 0 < ε) :
    (num / den) * |diff| < ε / 2 := by
  let A : ℝ := |diff| + 1
  have hApos : 0 < A := by
    dsimp [A]
    positivity
  have hcoeff_nonneg : 0 ≤ num / den := div_nonneg hnum_nonneg hden_pos.le
  have hcoeff_lt : num / den < ε / (2 * A) := by
    have h' : num < (ε / (2 * A)) * den := by
      simpa [A, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hnum_lt
    exact (div_lt_iff₀ hden_pos).2 h'
  have hle : (num / den) * |diff| ≤ (num / den) * A := by
    have habs_le : |diff| ≤ A := by
      dsimp [A]
      nlinarith
    exact mul_le_mul_of_nonneg_left habs_le hcoeff_nonneg
  have hlt : (num / den) * A < ε / 2 := by
    have hmul := mul_lt_mul_of_pos_right hcoeff_lt hApos
    have hEq : (ε / (2 * A)) * A = ε / 2 := by
      field_simp [A, hApos.ne']
    simpa [hEq] using hmul
  exact lt_of_le_of_lt hle hlt

/-
Lemma 3.4 lies in the chapter's univariate closed-convex continuity domain.

Primary domain:
- relative continuity of univariate closed convex `WithTop ℝ`-valued functions on their effective
  domain.

Sampled owner-style declarations:
- `dom f`, `withTopRealPart` from `Definition_3_3`
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- mathlib `continuousWithinAt_iff_continuousAt_restrict`
- mathlib `continuous_iff_seqContinuous`
- mathlib `ConvexOn.continuousOn`

Best owner abstraction:
- `ClosedConvexFunction`, with `dom f` and `withTopRealPart f` as the canonical derived
  domain/view data.

Primitive data:
- the effective domain `dom f`
- the finite real representative `withTopRealPart f`
- the owner hypothesis `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Source/core/bridge triage:
- source-facing: continuity of the finite-value representative on the effective domain
- core/canonical: `ClosedConvexFunction`
- bridge/view: restriction to the effective-domain subtype used to express relative continuity

The source-facing continuity theorem is the main public entry in this file. The sequential limit
reformulation carried no downstream use in the chapter, so the file keeps only the owner theorem
instead of exporting a second bridge statement.
-/

/-- Lemma 3.4: any univariate closed convex function is continuous on its effective domain. -/
-- Proof sketch: restrict `withTopRealPart f` to the effective-domain subtype. The one-dimensional
-- closed-convex argument gives sequential continuity there, and metric-space sequential continuity
-- upgrades to continuity on the subtype. Translating back yields continuity on the effective
-- domain.
theorem ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional
    {f : ℝ → WithTop ℝ} (hf : ClosedConvexFunction f) :
    ContinuousOn (withTopRealPart f) (dom f) := by
  let g : ℝ → ℝ := withTopRealPart f
  have hconv : ConvexOn ℝ (dom f) g := hf.convexOn_withTopRealPart
  have hclosed :
      IsClosed {p : ℝ × ℝ | p.1 ∈ dom f ∧ g p.1 ≤ p.2} := by
    rw [← constrainedEpigraph_eq_epigraph_withTopRealPart (subset_rfl : dom f ⊆ dom f)]
    exact hf.isClosed_constrainedEpigraph
  rw [continuousOn_iff_continuous_restrict, continuous_iff_seqContinuous]
  intro u x hu
  have hu_real : Tendsto (fun n ↦ ((u n : dom f) : ℝ)) atTop (𝓝 (x : ℝ)) :=
    tendsto_subtype_rng.1 hu
  have hnear :
      ∀ {δ : ℝ}, 0 < δ →
        ∀ᶠ n in atTop, |((u n : dom f) : ℝ) - (x : ℝ)| < δ := by
    intro δ hδ
    have hball : Metric.ball (x : ℝ) δ ∈ 𝓝 (x : ℝ) :=
      Metric.ball_mem_nhds _ hδ
    simpa [Metric.mem_ball, Real.dist_eq] using hu_real hball
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlower : ∀ᶠ n in atTop, g x - ε / 2 < g (u n) := by
    have hpair :
        Tendsto (fun n ↦ (((u n : dom f) : ℝ), g x - ε / 2)) atTop
          (𝓝 ((x : ℝ), g x - ε / 2)) :=
      hu_real.prodMk_nhds tendsto_const_nhds
    have hnot :
        ((x : ℝ), g x - ε / 2) ∉ {p : ℝ × ℝ | p.1 ∈ dom f ∧ g p.1 ≤ p.2} := by
      have : ¬ g x ≤ g x - ε / 2 := by
        nlinarith [hε]
      rintro ⟨_, hx⟩
      exact this hx
    have hmem :
        {p : ℝ × ℝ | p.1 ∈ dom f ∧ g p.1 ≤ p.2}ᶜ ∈
          𝓝 ((x : ℝ), g x - ε / 2) :=
      hclosed.isOpen_compl.mem_nhds hnot
    filter_upwards [hpair hmem] with n hn
    have hu_mem : ((u n : dom f) : ℝ) ∈ dom f := (u n).2
    exact not_le.mp (fun hle ↦ hn ⟨hu_mem, hle⟩)
  have hupper : ∀ᶠ n in atTop, g (u n) < g x + ε / 2 := by
    by_cases hleft : ∃ z : dom f, (z : ℝ) < (x : ℝ)
    · by_cases hright : ∃ z : dom f, (x : ℝ) < (z : ℝ)
      · rcases hleft with ⟨zl, hzl⟩
        rcases hright with ⟨zr, hzr⟩
        have hxl_pos : 0 < (x : ℝ) - (zl : ℝ) := sub_pos.mpr hzl
        have hxr_pos : 0 < (zr : ℝ) - (x : ℝ) := sub_pos.mpr hzr
        let δl : ℝ :=
          min (((x : ℝ) - (zl : ℝ)) / 2)
            ((((x : ℝ) - (zl : ℝ)) * ε) /
              (2 * (|g zl - g x| + 1)))
        let δr : ℝ :=
          min (((zr : ℝ) - (x : ℝ)) / 2)
            ((((zr : ℝ) - (x : ℝ)) * ε) /
              (2 * (|g zr - g x| + 1)))
        let δ : ℝ := min δl δr
        have hδl_pos : 0 < δl := by
          dsimp [δl]
          apply lt_min
          · exact half_pos hxl_pos
          · positivity
        have hδr_pos : 0 < δr := by
          dsimp [δr]
          apply lt_min
          · exact half_pos hxr_pos
          · positivity
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          exact lt_min hδl_pos hδr_pos
        filter_upwards [hnear hδ_pos] with n hn
        rcases le_or_gt ((u n : dom f) : ℝ) (x : ℝ) with hux | hxu
        · have hzl_un : (zl : ℝ) < ((u n : dom f) : ℝ) := by
            have habs := abs_lt.1 hn
            have hδ_le_δl : δ ≤ δl := by
              dsimp [δ]
              exact min_le_left _ _
            have hδl_half : δl ≤ (((x : ℝ) - (zl : ℝ)) / 2) := by
              dsimp [δl]
              exact min_le_left _ _
            nlinarith
          let coeff : ℝ := (((x : ℝ) - (u n : dom f)) / ((x : ℝ) - (zl : ℝ)))
          have hcoeff_nonneg : 0 ≤ coeff := by
            dsimp [coeff]
            exact div_nonneg (sub_nonneg.mpr hux) (sub_nonneg.mpr hzl.le)
          have hxu_lt_δ : (x : ℝ) - (u n : dom f) < δ := by
            have habs := abs_lt.1 hn
            nlinarith
          have hδ_num :
              (x : ℝ) - (u n : dom f) <
                (((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1)) := by
            have hδ_le_δl : δ ≤ δl := by
              dsimp [δ]
              exact min_le_left _ _
            have hδl_le :
                δl ≤ ((((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1))) := by
              dsimp [δl]
              exact min_le_right _ _
            exact lt_of_lt_of_le hxu_lt_δ (le_trans hδ_le_δl hδl_le)
          have hmul_lt : coeff * |g zl - g x| < ε / 2 := by
            dsimp [coeff]
            exact coeff_mul_abs_lt_half
              (sub_nonneg.mpr hux) hxl_pos hδ_num hε
          have hsec :
              g (u n) ≤ g x + coeff * (g zl - g x) := by
            simpa [g, coeff] using
              convexOn_left_secant_bound hconv zl.2 x.2 hzl_un hux
          have hbound : g (u n) ≤ g x + coeff * |g zl - g x| := by
            have : coeff * (g zl - g x) ≤ coeff * |g zl - g x| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
            nlinarith
          nlinarith
        · let coeff : ℝ := ((((u n : dom f) : ℝ) - (x : ℝ)) / ((zr : ℝ) - (x : ℝ)))
          have huzr : ((u n : dom f) : ℝ) < (zr : ℝ) := by
            have habs := abs_lt.1 hn
            have hδ_le_δr : δ ≤ δr := by
              dsimp [δ]
              exact min_le_right _ _
            have hδr_half : δr ≤ (((zr : ℝ) - (x : ℝ)) / 2) := by
              dsimp [δr]
              exact min_le_left _ _
            nlinarith
          have hcoeff_nonneg : 0 ≤ coeff := by
            dsimp [coeff]
            exact div_nonneg (sub_nonneg.mpr hxu.le) (sub_nonneg.mpr hzr.le)
          have hxu_lt_δ : ((u n : dom f) : ℝ) - (x : ℝ) < δ := by
            have habs := abs_lt.1 hn
            nlinarith
          have hδ_num :
              ((u n : dom f) : ℝ) - (x : ℝ) <
                (((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1)) := by
            have hδ_le_δr : δ ≤ δr := by
              dsimp [δ]
              exact min_le_right _ _
            have hδr_le :
                δr ≤ ((((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1))) := by
              dsimp [δr]
              exact min_le_right _ _
            exact lt_of_lt_of_le hxu_lt_δ (le_trans hδ_le_δr hδr_le)
          have hmul_lt : coeff * |g zr - g x| < ε / 2 := by
            dsimp [coeff]
            exact coeff_mul_abs_lt_half
              (sub_nonneg.mpr hxu.le) hxr_pos hδ_num hε
          have hsec :
              g (u n) ≤ g x + coeff * (g zr - g x) := by
            simpa [g, coeff] using
              convexOn_right_secant_bound hconv x.2 zr.2 hxu.le huzr
          have hbound : g (u n) ≤ g x + coeff * |g zr - g x| := by
            have : coeff * (g zr - g x) ≤ coeff * |g zr - g x| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
            nlinarith
          nlinarith
      · rcases hleft with ⟨zl, hzl⟩
        have hx_max : ∀ {y : ℝ}, y ∈ dom f → y ≤ (x : ℝ) := by
          intro y hy
          by_contra hyx
          exact hright ⟨⟨y, hy⟩, lt_of_not_ge hyx⟩
        have hxl_pos : 0 < (x : ℝ) - (zl : ℝ) := sub_pos.mpr hzl
        let δ : ℝ :=
          min (((x : ℝ) - (zl : ℝ)) / 2)
            ((((x : ℝ) - (zl : ℝ)) * ε) /
              (2 * (|g zl - g x| + 1)))
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          apply lt_min
          · exact half_pos hxl_pos
          · positivity
        filter_upwards [hnear hδ_pos] with n hn
        have hux : ((u n : dom f) : ℝ) ≤ (x : ℝ) := hx_max (u n).2
        have hzl_un : (zl : ℝ) < ((u n : dom f) : ℝ) := by
          have habs := abs_lt.1 hn
          have hδ_half : δ ≤ (((x : ℝ) - (zl : ℝ)) / 2) := by
            dsimp [δ]
            exact min_le_left _ _
          nlinarith
        let coeff : ℝ := (((x : ℝ) - (u n : dom f)) / ((x : ℝ) - (zl : ℝ)))
        have hcoeff_nonneg : 0 ≤ coeff := by
          dsimp [coeff]
          exact div_nonneg (sub_nonneg.mpr hux) (sub_nonneg.mpr hzl.le)
        have hxu_lt_δ : (x : ℝ) - (u n : dom f) < δ := by
          have habs := abs_lt.1 hn
          nlinarith
        have hδ_num :
            (x : ℝ) - (u n : dom f) <
              (((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1)) := by
          have hδ_le :
              δ ≤ ((((x : ℝ) - (zl : ℝ)) * ε) / (2 * (|g zl - g x| + 1))) := by
            dsimp [δ]
            exact min_le_right _ _
          exact lt_of_lt_of_le hxu_lt_δ hδ_le
        have hmul_lt : coeff * |g zl - g x| < ε / 2 := by
          dsimp [coeff]
          exact coeff_mul_abs_lt_half
            (sub_nonneg.mpr hux) hxl_pos hδ_num hε
        have hsec :
            g (u n) ≤ g x + coeff * (g zl - g x) := by
          simpa [g, coeff] using
            convexOn_left_secant_bound hconv zl.2 x.2 hzl_un hux
        have hbound : g (u n) ≤ g x + coeff * |g zl - g x| := by
          have : coeff * (g zl - g x) ≤ coeff * |g zl - g x| := by
            exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
          nlinarith
        nlinarith
    · by_cases hright : ∃ z : dom f, (x : ℝ) < (z : ℝ)
      · rcases hright with ⟨zr, hzr⟩
        have hx_min : ∀ {y : ℝ}, y ∈ dom f → (x : ℝ) ≤ y := by
          intro y hy
          by_contra hyx
          exact hleft ⟨⟨y, hy⟩, lt_of_not_ge hyx⟩
        have hxr_pos : 0 < (zr : ℝ) - (x : ℝ) := sub_pos.mpr hzr
        let δ : ℝ :=
          min (((zr : ℝ) - (x : ℝ)) / 2)
            ((((zr : ℝ) - (x : ℝ)) * ε) /
              (2 * (|g zr - g x| + 1)))
        have hδ_pos : 0 < δ := by
          dsimp [δ]
          apply lt_min
          · exact half_pos hxr_pos
          · positivity
        filter_upwards [hnear hδ_pos] with n hn
        have hxu : (x : ℝ) ≤ ((u n : dom f) : ℝ) := hx_min (u n).2
        have huzr : ((u n : dom f) : ℝ) < (zr : ℝ) := by
          have habs := abs_lt.1 hn
          have hδ_half : δ ≤ (((zr : ℝ) - (x : ℝ)) / 2) := by
            dsimp [δ]
            exact min_le_left _ _
          nlinarith
        let coeff : ℝ := ((((u n : dom f) : ℝ) - (x : ℝ)) / ((zr : ℝ) - (x : ℝ)))
        have hcoeff_nonneg : 0 ≤ coeff := by
          dsimp [coeff]
          exact div_nonneg (sub_nonneg.mpr hxu) (sub_nonneg.mpr hzr.le)
        have hxu_lt_δ : ((u n : dom f) : ℝ) - (x : ℝ) < δ := by
          have habs := abs_lt.1 hn
          nlinarith
        have hδ_num :
            ((u n : dom f) : ℝ) - (x : ℝ) <
              (((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1)) := by
          have hδ_le :
              δ ≤ ((((zr : ℝ) - (x : ℝ)) * ε) / (2 * (|g zr - g x| + 1))) := by
            dsimp [δ]
            exact min_le_right _ _
          exact lt_of_lt_of_le hxu_lt_δ hδ_le
        have hmul_lt : coeff * |g zr - g x| < ε / 2 := by
          dsimp [coeff]
          exact coeff_mul_abs_lt_half
            (sub_nonneg.mpr hxu) hxr_pos hδ_num hε
        have hsec :
            g (u n) ≤ g x + coeff * (g zr - g x) := by
          simpa [g, coeff] using
            convexOn_right_secant_bound hconv x.2 zr.2 hxu huzr
        have hbound : g (u n) ≤ g x + coeff * |g zr - g x| := by
          have : coeff * (g zr - g x) ≤ coeff * |g zr - g x| := by
            exact mul_le_mul_of_nonneg_left (le_abs_self _) hcoeff_nonneg
          nlinarith
        nlinarith
      · have hsingle : ∀ {y : ℝ}, y ∈ dom f → y = (x : ℝ) := by
          intro y hy
          by_cases hxy : y = (x : ℝ)
          · exact hxy
          · rcases lt_or_gt_of_ne hxy with hyx | hxy'
            · exact False.elim <| hleft ⟨⟨y, hy⟩, hyx⟩
            · exact False.elim <| hright ⟨⟨y, hy⟩, hxy'⟩
        filter_upwards [Filter.Eventually.of_forall fun n ↦ hsingle (u n).2] with n hn
        have : g x < g x + ε / 2 := by
          nlinarith
        simpa [g, hn] using this
  have hfinal :
      ∀ᶠ n in atTop,
        dist (((dom f).restrict (withTopRealPart f) ∘ u) n)
          (((dom f).restrict (withTopRealPart f)) x) < ε := by
    filter_upwards [hlower, hupper] with n hn_lower hn_upper
    have : |g (u n) - g x| < ε := by
      rw [abs_sub_lt_iff]
      constructor <;> nlinarith
    simpa [g, Real.dist_eq] using this
  simpa [Filter.eventually_atTop] using hfinal

end
