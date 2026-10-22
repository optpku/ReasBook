/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part3

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 5.24.1: Corollary 7.5.1 transports directly to the punctured interval
`Set.Ioo x y` by reparameterizing points there with the affine segment coefficient. -/
lemma helperForTheorem_5_24_1_segmentLimit_transport_to_Ioo
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x y : ℝ} (hy : y ∈ scalarEffectiveDomain f) (hxy : x < y) :
    Filter.Tendsto (fun z : ℝ => f (scalarPoint z))
      (nhdsWithin x (Set.Ioo x y))
      (nhds (f (scalarPoint x))) := by
  let e : EuclideanSpace Real (Fin 1) ≃L[Real] (Fin 1 → Real) :=
    EuclideanSpace.equiv (𝕜 := Real) (ι := Fin 1)
  let yE : EuclideanSpace Real (Fin 1) := e.symm (scalarPoint y)
  let xE : EuclideanSpace Real (Fin 1) := e.symm (scalarPoint x)
  have hyDom :
      yE ∈
        (fun x : EuclideanSpace Real (Fin 1) => (x : Fin 1 → Real)) ⁻¹'
          effectiveDomain (Set.univ : Set (Fin 1 → Real)) f := by
    simpa [yE, e, scalarEffectiveDomain] using hy
  let g : ℝ → ℝ := fun z => (y - z) / (y - x)
  have hseg :
      Filter.Tendsto
        (fun t : ℝ => f ((1 - t) • scalarPoint y + t • scalarPoint x))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (f (scalarPoint x))) := by
    -- Apply Corollary 7.5.1 with the domain endpoint `y` as the base point of the segment.
    simpa using
      (closedProperConvexFunction_eq_limit_along_segment
        (f := f) hclosed hproper (x := yE) hyDom xE)
  have hg :
      Filter.Tendsto g (nhdsWithin x (Set.Ioo x y)) (nhdsWithin (1 : ℝ) (Set.Iio 1)) := by
    -- The affine parameter tends to `1` from below as `z ↓ x`.
    simpa [g] using
      helperForTheorem_5_24_1_affineParameter_tendsto_one (x := x) (y := y) hxy
  have hcomp := hseg.comp hg
  refine hcomp.congr' ?_
  filter_upwards
      [Filter.Eventually.of_forall
        (fun z =>
          helperForTheorem_5_24_1_segmentParameterization_eq_scalarPoint
            (x := x) (y := y) (z := z) hxy)] with z hz
  -- The chosen parametrization is exactly the point `scalarPoint z`.
  simpa [g] using congrArg f hz

/-- Helper for Theorem 5.24.1: on a finite domain segment, the `EReal` secant slope is exactly
the coercion of the ordinary real secant quotient. -/
lemma helperForTheorem_5_24_1_finiteSecant_eq_coeReal_on_Ioo
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x y z : ℝ} (hx : x ∈ scalarEffectiveDomain f)
    (hy : y ∈ scalarEffectiveDomain f) (_hxy : x < y) (hz : z ∈ Set.Ioo x y) :
    (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal) =
      ((((f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal) / (y - z) : ℝ) : EReal) := by
  have hconv :
      Convex ℝ (scalarEffectiveDomain f) :=
    helperForTheorem_5_24_1_scalarEffectiveDomain_convex f hproper
  have hzDom : z ∈ scalarEffectiveDomain f := by
    -- Every strict interior point of the scalar segment between two domain points stays in the domain.
    exact (hconv.ordConnected.out hx hy) ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  have hyFinite : f (scalarPoint y) ≠ (⊤ : EReal) ∧ f (scalarPoint y) ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hy,
        hproper.2.2 (scalarPoint y) (by simp)⟩
  have hzFinite : f (scalarPoint z) ≠ (⊤ : EReal) ∧ f (scalarPoint z) ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hzDom,
        hproper.2.2 (scalarPoint z) (by simp)⟩
  -- Once both endpoint values are finite, `EReal` subtraction and division reduce to real arithmetic.
  simpa [EReal.coe_div, EReal.coe_sub, EReal.coe_toReal hyFinite.1 hyFinite.2,
    EReal.coe_toReal hzFinite.1 hzFinite.2]

/-- Helper for Theorem 5.24.1: in the left-exterior regime, the fixed-endpoint secant slope from
`z` to a domain point `y` tends to `⊥` as `z ↓ x`. -/
lemma helperForTheorem_5_24_1_secantSlope_tendsto_bot_on_Ioo
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x y : ℝ} (hxLeft : IsLeftOfScalarEffectiveDomain f x)
    (hy : y ∈ scalarEffectiveDomain f) (hxy : x < y) :
    Filter.Tendsto
      (fun z : ℝ => (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal))
      (nhdsWithin x (Set.Ioo x y))
      (nhds (⊥ : EReal)) := by
  have hyFinite : f (scalarPoint y) ≠ (⊤ : EReal) ∧ f (scalarPoint y) ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hy,
        hproper.2.2 (scalarPoint y) (by simp)⟩
  have hxTop : f (scalarPoint x) = (⊤ : EReal) := by
    by_contra hxTop
    exact
      (lt_irrefl x) (hxLeft x (by
        simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using hxTop))
  have hvalueTop :
      Filter.Tendsto (fun z : ℝ => f (scalarPoint z))
        (nhdsWithin x (Set.Ioo x y))
        (nhds (⊤ : EReal)) := by
    -- Route correction: first identify the endpoint value as `⊤`, then reuse the segment transport lemma.
    simpa [hxTop] using
      helperForTheorem_5_24_1_segmentLimit_transport_to_Ioo f hclosed hproper hy hxy
  have hnumBot :
      Filter.Tendsto (fun z : ℝ => f (scalarPoint y) - f (scalarPoint z))
        (nhdsWithin x (Set.Ioo x y))
        (nhds (⊥ : EReal)) := by
    rw [EReal.tendsto_nhds_bot_iff_real]
    intro a
    have hlarge :
        ∀ᶠ z in nhdsWithin x (Set.Ioo x y),
          (((f (scalarPoint y)).toReal - a : ℝ) : EReal) < f (scalarPoint z) := by
      exact
        (EReal.tendsto_nhds_top_iff_real.mp hvalueTop)
          ((f (scalarPoint y)).toReal - a)
    filter_upwards [hlarge] with z hz
    by_cases hztop : f (scalarPoint z) = (⊤ : EReal)
    · simp [hztop]
    · have hzbot : f (scalarPoint z) ≠ (⊥ : EReal) :=
        hproper.2.2 (scalarPoint z) (by simp)
      have hzFinite :
          ((((f (scalarPoint y)).toReal - a : ℝ) : EReal)) <
            (((f (scalarPoint z)).toReal : ℝ) : EReal) := by
        simpa [EReal.coe_toReal hztop hzbot] using hz
      have hzReal : (f (scalarPoint y)).toReal - a < (f (scalarPoint z)).toReal := by
        exact_mod_cast hzFinite
      have hsubReal : (f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal < a := by
        linarith
      have hsubEReal :
          ((((f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal : ℝ)) : EReal) < a := by
        exact_mod_cast hsubReal
      simpa [EReal.coe_sub, EReal.coe_toReal hyFinite.1 hyFinite.2,
        EReal.coe_toReal hztop hzbot] using hsubEReal
  have hden :
      Filter.Tendsto (fun z : ℝ => y - z)
        (nhdsWithin x (Set.Ioo x y))
        (nhds (y - x)) := by
    -- The denominator tends to the positive endpoint length `y - x`.
    simpa using
      (show ContinuousWithinAt (fun z : ℝ => y - z) (Set.Ioo x y) x by fun_prop).tendsto
  have hdenInvReal :
      Filter.Tendsto (fun z : ℝ => (y - z)⁻¹)
        (nhdsWithin x (Set.Ioo x y))
        (nhds ((y - x)⁻¹)) :=
    hden.inv₀ (sub_ne_zero.mpr hxy.ne')
  have hdenInv :
      Filter.Tendsto (fun z : ℝ => (((y - z)⁻¹ : ℝ) : EReal))
        (nhdsWithin x (Set.Ioo x y))
        (nhds ((((y - x)⁻¹ : ℝ) : EReal))) := by
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hdenInvReal
  have hmul :
      Filter.Tendsto
        (fun z : ℝ => ((((y - z)⁻¹ : ℝ) : EReal) * (f (scalarPoint y) - f (scalarPoint z)))
        )
        (nhdsWithin x (Set.Ioo x y))
        (nhds ((((y - x)⁻¹ : ℝ) : EReal) * (⊥ : EReal))) := by
    -- Multiplying a `⊥`-convergent numerator by a positive finite inverse denominator preserves `⊥`.
    exact
      EReal.Tendsto.mul hdenInv hnumBot
        (Or.inl (by simp [sub_ne_zero.mpr hxy.ne']))
        (Or.inl (by simp [sub_ne_zero.mpr hxy.ne']))
        (Or.inl (by simp))
        (Or.inl (by simp))
  have hrewrite :
      (fun z : ℝ => (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal)) =ᶠ[
        nhdsWithin x (Set.Ioo x y)]
        fun z : ℝ =>
          ((((y - z)⁻¹ : ℝ) : EReal) * (f (scalarPoint y) - f (scalarPoint z))) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    -- On the punctured interval, the secant quotient is the inverse-denominator product.
    simpa [EReal.div_eq_inv_mul, EReal.coe_inv]
  have htarget :
      ((((y - x)⁻¹ : ℝ) : EReal) * (⊥ : EReal)) = (⊥ : EReal) := by
    have hpos : 0 < ((y - x)⁻¹ : ℝ) := inv_pos.mpr (sub_pos.mpr hxy)
    simpa using EReal.bot_mul_coe_of_pos hpos
  simpa [htarget] using hmul.congr' hrewrite.symm

/-- Helper for Theorem 5.24.1: the positive-step directional quotient in direction `1` is exactly
the scalar secant from `x` to `x + t`. -/
lemma helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant
    (f : (Fin 1 → ℝ) → EReal) (x t : ℝ) :
    directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t =
      (f (scalarPoint (x + t)) - f (scalarPoint x)) / (t : EReal) := by
  -- Expanding the `Fin 1` direction `1` identifies the translated endpoint with `scalarPoint (x+t)`.
  have hstep :
      scalarPoint x + t • scalarPoint 1 = scalarPoint (x + t) := by
    ext i
    simp [scalarPoint]
  simp [directionalDifferenceQuotientAt, hstep]

/-- Helper for Theorem 5.24.1: at a domain point `x`, the fixed-endpoint secant slope to a
domain point `y > x` tends to the secant value at `x` as `z ↓ x`. -/
lemma helperForTheorem_5_24_1_secantSlope_tendsto_value_on_Ioo
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x y : ℝ} (hx : x ∈ scalarEffectiveDomain f)
    (hy : y ∈ scalarEffectiveDomain f) (hxy : x < y) :
    Filter.Tendsto
      (fun z : ℝ => (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal))
      (nhdsWithin x (Set.Ioo x y))
      (nhds ((f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal))) := by
  have hyFinite : f (scalarPoint y) ≠ (⊤ : EReal) ∧ f (scalarPoint y) ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hy,
        hproper.2.2 (scalarPoint y) (by simp)⟩
  have hxFinite : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hx,
        hproper.2.2 (scalarPoint x) (by simp)⟩
  have hvalue :
      Filter.Tendsto (fun z : ℝ => f (scalarPoint z))
        (nhdsWithin x (Set.Ioo x y))
        (nhds (f (scalarPoint x))) :=
    helperForTheorem_5_24_1_segmentLimit_transport_to_Ioo f hclosed hproper hy hxy
  have htoReal :
      Filter.Tendsto (fun z : ℝ => (f (scalarPoint z)).toReal)
        (nhdsWithin x (Set.Ioo x y))
        (nhds ((f (scalarPoint x)).toReal)) := by
    -- Transport the `EReal` value limit through `toReal` at the finite endpoint `x`.
    exact (EReal.tendsto_toReal hxFinite.1 hxFinite.2).comp hvalue
  have hnum :
      Filter.Tendsto
        (fun z : ℝ => (f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal)
        (nhdsWithin x (Set.Ioo x y))
        (nhds ((f (scalarPoint y)).toReal - (f (scalarPoint x)).toReal)) := by
    -- The real numerator is a continuous affine transform of the transported value limit.
    exact tendsto_const_nhds.sub htoReal
  have hden :
      Filter.Tendsto (fun z : ℝ => y - z)
        (nhdsWithin x (Set.Ioo x y))
        (nhds (y - x)) := by
    -- The denominator stays in the ordinary real layer and tends to the endpoint spacing.
    simpa using
      (show ContinuousWithinAt (fun z : ℝ => y - z) (Set.Ioo x y) x by fun_prop).tendsto
  have hquotReal :
      Filter.Tendsto
        (fun z : ℝ => ((f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal) / (y - z))
        (nhdsWithin x (Set.Ioo x y))
        (nhds (((f (scalarPoint y)).toReal - (f (scalarPoint x)).toReal) / (y - x))) := by
    -- Ordinary real continuity of division now finishes the finite quotient limit.
    exact hnum.div hden (sub_ne_zero.mpr hxy.ne')
  have hquot :
      Filter.Tendsto
        (fun z : ℝ =>
          ((((f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal) / (y - z) : ℝ) : EReal))
        (nhdsWithin x (Set.Ioo x y))
        (nhds
          (((((f (scalarPoint y)).toReal - (f (scalarPoint x)).toReal) / (y - x) : ℝ) :
            EReal))) := by
    exact continuous_coe_real_ereal.continuousAt.tendsto.comp hquotReal
  have hrewrite :
      (fun z : ℝ => (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal)) =ᶠ[
        nhdsWithin x (Set.Ioo x y)]
        fun z : ℝ =>
          ((((f (scalarPoint y)).toReal - (f (scalarPoint z)).toReal) / (y - z) : ℝ) : EReal) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    -- The new finite-secant helper isolates all `EReal` coercion plumbing outside the filter proof.
    exact helperForTheorem_5_24_1_finiteSecant_eq_coeReal_on_Ioo
      f hproper hx hy hxy hz
  have htarget :
      (((((f (scalarPoint y)).toReal - (f (scalarPoint x)).toReal) / (y - x) : ℝ) : EReal)) =
        (f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal) := by
    -- At the endpoint `x`, the same finite arithmetic rewrite identifies the limiting target.
    symm
    simpa [EReal.coe_div, EReal.coe_sub, EReal.coe_toReal hyFinite.1 hyFinite.2,
      EReal.coe_toReal hxFinite.1 hxFinite.2]
  simpa [htarget] using hquot.congr' hrewrite.symm

/-- Helper for Theorem 5.24.1: at a domain point, any lower bound for all strict-right derivative
values is already a lower bound for the derivative value at the base point. -/
lemma helperForTheorem_5_24_1_domain_tailLowerBound_le_rightDerivativeAt
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ} {u : EReal} (hx : x ∈ scalarEffectiveDomain f)
    (hu : ∀ z > x, u ≤ rightDerivativeExtension f z) :
    u ≤ rightDerivativeExtension f x := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact
      ⟨mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hx,
        hproper.2.2 (scalarPoint x) (by simp)⟩
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hx
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hf (scalarPoint x) hxFinite with
    ⟨hdirRight, _hposRight, _hconvRight, _hzeroRight, _hsymmRight⟩
  have hquotLower :
      ∀ {t : ℝ}, 0 < t →
        u ≤ directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t := by
    intro t ht
    let y : ℝ := x + t
    have hxy : x < y := by
      dsimp [y]
      linarith
    by_cases hy : y ∈ scalarEffectiveDomain f
    · have hlimit :
          Filter.Tendsto
            (fun z : ℝ =>
              (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal))
            (nhdsWithin x (Set.Ioo x y))
            (nhds ((f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal))) :=
        helperForTheorem_5_24_1_secantSlope_tendsto_value_on_Ioo f hclosed hproper hx hy hxy
      have hnebot : (nhdsWithin x (Set.Ioo x y)).NeBot := by
        exact
          (mem_closure_iff_nhdsWithin_neBot).1 (by
            rw [closure_Ioo hxy.ne]
            simp [hxy.le])
      letI := hnebot
      have hmem :
          ∀ᶠ z in nhdsWithin x (Set.Ioo x y),
            (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal) ∈ Set.Ici u := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        have hconv :
            Convex ℝ (scalarEffectiveDomain f) :=
          helperForTheorem_5_24_1_scalarEffectiveDomain_convex f hproper
        have hzDom : z ∈ scalarEffectiveDomain f := by
          exact (hconv.ordConnected.out hx hy) ⟨le_of_lt hz.1, le_of_lt hz.2⟩
        have hsec :
            rightDerivativeExtension f z ≤
              (f (scalarPoint y) - f (scalarPoint z)) / (((y - z : ℝ)) : EReal) :=
          (helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
            f hproper hz.2 hzDom hy).1
        exact le_trans (hu z hz.1) hsec
      have htargetMem :
          ((f (scalarPoint y) - f (scalarPoint x)) / (((y - x : ℝ)) : EReal)) ∈ Set.Ici u :=
        isClosed_Ici.mem_of_tendsto hlimit hmem
      simpa [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant,
        y] using htargetMem
    · have hyTop : f (scalarPoint y) = (⊤ : EReal) := by
        by_contra hyTop
        exact hy (by
          simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top] using hyTop)
      -- Off the effective domain to the right, the positive-step quotient is `⊤`.
      have hquotTop :
          directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t = (⊤ : EReal) := by
        rw [helperForTheorem_5_24_1_directionalDifferenceQuotient_dirOne_eq_scalarSecant, hyTop]
        rw [EReal.top_sub hxFinite.1]
        have htE : (0 : EReal) < (t : EReal) := by
          exact_mod_cast ht
        simpa using
          (EReal.top_div_of_pos_ne_top htE (by simp : (t : EReal) ≠ ⊤))
      rw [hquotTop]
      exact le_top
  have hnonempty :
      ((Set.Ioi (0 : ℝ)).image
        fun t : ℝ => directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t).Nonempty := by
    refine ⟨directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) 1, ?_⟩
    exact ⟨1, by simp, rfl⟩
  have hlower :
      u ≤ sInf
        ((Set.Ioi (0 : ℝ)).image
          fun t : ℝ => directionalDifferenceQuotientAt f (scalarPoint x) (scalarPoint 1) t) := by
    refine le_csInf hnonempty ?_
    intro q hq
    rcases hq with ⟨t, ht, rfl⟩
    exact hquotLower ht
  have hupper :
      u ≤ upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) := by
    simpa [(hdirRight (scalarPoint 1)).2.2] using hlower
  -- The domain value of the extension is exactly the upper derivative in direction `1`.
  simpa [rightDerivativeExtension, hxNot.1, hxNot.2] using hupper

/-- Helper for Theorem 5.24.1: outside the trivial right-exterior case, the value at `x` is the
greatest lower bound of the right tail of `rightDerivativeExtension`. -/
lemma helperForTheorem_5_24_1_rightDerivativeExtension_Ioi_isGLB
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x : ℝ} (hxNotRight : ¬ IsRightOfScalarEffectiveDomain f x) :
    IsGLB ((rightDerivativeExtension f) '' Set.Ioi x) (rightDerivativeExtension f x) := by
  have hmono : Monotone (rightDerivativeExtension f) :=
    (helperForTheorem_5_24_1_monotoneDerivativeExtensions f hproper).1
  refine ⟨?_, ?_⟩
  · intro z hz
    rcases hz with ⟨w, hwx, rfl⟩
    exact hmono (le_of_lt hwx)
  · intro u hu
    have huTail : ∀ z > x, u ≤ rightDerivativeExtension f z := by
      intro z hz
      exact hu ⟨z, hz, rfl⟩
    by_cases hxLeft : IsLeftOfScalarEffectiveDomain f x
    · rcases properConvexFunctionOn_effectiveDomain_nonempty (f := f) hproper with ⟨yVec, hyVec⟩
      have hscalarY : scalarPoint (yVec 0) = yVec := by
        ext i
        have hi : i = 0 := Subsingleton.elim i 0
        simpa [scalarPoint, hi]
      have hy : yVec 0 ∈ scalarEffectiveDomain f := by
        simpa [scalarEffectiveDomain, hscalarY] using hyVec
      have hxy : x < yVec 0 := hxLeft _ hy
      have hnebot : (nhdsWithin x (Set.Ioo x (yVec 0))).NeBot := by
        exact
          (mem_closure_iff_nhdsWithin_neBot).1 (by
            rw [closure_Ioo hxy.ne]
            simp [hxy.le])
      letI := hnebot
      have hmem :
          ∀ᶠ z in nhdsWithin x (Set.Ioo x (yVec 0)),
            (f (scalarPoint (yVec 0)) - f (scalarPoint z)) / (((yVec 0 - z : ℝ)) : EReal) ∈
              Set.Ici u := by
        filter_upwards [self_mem_nhdsWithin] with z hz
        by_cases hzLeft : IsLeftOfScalarEffectiveDomain f z
        · have hzNotRight :
            ¬ IsRightOfScalarEffectiveDomain f z :=
              helperForTheorem_5_24_1_not_right_of_left f hproper hzLeft
          have huzBot : u ≤ (⊥ : EReal) := by
            simpa [rightDerivativeExtension, hzLeft, hzNotRight] using huTail z hz.1
          exact le_trans huzBot bot_le
        · have hzNotRight : ¬ IsRightOfScalarEffectiveDomain f z := by
            intro hzRight
            have hylt : yVec 0 < z := hzRight _ hy
            exact (not_lt_of_ge (le_of_lt hz.2)) hylt
          have hzDom :
              z ∈ scalarEffectiveDomain f :=
            helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
              f hproper hzLeft hzNotRight
          have hsec :
              rightDerivativeExtension f z ≤
                (f (scalarPoint (yVec 0)) - f (scalarPoint z)) / (((yVec 0 - z : ℝ)) : EReal) :=
            (helperForTheorem_5_24_1_secantSlope_between_rightAndLeftDerivatives
              f hproper hz.2 hzDom hy).1
          exact le_trans (huTail z hz.1) hsec
      have hbotMem :
          (⊥ : EReal) ∈ Set.Ici u :=
        isClosed_Ici.mem_of_tendsto
          (helperForTheorem_5_24_1_secantSlope_tendsto_bot_on_Ioo f hclosed hproper hxLeft hy hxy)
          hmem
      simpa [rightDerivativeExtension, hxLeft, hxNotRight] using hbotMem
    · have hxDom :
          x ∈ scalarEffectiveDomain f :=
        helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
          f hproper hxLeft hxNotRight
      exact
        helperForTheorem_5_24_1_domain_tailLowerBound_le_rightDerivativeAt
          f hclosed hproper hxDom huTail

/-- Helper for Theorem 5.24.1: the remaining hard part is the right continuity of the extended
right derivative. -/
lemma helperForTheorem_5_24_1_rightDerivativeExtension_rightContinuous
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) (x : ℝ) :
    Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
      (nhds (rightDerivativeExtension f x)) := by
  by_cases hxRight : IsRightOfScalarEffectiveDomain f x
  · have hxNotLeft :
      ¬ IsLeftOfScalarEffectiveDomain f x :=
        helperForTheorem_5_24_1_not_left_of_right f hproper hxRight
    have hEventually :
        rightDerivativeExtension f =ᶠ[nhdsWithin x (Set.Ioi x)] fun _ => (⊤ : EReal) := by
      -- Once `x` is already to the right of the domain, every larger point stays there.
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hzRight :
          IsRightOfScalarEffectiveDomain f z :=
        helperForTheorem_5_24_1_rightOfScalarEffectiveDomain_mono f (le_of_lt hz) hxRight
      have hzNotLeft :
          ¬ IsLeftOfScalarEffectiveDomain f z :=
        helperForTheorem_5_24_1_not_left_of_right f hproper hzRight
      simp [rightDerivativeExtension, hzRight, hzNotLeft]
    have hconst :
        Filter.Tendsto (fun _ : ℝ => (⊤ : EReal)) (nhdsWithin x (Set.Ioi x)) (nhds (⊤ : EReal)) :=
      tendsto_const_nhds
    simpa [rightDerivativeExtension, hxRight, hxNotLeft] using hconst.congr' hEventually.symm
  -- Route correction: instead of proving continuity directly, first identify the strict-right tail
  -- infimum with the textbook value at `x`, then apply the monotone right-limit theorem.
  have hmono : Monotone (rightDerivativeExtension f) :=
    (helperForTheorem_5_24_1_monotoneDerivativeExtensions f hproper).1
  have htail :
      IsGLB ((rightDerivativeExtension f) '' Set.Ioi x) (rightDerivativeExtension f x) :=
    helperForTheorem_5_24_1_rightDerivativeExtension_Ioi_isGLB f hclosed hproper hxRight
  have hlimit :
      Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
        (nhds (sInf ((rightDerivativeExtension f) '' Set.Ioi x))) :=
    hmono.tendsto_nhdsGT x
  simpa [htail.sInf_eq] using hlimit

/-- Helper for Theorem 5.24.1: left continuity of the extended left derivative is obtained by
applying right continuity to the reflected function and transporting along `t ↦ -t`. -/
lemma helperForTheorem_5_24_1_leftDerivativeExtension_leftContinuous
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (hReflectedRightCont :
      ∀ x : ℝ,
        Filter.Tendsto (rightDerivativeExtension (fun u => f (-u)))
          (nhdsWithin x (Set.Ioi x))
          (nhds (rightDerivativeExtension (fun u => f (-u)) x))) :
    ∀ x : ℝ,
      Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Iio x))
        (nhds (leftDerivativeExtension f x)) := by
  intro x
  have hnegMap :
      Filter.Tendsto (fun t : ℝ => -t) (nhdsWithin x (Set.Iio x))
        (nhdsWithin (-x) (Set.Ioi (-x))) := by
    -- Negation swaps left neighborhoods at `x` with right neighborhoods at `-x`.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within (fun t : ℝ => -t) ?_ ?_
    · simpa using
        (show ContinuousWithinAt (fun t : ℝ => -t) (Set.Iio x) x by fun_prop).tendsto
    · filter_upwards [self_mem_nhdsWithin] with t ht
      show -t ∈ Set.Ioi (-x)
      have htx : t < x := ht
      simpa [Set.mem_Ioi] using (neg_lt_neg htx)
  have hcomp :=
    (hReflectedRightCont (-x)).comp hnegMap
  have hcomp₁ :
      Filter.Tendsto
        (fun t : ℝ => rightDerivativeExtension (fun u => f (-u)) (-t))
        (nhdsWithin x (Set.Iio x))
        (nhds (rightDerivativeExtension (fun u => f (-u)) (-x))) := by
    simpa using hcomp
  have hcomp₂ :
      Filter.Tendsto (fun t : ℝ => - leftDerivativeExtension f t)
        (nhdsWithin x (Set.Iio x))
        (nhds (rightDerivativeExtension (fun u => f (-u)) (-x))) := by
    -- Rewrite the reflected right derivative using the pointwise reflection identity.
    refine hcomp₁.congr' ?_
    filter_upwards with t
    have hIdt :=
      (helperForTheorem_5_24_1_reflectedFunction_derivativeIdentities f hproper t).1
    simpa [hIdt]
  have hIdx :=
    (helperForTheorem_5_24_1_reflectedFunction_derivativeIdentities f hproper x).1
  have hcomp₃ :
      Filter.Tendsto (fun t : ℝ => - leftDerivativeExtension f t)
        (nhdsWithin x (Set.Iio x))
        (nhds (- leftDerivativeExtension f x)) := by
    simpa [hIdx] using hcomp₂
  -- Negating once more removes the reflected sign change and yields the desired left continuity.
  simpa using hcomp₃.neg

/-- Helper for Theorem 5.24.1: once the two self-continuity statements are known, the remaining
cross-limits follow by squeezing with the derivative-order inequalities. -/
lemma helperForTheorem_5_24_1_crossLimits_from_selfContinuity
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    (hRightSelf : ∀ x : ℝ,
      Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
        (nhds (rightDerivativeExtension f x)))
    (hLeftSelf : ∀ x : ℝ,
      Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Iio x))
        (nhds (leftDerivativeExtension f x)))
    (x : ℝ) :
    Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Iio x))
        (nhds (leftDerivativeExtension f x)) ∧
      Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
        (nhds (rightDerivativeExtension f x)) := by
  constructor
  · refine tendsto_order.2 ?_
    constructor
    · intro a ha
      have hLeftOrder := tendsto_order.1 (hLeftSelf x)
      -- A strict lower bound on `f'_-(x)` is eventually a strict lower bound on `f'_-(z)`,
      -- hence also on `f'_+(z)` by the same-point inequality.
      filter_upwards [hLeftOrder.1 a ha] with z hz
      exact lt_of_lt_of_le hz
        (helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
          f hproper z)
    · intro b hb
      -- For every `z < x`, the order chain already gives `f'_+(z) ≤ f'_-(x) < b`.
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact lt_of_le_of_lt
        (helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
          f hproper hz)
        hb
  · refine tendsto_order.2 ?_
    constructor
    · intro a ha
      -- For every `z > x`, the order chain gives `a < f'_+(x) ≤ f'_-(z)`.
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact lt_of_lt_of_le ha
        (helperForTheorem_5_24_1_rightDerivativeExtension_le_leftDerivativeExtension_of_lt
          f hproper hz)
    · intro b hb
      have hRightOrder := tendsto_order.1 (hRightSelf x)
      -- A strict upper bound on `f'_+(x)` is eventually a strict upper bound on `f'_+(z)`,
      -- and `f'_-(z) ≤ f'_+(z)` transfers that bound to the left derivative.
      filter_upwards [hRightOrder.2 b hb] with z hz
      exact lt_of_le_of_lt
        (helperForTheorem_5_24_1_leftDerivativeExtension_le_rightDerivativeExtension
          f hproper z)
        hz

-- Proof sketch: specialize the one-dimensional convex-difference-quotient monotonicity from
-- Theorem 23.1 to the directions `1` and `-1`, use closedness and properness to identify the
-- finite interior-domain regime, and then transport the standard monotone one-sided-limit facts
-- for convex slopes to the domain-extended derivatives.
/-- Theorem 5.24.1: for a closed proper convex function on `ℝ`, the right and left derivative
extensions are nondecreasing, finite on the interior of the effective domain, satisfy
`f'_+(z₁) ≤ f'_-(x) ≤ f'_+(x) ≤ f'_-(z₂)` whenever `z₁ < x < z₂`, and have the one-sided limit
relations
`lim_{z ↓ x} f'_+(z) = f'_+(x)`, `lim_{z ↑ x} f'_+(z) = f'_-(x)`,
`lim_{z ↓ x} f'_-(z) = f'_+(x)`, and `lim_{z ↑ x} f'_-(z) = f'_-(x)`. -/
theorem oneDimensional_derivativeExtensions_monotone_ordered_and_oneSidedContinuous
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) :
    Monotone (rightDerivativeExtension f) ∧
      Monotone (leftDerivativeExtension f) ∧
      (∀ x ∈ interior (scalarEffectiveDomain f),
        rightDerivativeExtension f x ≠ (⊤ : EReal) ∧
          rightDerivativeExtension f x ≠ (⊥ : EReal) ∧
          leftDerivativeExtension f x ≠ (⊤ : EReal) ∧
          leftDerivativeExtension f x ≠ (⊥ : EReal)) ∧
      (∀ ⦃z1 x z2 : ℝ⦄, z1 < x → x < z2 →
        rightDerivativeExtension f z1 ≤ leftDerivativeExtension f x ∧
          leftDerivativeExtension f x ≤ rightDerivativeExtension f x ∧
          rightDerivativeExtension f x ≤ leftDerivativeExtension f z2) ∧
      (∀ x : ℝ,
        Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
          (nhds (rightDerivativeExtension f x))) ∧
      (∀ x : ℝ,
        Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Iio x))
          (nhds (leftDerivativeExtension f x))) ∧
      (∀ x : ℝ,
        Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
          (nhds (rightDerivativeExtension f x))) ∧
      (∀ x : ℝ,
    Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Iio x))
          (nhds (leftDerivativeExtension f x))) := by
  have hmonotone :
      Monotone (rightDerivativeExtension f) ∧ Monotone (leftDerivativeExtension f) :=
    helperForTheorem_5_24_1_monotoneDerivativeExtensions f hproper
  have hRightSelf :
      ∀ x : ℝ,
        Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
          (nhds (rightDerivativeExtension f x)) := by
    intro x
    -- Package the remaining right-continuity task into the dedicated helper above.
    exact
      helperForTheorem_5_24_1_rightDerivativeExtension_rightContinuous
        f hclosed hproper x
  have hReflectedRightSelf :
      ∀ x : ℝ,
        Filter.Tendsto (rightDerivativeExtension (fun u => f (-u))) (nhdsWithin x (Set.Ioi x))
          (nhds (rightDerivativeExtension (fun u => f (-u)) x)) :=
    helperForTheorem_5_24_1_rightDerivativeExtension_rightContinuous
      (fun u => f (-u))
      (helperForTheorem_5_24_1_reflectedFunction_closed f hclosed)
      (helperForTheorem_5_24_1_reflectedFunction_proper f hproper)
  have hLeftSelf :
      ∀ x : ℝ,
        Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Iio x))
          (nhds (leftDerivativeExtension f x)) := by
    intro x
    -- Reflection turns left continuity of `f'_-` into the already isolated right continuity task.
    exact
      helperForTheorem_5_24_1_leftDerivativeExtension_leftContinuous
        f hproper hReflectedRightSelf x
  have hCross :
      ∀ x : ℝ,
        Filter.Tendsto (rightDerivativeExtension f) (nhdsWithin x (Set.Iio x))
            (nhds (leftDerivativeExtension f x)) ∧
          Filter.Tendsto (leftDerivativeExtension f) (nhdsWithin x (Set.Ioi x))
            (nhds (rightDerivativeExtension f x)) := by
    intro x
    -- Once the self-limits are known, the two cross-limits are pure order squeezing.
    exact
      helperForTheorem_5_24_1_crossLimits_from_selfContinuity
        f hproper hRightSelf hLeftSelf x
  refine ⟨hmonotone.1, hmonotone.2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    -- Interior points are genuine domain points, so both derivative extensions are finite.
    exact
      helperForTheorem_5_24_1_scalarInterior_finiteDirectionalDerivatives
        f hproper hx
  · intro z1 x z2 hz1x hxz2
    -- The scalar secant-slope comparison yields the textbook three-term chain.
    exact
      helperForTheorem_5_24_1_derivativeExtensions_orderChain
        f hproper hz1x hxz2
  · intro x
    -- This is the dedicated right-continuity helper.
    exact hRightSelf x
  · intro x
    -- The left-limit of `f'_+` is the first squeeze consequence of the two self-limits.
    exact (hCross x).1
  · intro x
    -- The right-limit of `f'_-` is the second squeeze consequence.
    exact (hCross x).2
  · intro x
    -- Reflection packages the left continuity of `f'_-` into the reflected right continuity task.
    exact hLeftSelf x

-- Proof sketch: combine the one-dimensional subgradient criterion from Chapter 23 with Theorem
-- 5.24.1. A scalar subgradient gives lower bounds on the directional derivatives in directions
-- `1` and `-1`, yielding `f'_-(x) ≤ x* ≤ f'_+(x)`. Conversely, the monotonicity and one-sided
-- continuity of the derivative extensions identify every scalar in that interval with a
-- supporting slope at `x`.
/-- Helper for Theorem 5.24.2: evaluating the Euclidean dual vector attached to `a` on the scalar
point `b` recovers the scalar product `a * b`. -/
lemma helperForTheorem_5_24_2_dotProductEquiv_apply_scalarPoint
    (a b : ℝ) :
    (((dotProductEquiv ℝ (Fin 1) (scalarPoint a)) (scalarPoint b) : ℝ)) = a * b := by
  -- In one dimension, the dot product is just scalar multiplication.
  simp [dotProductEquiv, scalarPoint, dotProduct]

/-- Helper for Theorem 5.24.2: every direction in `Fin 1 → ℝ` is determined by its `0`th
coordinate, hence equals the corresponding scalar point. -/
lemma helperForTheorem_5_24_2_direction_eq_scalarPoint_apply_zero
    (y : Fin 1 → ℝ) :
    y = scalarPoint (y 0) := by
  -- Extensionality collapses the unique coordinate of `Fin 1`.
  ext i
  have hi : i = 0 := Subsingleton.elim i 0
  simpa [scalarPoint, hi]

/-- Helper for Theorem 5.24.2: every scalar direction is a positive multiple of either `1` or
`-1`, according to the sign choice used later in the proof. -/
lemma helperForTheorem_5_24_2_scalarDirection_rewrite
    (a : ℝ) :
    scalarPoint a = a • scalarPoint 1 ∧ scalarPoint a = (-a) • scalarPoint (-1) := by
  constructor
  · -- The positive-direction rewrite is coordinatewise scalar multiplication by `a`.
    ext i
    simp [scalarPoint]
  · -- The negative-direction rewrite records the same vector with positive coefficient `-a`.
    ext i
    simp [scalarPoint]

/-- Helper for Theorem 5.24.2: a scalar subgradient at a domain point forces the scalar slope to
lie between the left and right derivative extensions. -/
lemma helperForTheorem_5_24_2_subgradient_implies_intervalBounds
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x xStar : ℝ} (hx : x ∈ scalarEffectiveDomain f)
    (hxStar : dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ f (scalarPoint x)) :
    leftDerivativeExtension f x ≤ ((xStar : ℝ) : EReal) ∧
      (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension f x) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxMemUniv : scalarPoint x ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  have hxFiniteTop :
      f (scalarPoint x) ≠ (⊤ : EReal) := by
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hx
  have hxFiniteBot :
      f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact hproper.2.2 (scalarPoint x) hxMemUniv
  have hxFinite :
      f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact ⟨hxFiniteTop, hxFiniteBot⟩
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hx
  have hxStarSub :
      IsSubgradientAt f (scalarPoint x) (dotProductEquiv ℝ (Fin 1) (scalarPoint xStar)) := by
    simpa [subdifferentialAt] using hxStar
  have hminor :
      ∀ y : Fin 1 → ℝ,
        (((dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) y : ℝ) : EReal) ≤
          upperDirectionalDerivativeAt f (scalarPoint x) y) := by
    -- Theorem 23.2 converts subgradient membership into a directional-derivative minorant.
    exact
      (subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
        f hf (scalarPoint x) hxFinite
        (dotProductEquiv ℝ (Fin 1) (scalarPoint xStar))).1.mp hxStarSub
  constructor
  · -- Evaluating the minorant at direction `-1` produces the left derivative bound.
    have hdirMinus :
        ((((-xStar : ℝ) : EReal))) ≤
          upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1)) := by
      simpa [dotProductEquiv, scalarPoint, dotProduct] using
        hminor (scalarPoint (-1))
    simpa [leftDerivativeExtension, hxNot.2, hxNot.1] using
      (EReal.neg_le.mp (by simpa using hdirMinus))
  · -- Evaluating at direction `1` gives the right derivative bound directly.
    have hdirOne :
        (((xStar : ℝ) : EReal)) ≤
          upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) := by
      simpa [dotProductEquiv, scalarPoint, dotProduct] using
        hminor (scalarPoint 1)
    simpa [rightDerivativeExtension, hxNot.2, hxNot.1] using hdirOne

/-- Helper for Theorem 5.24.2: scalar interval bounds imply the directional-derivative minorant
required by Theorem 23.2. -/
lemma helperForTheorem_5_24_2_intervalBounds_imply_directional_minorant
    (f : (Fin 1 → ℝ) → EReal)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f)
    {x xStar : ℝ} (hx : x ∈ scalarEffectiveDomain f)
    (hxStar :
      leftDerivativeExtension f x ≤ ((xStar : ℝ) : EReal) ∧
        (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension f x)) :
    ∀ y : Fin 1 → ℝ,
      (((dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) y : ℝ) : EReal) ≤
        upperDirectionalDerivativeAt f (scalarPoint x) y) := by
  have hf : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxMemUniv : scalarPoint x ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
    simp
  have hxFiniteTop :
      f (scalarPoint x) ≠ (⊤ : EReal) := by
    exact mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hx
  have hxFiniteBot :
      f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact hproper.2.2 (scalarPoint x) hxMemUniv
  have hxFinite :
      f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
    exact ⟨hxFiniteTop, hxFiniteBot⟩
  have hxNot :
      ¬ IsLeftOfScalarEffectiveDomain f x ∧ ¬ IsRightOfScalarEffectiveDomain f x :=
    helperForTheorem_5_24_1_not_left_not_right_of_mem_scalarEffectiveDomain f hx
  rcases convex_directionalDerivative_monotone_exists_and_sublinear
      f hf (scalarPoint x) hxFinite with
    ⟨_hdirData, hpos, _hconv, hzero, _hsymm⟩
  have hRight :
      (((xStar : ℝ) : EReal)) ≤ upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) := by
    -- On the domain branch, the right derivative extension is the actual directional derivative.
    simpa [rightDerivativeExtension, hxNot.2, hxNot.1] using hxStar.2
  have hLeftNeg :
      (((-xStar : ℝ) : EReal)) ≤
        upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1)) := by
    -- The left derivative bound is equivalent, after negation, to a bound in direction `-1`.
    exact EReal.neg_le.mp (by simpa [leftDerivativeExtension, hxNot.2, hxNot.1] using hxStar.1)
  intro y
  have hyScalar :
      y = scalarPoint (y 0) :=
    helperForTheorem_5_24_2_direction_eq_scalarPoint_apply_zero y
  by_cases hyPos : 0 < y 0
  · have hyRewrite : y = (y 0) • scalarPoint 1 := by
      calc
        y = scalarPoint (y 0) := hyScalar
        _ = (y 0) • scalarPoint 1 := (helperForTheorem_5_24_2_scalarDirection_rewrite (y 0)).1
    have hyNonneg : 0 ≤ y 0 := le_of_lt hyPos
    -- Positive directions are scalar multiples of `1`, so positive homogeneity transfers the
    -- right-endpoint bound to the arbitrary direction `y`.
    calc
      (((dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) y : ℝ) : EReal)) =
          (((xStar * y 0 : ℝ) : EReal)) := by
            rw [hyScalar]
            simp [dotProductEquiv, scalarPoint, dotProduct,
              helperForTheorem_5_24_2_dotProductEquiv_apply_scalarPoint]
      _ = ((y 0 : EReal) * (((xStar : ℝ) : EReal))) := by
        simp [EReal.coe_mul, mul_comm]
      _ ≤ (y 0 : EReal) *
            upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint 1) := by
              exact mul_le_mul_of_nonneg_left hRight (by exact_mod_cast hyNonneg)
      _ = upperDirectionalDerivativeAt f (scalarPoint x) ((y 0) • scalarPoint 1) := by
        symm
        simpa using hpos (scalarPoint 1) (y 0) hyPos
      _ = upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (y 0)) := by
        rw [← (helperForTheorem_5_24_2_scalarDirection_rewrite (y 0)).1]
      _ = upperDirectionalDerivativeAt f (scalarPoint x) y := by
        rw [hyScalar.symm]
  · by_cases hyNeg : y 0 < 0
    · have hyScalePos : 0 < -y 0 := by
        linarith
      have hyRewrite : y = (-y 0) • scalarPoint (-1) := by
        calc
          y = scalarPoint (y 0) := hyScalar
          _ = (-y 0) • scalarPoint (-1) :=
            (helperForTheorem_5_24_2_scalarDirection_rewrite (y 0)).2
      have hyScaleNonneg : 0 ≤ -y 0 := le_of_lt hyScalePos
      -- Negative directions are positive multiples of `-1`, so the left-endpoint bound gives the
      -- required minorant after rewriting the scalar product.
      calc
        (((dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) y : ℝ) : EReal)) =
            (((xStar * y 0 : ℝ) : EReal)) := by
              rw [hyScalar]
              simp [dotProductEquiv, scalarPoint, dotProduct,
                helperForTheorem_5_24_2_dotProductEquiv_apply_scalarPoint]
        _ = ((((-y 0) * (-xStar) : ℝ) : EReal)) := by
          congr 1
          ring
        _ = ((-y 0 : EReal) * (((-xStar : ℝ) : EReal))) := by
          simp [EReal.coe_mul]
        _ ≤ (-y 0 : EReal) *
              upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (-1)) := by
                exact mul_le_mul_of_nonneg_left hLeftNeg (by exact_mod_cast hyScaleNonneg)
        _ = upperDirectionalDerivativeAt f (scalarPoint x) ((-y 0) • scalarPoint (-1)) := by
          symm
          simpa using hpos (scalarPoint (-1)) (-y 0) hyScalePos
        _ = upperDirectionalDerivativeAt f (scalarPoint x) (scalarPoint (y 0)) := by
          rw [← (helperForTheorem_5_24_2_scalarDirection_rewrite (y 0)).2]
        _ = upperDirectionalDerivativeAt f (scalarPoint x) y := by
          rw [hyScalar.symm]
    · have hyNonpos : y 0 ≤ 0 := le_of_not_gt hyPos
      have hyNonneg : 0 ≤ y 0 := le_of_not_gt hyNeg
      have hyZeroVal : y 0 = 0 := le_antisymm hyNonpos hyNonneg
      have hyZero : y = 0 := by
        ext i
        have hi : i = 0 := Subsingleton.elim i 0
        simpa [scalarPoint, hyZeroVal, hi]
      -- The zero direction reduces to the `f'(x; 0) = 0` clause of Theorem 23.1.
      rw [hyZero]
      simp [dotProductEquiv, dotProduct, hzero]

/-- Theorem 5.24.2: under the hypotheses of Theorem 5.24.1, the one-dimensional subdifferential
at `x` is exactly the set of scalars `xStar` such that `f'_-(x) ≤ xStar ≤ f'_+(x)`. -/
theorem oneDimensional_subdifferential_preimage_eq_setOf_leftDerivativeExtension_le_and_le_rightDerivativeExtension
    (f : (Fin 1 → ℝ) → EReal) (hclosed : ClosedConvexFunction f)
    (hproper : ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ)) f) (x : ℝ) :
    {xStar : ℝ | dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) ∈ ∂ f (scalarPoint x)} =
      {xStar : ℝ |
        leftDerivativeExtension f x ≤ ((xStar : ℝ) : EReal) ∧
          (((xStar : ℝ) : EReal) ≤ rightDerivativeExtension f x)} := by
  by_cases hxRight : IsRightOfScalarEffectiveDomain f x
  · have hxNotLeft :
        ¬ IsLeftOfScalarEffectiveDomain f x :=
      helperForTheorem_5_24_1_not_left_of_right f hproper hxRight
    have hxOff :
        scalarPoint x ∉ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
      -- A point strictly right of every scalar domain point cannot itself lie in the domain.
      intro hxMem
      have hxScalar : x ∈ scalarEffectiveDomain f := by
        simpa [scalarEffectiveDomain] using hxMem
      exact (lt_irrefl x) (hxRight x hxScalar)
    have hsubEmpty :
        ∂ f (scalarPoint x) = ∅ := by
      simpa using
        helperForTheorem_23_4_subdifferential_empty_of_not_mem_effectiveDomain
          f hproper (scalarPoint x) hxOff
    ext xStar
    constructor
    · intro hxStar
      -- Route correction: in the off-domain branch, first collapse the subdifferential to `∅`.
      exfalso
      simpa [hsubEmpty] using hxStar
    · intro hxStar
      -- The interval side is also empty because both derivative extensions are `⊤`.
      exfalso
      simpa [leftDerivativeExtension, rightDerivativeExtension, hxRight, hxNotLeft] using hxStar
  · by_cases hxLeft : IsLeftOfScalarEffectiveDomain f x
    · have hxNotRight :
          ¬ IsRightOfScalarEffectiveDomain f x :=
        helperForTheorem_5_24_1_not_right_of_left f hproper hxLeft
      have hxOff :
          scalarPoint x ∉ effectiveDomain (Set.univ : Set (Fin 1 → ℝ)) f := by
        -- A point strictly left of every scalar domain point is also off the effective domain.
        intro hxMem
        have hxScalar : x ∈ scalarEffectiveDomain f := by
          simpa [scalarEffectiveDomain] using hxMem
        exact (lt_irrefl x) (hxLeft x hxScalar)
      have hsubEmpty :
          ∂ f (scalarPoint x) = ∅ := by
        simpa using
          helperForTheorem_23_4_subdifferential_empty_of_not_mem_effectiveDomain
            f hproper (scalarPoint x) hxOff
      ext xStar
      constructor
      · intro hxStar
        -- The subdifferential side is empty once `x` lies strictly left of the domain.
        exfalso
        simpa [hsubEmpty] using hxStar
      · intro hxStar
        -- The interval side is empty because both derivative extensions are `⊥`.
        exfalso
        simpa [leftDerivativeExtension, rightDerivativeExtension, hxLeft, hxNotRight] using hxStar
    · have hxDom :
            x ∈ scalarEffectiveDomain f :=
          helperForTheorem_5_24_1_mem_scalarEffectiveDomain_of_not_left_not_right
            f hproper hxLeft hxRight
      have hf : ConvexFunction f := by
        simpa [ConvexFunction] using hproper.1
      have hxMemUniv : scalarPoint x ∈ (Set.univ : Set (Fin 1 → ℝ)) := by
        simp
      have hxFiniteTop :
          f (scalarPoint x) ≠ (⊤ : EReal) := by
        exact
          mem_effectiveDomain_imp_ne_top (S := (Set.univ : Set (Fin 1 → ℝ))) (f := f) hxDom
      have hxFiniteBot :
          f (scalarPoint x) ≠ (⊥ : EReal) := by
        exact hproper.2.2 (scalarPoint x) hxMemUniv
      have hxFinite :
          f (scalarPoint x) ≠ (⊤ : EReal) ∧ f (scalarPoint x) ≠ (⊥ : EReal) := by
        exact ⟨hxFiniteTop, hxFiniteBot⟩
      ext xStar
      constructor
      · intro hxStar
        -- In the domain regime, apply the directional-derivative minorant criterion at `±1`.
        exact
          helperForTheorem_5_24_2_subgradient_implies_intervalBounds
            f hproper hxDom hxStar
      · intro hxStar
        have hminor :
            ∀ y : Fin 1 → ℝ,
              (((dotProductEquiv ℝ (Fin 1) (scalarPoint xStar) y : ℝ) : EReal) ≤
                upperDirectionalDerivativeAt f (scalarPoint x) y) :=
          helperForTheorem_5_24_2_intervalBounds_imply_directional_minorant
            f hproper hxDom hxStar
        -- The converse implication of Theorem 23.2 packages that minorant back into a subgradient.
        change IsSubgradientAt f (scalarPoint x) (dotProductEquiv ℝ (Fin 1) (scalarPoint xStar))
        exact
          ((subgradient_iff_directionalDerivative_ge_and_closure_eq_subdifferentialSupport
            f hf (scalarPoint x) hxFinite
            (dotProductEquiv ℝ (Fin 1) (scalarPoint xStar))).1).2 hminor


end Section24
end Chap05
