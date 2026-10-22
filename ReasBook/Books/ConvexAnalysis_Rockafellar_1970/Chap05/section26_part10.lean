/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part9

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped Topology ConvexAnalysis Pointwise

-- Proof sketch: apply Theorem 26.3 to convert essential smoothness of `f` into essential strict
-- convexity of `f*`, use Theorem 16.3 to identify `(A f)*` with `f* ∘ A*`, then invoke Theorem
-- 23.9 with the adjoint-range qualification to transfer essential strict convexity to that
-- precomposition, and dualize back with Theorem 26.3.
/-- Corollary 26.3.3: if `f` is a closed proper convex function on `ℝ^n` that is essentially
smooth, `A : ℝ^n → ℝ^m` is onto, and there exists `y* ∈ ℝ^m` with `A* y* ∈ ri (dom f*)`, then
the image function `A f` is essentially smooth. -/
theorem essentiallySmooth_imageUnderLinearMap_of_surjective_and_adjoint_mem_relativeInterior_conjugateEffectiveDomain
    {n m : ℕ} (f : (Fin n → ℝ) → EReal) (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ))
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hf_smooth : IsEssentiallySmooth f)
    (hA : Function.Surjective A)
    (hri :
      ∃ yStar : Fin m → ℝ,
        coordinateAdjointLinearMap A yStar ∈
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f))) :
    IsEssentiallySmooth (imageUnderLinearMap A f) := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := coordinateAdjointLinearMap A
  let g : (Fin m → ℝ) → EReal := fun yStar => fStar (B yStar)
  have hproper : ProperConvexFunctionOn Set.univ f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hconvStar : ConvexFunction fStar :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).2
  have hconjImage : fenchelConjugate m (imageUnderLinearMap A f) = g := by
    have himage :
        imageUnderLinearMap A f =
          (fun y : Fin m → ℝ =>
            sInf
              ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) ''
                {x | (A x : Fin m → ℝ) = y})) := by
      funext y
      have hset :
          {z | ∃ x : Fin n → ℝ, A x = y ∧ z = f x} =
            ((fun x : EuclideanSpace ℝ (Fin n) => f (x : Fin n → ℝ)) ''
              {x | (A x : Fin m → ℝ) = y}) := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hxEuclid : (A (WithLp.toLp 2 x) : Fin m → ℝ) = y := by
            simpa using hx
          have hzVal : f ((WithLp.toLp 2 x : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) = f x := by
            simp
          exact ⟨WithLp.toLp 2 x, hxEuclid, hzVal.symm⟩
        · rintro ⟨x, hx, hxVal⟩
          have hxCoord : A (x : Fin n → ℝ) = y := by
            simpa using hx
          exact ⟨(x : Fin n → ℝ), hxCoord, hxVal.symm⟩
      -- This is just the `imageUnderLinearMap` fiber written in Euclidean-space coordinates.
      simp [imageUnderLinearMap, hset]
    rw [himage]
    simpa [g, fStar, B, coordinateAdjointLinearMap,
      helperForTheorem_23_9_coordinateAdjointMap,
      helperForTheorem_23_9_euclideanLinearLift] using
      (section16_fenchelConjugate_linearImage
        (A := helperForTheorem_23_9_euclideanLinearLift A) (f := f))
  have hg_essStrict : IsEssentiallyStrictlyConvex g :=
    helperForCorollary_26_3_3_essentiallyStrictlyConvex_conjugatePrecomp
      f A hf hf_closed hf_smooth hA hri
  have hg_closed : LowerSemicontinuous g := by
    -- Rewriting `g` as `(A f)*` imports lower semicontinuity from the general conjugate theorem.
    rw [← hconjImage]
    exact (fenchelConjugate_closedConvex (n := m) (f := imageUnderLinearMap A f)).1
  have hg_proper : ProperConvexERealFunction (F := (Fin m → ℝ)) g :=
    helperForLemma_26_2_properConvexERealFunction hg_essStrict.1
  have hg_smoothConj : IsEssentiallySmooth (fenchelConjugate m g) :=
    (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
      (f := g) hg_proper hg_closed).1 hg_essStrict
  rcases hri with ⟨y0, hy0⟩
  have hy0' : B y0 ∈
      euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) := by
    simpa [fStar, B] using hy0
  have hRangeRi : RangeMeetsRelativeInteriorEffectiveDomain B fStar :=
    ⟨B y0, ⟨y0, rfl⟩, hy0'⟩
  have hneBot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
    intro x
    exact hproper.2.2 x (by simp)
  have hbiconj : fenchelConjugate n fStar = f :=
    fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f)
      hf_closed hconv hneBot
  have hconjG :
      fenchelConjugate m g =
        imageUnderLinearMap (coordinateAdjointLinearMap B) (fenchelConjugate n fStar) := by
    -- Apply Theorem 16.3.3 to the precomposition `y* ↦ f*(B y*)`.
    simpa [g, fStar, B] using
      helperForCorollary_26_3_3_fenchelConjugate_coordinateAdjointPrecomp_eq_imageUnderLinearMap
        fStar B hconvStar hRangeRi
  -- Dualizing back identifies `(f* ∘ A*)*` with `A ((f*)*) = A f`.
  simpa [hconjG, hbiconj, B,
    helperForCorollary_26_3_3_coordinateAdjoint_involutive A] using
    (show IsEssentiallySmooth
      (imageUnderLinearMap (coordinateAdjointLinearMap B) (fenchelConjugate n fStar))
      from by
        simpa [hconjG] using hg_smoothConj)

-- Proof sketch: apply Corollary 26.3.2 to the infimal convolution of the indicator of `C` with
-- the power function `x ↦ ‖x‖^p`, identify the resulting formula with the pointwise infimum
-- `inf_{y ∈ C} |x - y|^p`, and then use Corollary 25.5.1 to upgrade differentiability of this
-- convex function to `C¹` regularity.
/-- Helper for Text 26.3.3.1: translating the Euclidean `p`-power kernel preserves the convexity
and `C¹` regularity of `x ↦ ‖x‖^p`. -/
lemma helperForText_26_3_3_1_translatedDistRpow_convex_contDiff
    {n : ℕ} (y : EuclideanSpace ℝ (Fin n)) {p : ℝ} (hp : 1 < p) :
    ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) ∧
      ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) := by
  constructor
  · -- Translate the base convexity of the Euclidean `p`-power norm by the fixed point `y`.
    simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (convexOn_univ_euclidean_norm_rpow (n := n) (p := p) (hp := le_of_lt hp)).translate_right
        (-y)
  · -- The same translation is `C¹`, so the norm-power regularity composes directly.
    have htranslate :
        ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => x - y) := by
      simpa [sub_eq_add_neg] using (contDiff_id.add contDiff_const)
    simpa [dist_eq_norm] using htranslate.norm_rpow hp

/-- Helper for Text 26.3.3.1: once the textbook envelope is known to be convex and differentiable
on `ℝⁿ`, Corollary 25.5.1 upgrades it to `C¹` after transporting along the standard coordinate
equivalence. -/
lemma helperForText_26_3_3_1_contDiffOne_of_convex_differentiable
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_convex : ConvexOn ℝ Set.univ f) (hf_differentiable : Differentiable ℝ f) :
    ContDiff ℝ 1 f := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let fFin : (Fin n → ℝ) → ℝ := fun x => f (e.symm x)
  have hfFin_convex : ConvexOn ℝ Set.univ fFin := by
    -- Precomposing with the linear equivalence `e.symm` transports convexity to the coordinate
    -- model where Corollary 25.5.1 is formulated.
    simpa [fFin, e] using hf_convex.comp_linearMap e.symm.toLinearMap
  have hfFin_differentiable : Differentiable ℝ fFin := by
    -- Differentiability is preserved under the same continuous linear change of coordinates.
    simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
  have hfFin_contDiffOn : ContDiffOn ℝ 1 fFin Set.univ := by
    -- Corollary 25.5.1 applies on the open convex set `Set.univ` in the coordinate model.
    simpa [fFin] using
      (convexOn_contDiffOn_one_of_differentiableOn_open
        (C := Set.univ) (hCopen := isOpen_univ) (hCconv := convex_univ)
        (hf := hfFin_convex) (hdiff := fun x _ => (hfFin_differentiable x).differentiableWithinAt))
  have hfFin_contDiff : ContDiff ℝ 1 fFin := by
    -- On the whole space, `ContDiffOn` is the same as global `ContDiff`.
    simpa [contDiffOn_univ] using hfFin_contDiffOn
  have hback :
      ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => fFin (e x)) := by
    -- Composing back with the forward equivalence returns to the Euclidean textbook coordinates.
    simpa [e] using hfFin_contDiff.comp e.contDiff
  simpa [fFin, e] using hback

/-- Helper for Text 26.3.3.1: the distance-power envelope is convex by taking near-minimizers in
`C`, convex-combining those points, and applying convexity of the kernel `x ↦ ‖x‖^p`. -/
lemma helperForText_26_3_3_1_convex_infDist_rpow
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C)
    {p : ℝ} (hp : 1 < p) :
    let f : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => sInf ((fun y : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) '' C)
    ConvexOn ℝ Set.univ f := by
  dsimp
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  let f : EuclideanSpace ℝ (Fin n) → ℝ :=
    fun x => sInf ((fun y : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) '' C)
  have hApprox :
      ∀ ε > 0, f (a • x + b • y) ≤ a * f x + b * f y + ε := by
    intro ε hε
    obtain ⟨u, huC, hu_lt⟩ :
        ∃ u ∈ C, Real.rpow (dist x u) p < f x + ε := by
      let sx : Set ℝ := ((fun z : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x z) p) '' C)
      have hsx_nonempty : sx.Nonempty := by
        simpa [sx] using
          hC_nonempty.image (fun z : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x z) p)
      have hsx_lt : sInf sx < sInf sx + ε := by
        linarith
      rcases exists_lt_of_csInf_lt hsx_nonempty hsx_lt with ⟨r, hrmem, hlt⟩
      rcases hrmem with ⟨u, huC, rfl⟩
      exact ⟨u, huC, by simpa [f, sx] using hlt⟩
    obtain ⟨v, hvC, hv_lt⟩ :
        ∃ v ∈ C, Real.rpow (dist y v) p < f y + ε := by
      let sy : Set ℝ := ((fun z : EuclideanSpace ℝ (Fin n) => Real.rpow (dist y z) p) '' C)
      have hsy_nonempty : sy.Nonempty := by
        simpa [sy] using
          hC_nonempty.image (fun z : EuclideanSpace ℝ (Fin n) => Real.rpow (dist y z) p)
      have hsy_lt : sInf sy < sInf sy + ε := by
        linarith
      rcases exists_lt_of_csInf_lt hsy_nonempty hsy_lt with ⟨r, hrmem, hlt⟩
      rcases hrmem with ⟨v, hvC, rfl⟩
      exact ⟨v, hvC, by simpa [f, sy] using hlt⟩
    let z : EuclideanSpace ℝ (Fin n) := a • u + b • v
    have hzC : z ∈ C := by
      -- Convexity of `C` supplies an admissible comparison point for the mixed argument.
      exact hC_convex huC hvC ha hb hab
    have hz_upper : f (a • x + b • y) ≤ Real.rpow (dist (a • x + b • y) z) p := by
      -- The point `z` is one candidate in the infimum defining the envelope at the mixed point.
      refine csInf_le ?_ ?_
      · refine ⟨0, ?_⟩
        rintro r ⟨w, hwC, rfl⟩
        exact Real.rpow_nonneg dist_nonneg p
      · exact ⟨z, hzC, rfl⟩
    have hkernel_conv :=
      (helperForText_26_3_3_1_translatedDistRpow_convex_contDiff (n := n) (y := 0) hp).1
    have hkernel :=
      hkernel_conv.2 (show x - u ∈ Set.univ by simp) (show y - v ∈ Set.univ by simp) ha hb hab
    have hdist_conv :
        Real.rpow (dist (a • x + b • y) z) p ≤
          a * Real.rpow (dist x u) p + b * Real.rpow (dist y v) p := by
      -- Rewriting the mixed distance as a norm of an affine combination reduces to kernel convexity.
      have hrewrite :
          a • x + b • y - z = a • (x - u) + b • (y - v) := by
        simp [z, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      simpa [dist_eq_norm, hrewrite, smul_eq_mul] using hkernel
    have hsum_le :
        a * Real.rpow (dist x u) p + b * Real.rpow (dist y v) p ≤
          a * (f x + ε) + b * (f y + ε) := by
      -- The chosen near-minimizers are within `ε` of the two infima, so the weighted sum is too.
      have hau : a * Real.rpow (dist x u) p ≤ a * (f x + ε) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hu_lt) ha
      have hbv : b * Real.rpow (dist y v) p ≤ b * (f y + ε) := by
        exact mul_le_mul_of_nonneg_left (le_of_lt hv_lt) hb
      exact add_le_add hau hbv
    have hscaled_eps : a * (f x + ε) + b * (f y + ε) = a * f x + b * f y + ε := by
      nlinarith [hab]
    exact (hz_upper.trans hdist_conv).trans (by simpa [hscaled_eps] using hsum_le)
  -- Letting `ε → 0` recovers the exact Jensen inequality.
  exact le_of_forall_pos_le_add hApprox

/-- Helper for Text 26.3.3.1: an everywhere-finite `EReal` envelope that is differentiable in
Rockafellar's sense at `x` has an ordinary real Fréchet derivative after taking `.toReal`. -/
lemma helperForText_26_3_3_1_realDifferentiableAt_of_ERealDifferentiableAt_everywhereFinite
    {n : ℕ} {F : (Fin n → ℝ) → EReal}
    (hfinite : ∀ x : Fin n → ℝ, F x ≠ ⊤ ∧ F x ≠ ⊥)
    {x : Fin n → ℝ} (hdiff : ERealDifferentiableAt F x) :
    DifferentiableAt ℝ (fun y => (F y).toReal) x := by
  let g : Fin n → ℝ := erealGradientAt hdiff
  let L : (Fin n → ℝ) →L[ℝ] ℝ :=
    helperForCorollary_25_5_1_dotProductContinuousLinearMap g
  have hwithin :
      ({z | z ≠ x} ∩ effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = ({z | z ≠ x} : Set _) := by
    ext z
    -- Everywhere-finiteness collapses the punctured effective-domain filter to the punctured
    -- neighborhood filter.
    constructor
    · intro hz
      exact hz.1
    · intro hz
      refine ⟨hz, ?_⟩
      rw [effectiveDomain_eq]
      exact ⟨by simp, lt_top_iff_ne_top.mpr (hfinite z).1⟩
  have hERealTendsto :
      Filter.Tendsto (fun z => erealGradientErrorQuotient F x g z) (𝓝[≠] x) (𝓝 0) := by
    -- The `EReal` derivative data already gives the punctured quotient limit.
    simpa [g, hwithin] using (ERealDifferentiableAt.hasERealGradientAt hdiff).2.2
  have hEventuallyEq :
      (fun z => erealGradientErrorQuotient F x g z) =ᶠ[𝓝[≠] x]
        fun z => (((F z).toReal - (F x).toReal - g ⬝ᵥ (z - x)) / ‖z - x‖) := by
    filter_upwards [self_mem_nhdsWithin] with z _
    have hzTop : F z ≠ ⊤ := (hfinite z).1
    have hzBot : F z ≠ ⊥ := (hfinite z).2
    have hxTop : F x ≠ ⊤ := (hfinite x).1
    have hxBot : F x ≠ ⊥ := (hfinite x).2
    have hToRealSub :
        (F z - F x).toReal = (F z).toReal - (F x).toReal := by
      simpa using EReal.toReal_sub hzTop hzBot hxTop hxBot
    -- On finite-valued points, the `EReal` error quotient is the ordinary real one.
    simp [erealGradientErrorQuotient, g, hToRealSub]
  have hRealTendsto :
      Filter.Tendsto
        (fun z => (((F z).toReal - (F x).toReal - g ⬝ᵥ (z - x)) / ‖z - x‖))
        (𝓝[≠] x) (𝓝 0) := by
    exact Filter.Tendsto.congr' hEventuallyEq hERealTendsto
  have hNormPunctured :
      Filter.Tendsto
        (fun z => ‖z - x‖⁻¹ * ‖(F z).toReal - (F x).toReal - L (z - x)‖)
        (𝓝[≠] x) (𝓝 0) := by
    have hNormQuotient :
        Filter.Tendsto
          (fun z =>
            ‖(((F z).toReal - (F x).toReal - g ⬝ᵥ (z - x)) / ‖z - x‖)‖)
          (𝓝[≠] x) (𝓝 0) := by
      simpa using hRealTendsto.norm
    refine Filter.Tendsto.congr' ?_ hNormQuotient
    filter_upwards [self_mem_nhdsWithin] with z hz
    -- Rewriting the norm of the scalar quotient matches the standard Fréchet-derivative criterion.
    have hnormNorm : ‖‖z - x‖‖ = ‖z - x‖ := by
      simp
    rw [norm_div, hnormNorm, div_eq_mul_inv, mul_comm]
    simp [L, g, helperForCorollary_25_5_1_dotProductContinuousLinearMap]
  have hNormAtX :
      ‖x - x‖⁻¹ * ‖(F x).toReal - (F x).toReal - L (x - x)‖ = 0 := by
    -- At the base point, the derivative-test expression vanishes by convention.
    simp [L]
  have hNorm :
      Filter.Tendsto
        (fun z => ‖z - x‖⁻¹ * ‖(F z).toReal - (F x).toReal - L (z - x)‖)
        (𝓝 x) (𝓝 0) := by
    -- A function with punctured-neighborhood limit `0` and value `0` at the center is continuous
    -- there, so the full-neighborhood limit follows.
    have hNormPuncturedAt :
        Filter.Tendsto
          (fun z => ‖z - x‖⁻¹ * ‖(F z).toReal - (F x).toReal - L (z - x)‖)
          (𝓝[≠] x)
          (𝓝 (‖x - x‖⁻¹ * ‖(F x).toReal - (F x).toReal - L (x - x)‖)) := by
      simpa [hNormAtX] using hNormPunctured
    rw [← hNormAtX]
    exact (continuousAt_iff_punctured_nhds).2 hNormPuncturedAt
  have hHasFDeriv :
      HasFDerivAt (fun y => (F y).toReal) L x := by
    exact (hasFDerivAt_iff_tendsto).2 hNorm
  exact hHasFDeriv.differentiableAt

/-- Helper for Text 26.3.3.1: global everywhere-finite `EReal` differentiability yields ordinary
real differentiability after taking `.toReal`. -/
lemma helperForText_26_3_3_1_realDifferentiable_of_ERealDifferentiable_everywhere
    {n : ℕ} {F : (Fin n → ℝ) → EReal}
    (hfinite : ∀ x : Fin n → ℝ, F x ≠ ⊤ ∧ F x ≠ ⊥)
    (hdiff : ∀ x : Fin n → ℝ, ERealDifferentiableAt F x) :
    Differentiable ℝ (fun x => (F x).toReal) := by
  intro x
  -- Pointwise conversion is enough for global differentiability.
  exact
    helperForText_26_3_3_1_realDifferentiableAt_of_ERealDifferentiableAt_everywhereFinite
      hfinite (hdiff x)

/-- Helper for Text 26.3.3.1: transporting a nonempty closed convex Euclidean set through
`WithLp.toLp` preserves the nonemptiness, closedness, and convexity needed for the coordinate
model of Corollary 26.3.2. -/
lemma helperForText_26_3_3_1_withLpPreimage_nonempty_closed_convex
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    let Cfin : Set (Fin n → ℝ) := (WithLp.toLp (p := 2)) ⁻¹' C
    Cfin.Nonempty ∧ IsClosed Cfin ∧ Convex ℝ Cfin := by
  dsimp
  constructor
  · -- A point of `C` yields a point of the preimage after forgetting Euclidean notation.
    rcases hC_nonempty with ⟨x, hxC⟩
    refine ⟨(x : Fin n → ℝ), ?_⟩
    simpa [Section10.toLp_coeFn_eq] using hxC
  constructor
  · -- Closedness transports through the continuous `WithLp.toLp` identification.
    exact hC_closed.preimage
      (PiLp.continuous_toLp (p := (2 : ENNReal)) (β := fun _ : Fin n => ℝ))
  · -- Convexity transports through the affine map underlying the same linear equivalence.
    let e : EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] (Fin n → ℝ) :=
      WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)
    simpa [e] using hC_convex.affine_preimage (e.symm.toAffineEquiv.toAffineMap)

/-- Helper for Text 26.3.3.1: the indicator of the transported set already satisfies the
right-hand properness, closedness, and relative-interior qualification required by
Corollary 26.3.2. -/
lemma helperForText_26_3_3_1_preimageIndicator_qualification
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    let Cfin : Set (Fin n → ℝ) := (WithLp.toLp (p := 2)) ⁻¹' C
    ProperConvexERealFunction (F := (Fin n → ℝ)) (indicatorFunction Cfin) ∧
      LowerSemicontinuous (indicatorFunction Cfin) ∧
        Set.Nonempty
          (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fenchelConjugate n (indicatorFunction Cfin)))) := by
  dsimp
  rcases
      helperForText_26_3_3_1_withLpPreimage_nonempty_closed_convex
        (C := C) hC_nonempty hC_closed hC_convex with
    ⟨hCfin_nonempty, hCfin_closed, hCfin_convex⟩
  have hproperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C)) :=
    properConvexFunctionOn_indicator_of_convex_of_nonempty hCfin_convex hCfin_nonempty
  have hproper :
      ProperConvexERealFunction (F := (Fin n → ℝ)) (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C)) :=
    helperForLemma_26_2_properConvexERealFunction hproperOn
  have hls :
      LowerSemicontinuous (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C)) := by
    -- Closedness of the set makes the indicator lower semicontinuous by closed-sublevel
    -- inspection.
    refine
      (lowerSemicontinuous_iff_closed_sublevel
        (f := indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C))).2 ?_
    intro α
    by_cases hα : (0 : ℝ) ≤ α
    · have hset :
          {x : Fin n → ℝ |
              indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C) x ≤ (α : EReal)} =
            ((WithLp.toLp (p := 2)) ⁻¹' C) := by
        ext x
        by_cases hx : x ∈ ((WithLp.toLp (p := 2)) ⁻¹' C)
        · have hxC : WithLp.toLp (p := 2) x ∈ C := hx
          have hαE : ((0 : EReal) ≤ (α : EReal)) := by
            exact_mod_cast hα
          simp [indicatorFunction, hxC, hαE]
        · have hxC : WithLp.toLp (p := 2) x ∉ C := hx
          simp [indicatorFunction, hxC]
      simpa [hset] using hCfin_closed
    · have hset :
          {x : Fin n → ℝ |
              indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C) x ≤ (α : EReal)} =
            (∅ : Set (Fin n → ℝ)) := by
        ext x
        by_cases hx : x ∈ ((WithLp.toLp (p := 2)) ⁻¹' C)
        · have hαE : ¬ ((0 : EReal) ≤ (α : EReal)) := by
            exact_mod_cast hα
          have hxC : WithLp.toLp (p := 2) x ∈ C := hx
          simp [indicatorFunction, hxC, hαE]
        · have hxC : WithLp.toLp (p := 2) x ∉ C := hx
          simp [indicatorFunction, hxC]
      simpa [hset] using isClosed_empty
  have hconj :
      fenchelConjugate n (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C)) =
        supportFunctionEReal ((WithLp.toLp (p := 2)) ⁻¹' C) := by
    exact
      (indicatorFunction_conjugate_supportFunctionEReal_of_isClosed
        (n := n) (((WithLp.toLp (p := 2)) ⁻¹' C)) hCfin_convex hCfin_closed).1
  have hsupp_conv :
      ConvexFunction (supportFunctionEReal ((WithLp.toLp (p := 2)) ⁻¹' C)) :=
    (section13_supportFunctionEReal_closedProperConvex_posHom
      (n := n) (C := ((WithLp.toLp (p := 2)) ⁻¹' C)) hCfin_nonempty hCfin_convex).1.1
  have hdom_nonempty :
      (effectiveDomain (Set.univ : Set (Fin n → ℝ))
        (fenchelConjugate n (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C)))).Nonempty := by
    -- The support function is finite at `0`, so the conjugate effective domain is nonempty.
    refine ⟨0, ?_⟩
    rw [hconj, effectiveDomain_eq]
    refine ⟨by simp, ?_⟩
    rw [lt_top_iff_ne_top]
    rw [helperForCorollary_20_2_1_supportFunctionEReal_zero_of_nonempty hCfin_nonempty]
    norm_num
  have hdom_conv :
      Convex ℝ
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fenchelConjugate n (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C)))) := by
    -- Effective domains of convex functions are convex, and the conjugate here is the support
    -- function of the transported set.
    rw [hconj]
    exact effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ)))
      (f := supportFunctionEReal ((WithLp.toLp (p := 2)) ⁻¹' C)) hsupp_conv
  have hri_nonempty :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (fenchelConjugate n (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C))))) := by
    -- Any nonempty convex effective domain in finite dimensions has nonempty relative interior.
    simpa using
      helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty
        (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fenchelConjugate n (indicatorFunction ((WithLp.toLp (p := 2)) ⁻¹' C))))
        hdom_conv hdom_nonempty
  exact ⟨hproper, hls, hri_nonempty⟩

/-- Helper for Text 26.3.3.1: the scaled Euclidean `p`-power kernel on `Fin n → ℝ` is a closed
proper convex `EReal` function and is differentiable everywhere in Rockafellar's `EReal` sense. -/
lemma helperForText_26_3_3_1_scaledEuclideanNormRpow_closedProper_and_eRealDifferentiable
    {n : ℕ} {p : ℝ} (hp : 1 < p) :
    let g : (Fin n → ℝ) → EReal :=
      fun x => (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) : ℝ)) : EReal)
    ProperConvexERealFunction (F := (Fin n → ℝ)) g ∧
      LowerSemicontinuous g ∧
        ∀ x : Fin n → ℝ, ERealDifferentiableAt g x := by
  intro g
  let f : EuclideanSpace ℝ (Fin n) → ℝ := fun x => (1 / p) * Real.rpow (dist x 0) p
  have hbase_conv : ConvexOn ℝ Set.univ (fun x : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x 0) p) :=
    (helperForText_26_3_3_1_translatedDistRpow_convex_contDiff (n := n) (y := 0) hp).1
  have hp_inv_nonneg : 0 ≤ 1 / p := by
    have hp_pos : 0 < p := by linarith
    exact le_of_lt (one_div_pos.mpr hp_pos)
  have hf_conv : ConvexOn ℝ Set.univ f := by
    -- The Euclidean `p`-power kernel stays convex after the scalar normalization by `1 / p`.
    simpa [f, mul_comm, mul_left_comm, mul_assoc] using
      (ConvexOn.smul hp_inv_nonneg hbase_conv)
  have hproper :
      ProperConvexERealFunction (F := (Fin n → ℝ))
        (fun x => (f (WithLp.toLp (p := 2) x) : EReal)) := by
    -- Section 10 transports convexity from Euclidean coordinates to `Fin n → ℝ`.
    exact
      helperForLemma_26_2_properConvexERealFunction
        (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn (n := n) (f := f) hf_conv)
  have hclosed :
      LowerSemicontinuous (fun x : Fin n → ℝ => (f (WithLp.toLp (p := 2) x) : EReal)) := by
    -- The same transport also packages lower semicontinuity.
    exact (Section10.closedConvexFunction_coe_comp_toLp_of_convexOn (n := n) (f := f) hf_conv).2
  have hdiff :
      ∀ x : Fin n → ℝ, ERealDifferentiableAt (fun x => (f (WithLp.toLp (p := 2) x) : EReal)) x := by
    intro x
    have hbase_cont : ContDiff ℝ 1 (fun x : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x 0) p) :=
      (helperForText_26_3_3_1_translatedDistRpow_convex_contDiff (n := n) (y := 0) hp).2
    have hf_contDiff : ContDiff ℝ 1 f := by
      -- The translated kernel is `C¹`, and the scalar normalization does not change that.
      simpa [f, mul_comm, mul_left_comm, mul_assoc] using
        (ContDiff.const_smul (1 / p) hbase_cont)
    have hf_diff :
        Differentiable ℝ (fun x : Fin n → ℝ => f (WithLp.toLp (p := 2) x)) := by
      -- Composing with the `WithLp` linear equivalence preserves differentiability.
      simpa using
        hf_contDiff.differentiable le_rfl |>.comp
          ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)).symm.toContinuousLinearEquiv.differentiable)
    have hExt :
        ∃ hDiffExt :
          ERealDifferentiableAt
            (fun y : Fin n → ℝ => ((f (WithLp.toLp (p := 2) y) : ℝ) : EReal) +
              indicatorFunction (Set.univ : Set (Fin n → ℝ)) y) x,
            erealGradientAt hDiffExt =
              euclideanGradientAt (fun y : Fin n → ℝ => f (WithLp.toLp (p := 2) y)) x := by
      exact
        helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
          (hCopen := isOpen_univ) (f := fun y : Fin n → ℝ => f (WithLp.toLp (p := 2) y))
          (x := x) (by simp) (hf_diff x)
    rcases hExt with ⟨hDiffExt, _⟩
    simpa [indicatorFunction] using hDiffExt
  refine ⟨?_, ?_, ?_⟩
  · simpa [g, f] using hproper
  · simpa [g, f] using hclosed
  · intro x
    simpa [g, f] using hdiff x

/-- Helper for Text 26.3.3.1: the scaled Euclidean `p`-power kernel is essentially smooth, and
its Fenchel conjugate is finite on all of `ℝⁿ`. -/
lemma helperForText_26_3_3_1_scaledEuclideanNormRpow_essentiallySmooth_and_conjugateDomain_univ
    {n : ℕ} {p : ℝ} (hp : 1 < p) :
    let q : ℝ := p / (p - 1)
    let g : (Fin n → ℝ) → EReal :=
      fun x => (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) : ℝ)) : EReal)
    IsEssentiallySmooth g ∧
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g) = Set.univ := by
  intro q g
  rcases
      helperForText_26_3_3_1_scaledEuclideanNormRpow_closedProper_and_eRealDifferentiable
        (n := n) (p := p) hp with
    ⟨hg_proper, hg_closed, hg_diff⟩
  have hg_properOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g :=
    helperForTheorem_25_6_properConvexFunctionOn (f := g) hg_proper
  have hg_conv : ConvexFunction g := by
    simpa [ConvexFunction] using hg_properOn.1
  have hsingle : IsSingleValuedMultivaluedMap (subdifferentialAt g) := by
    intro x u hu v hv
    let uVec : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm u
    let vVec : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm v
    have huVec : uVec ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x) := by
      simpa [uVec] using hu
    have hvVec : vVec ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt g x) := by
      simpa [vVec] using hv
    have huEq : uVec = erealGradientAt (hg_diff x) :=
      helperForTheorem_25_5_subgradientPreimage_eq_gradient
        (f := g) hg_conv (x := x) (hg_diff x) huVec
    have hvEq : vVec = erealGradientAt (hg_diff x) :=
      helperForTheorem_25_5_subgradientPreimage_eq_gradient
        (f := g) hg_conv (x := x) (hg_diff x) hvVec
    have hEqDual :
        dotProductEquiv ℝ (Fin n) uVec = dotProductEquiv ℝ (Fin n) vVec := by
      rw [huEq, hvEq]
    simpa [uVec, vVec] using hEqDual
  have hg_smooth : IsEssentiallySmooth g :=
    (subdifferential_singleValued_iff_essentiallySmooth (f := g) hg_proper hg_closed).1.1 hsingle
  have hpq : p.HolderConjugate q := by
    -- Rewrite the textbook conjugate exponent relation in Mathlib's `HolderConjugate` form.
    refine (Real.holderConjugate_iff).2 ?_
    dsimp [q]
    constructor
    · linarith
    · field_simp
      ring
  have hterm_le :
      ∀ xStar x : Fin n → ℝ,
        (((x ⬝ᵥ xStar : ℝ) : EReal) - g x) ≤
          (((((1 / q) * Real.rpow (l1Norm xStar) q) : ℝ)) : EReal) := by
    intro xStar x
    have hl1_nonneg : 0 ≤ l1Norm xStar := by
      exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    have hxnorm : ‖x‖ ≤ dist (WithLp.toLp (p := 2) x) 0 := by
      -- The sup norm on `Fin n → ℝ` is bounded by the Euclidean norm transported through `WithLp`.
      calc
        ‖x‖ ≤ Real.sqrt (x ⬝ᵥ x) :=
          (supNorm_le_piEuclideanNorm_and_piEuclideanNorm_le_sqrt_n_mul_supNorm (n := n) x).1
        _ = dist (WithLp.toLp (p := 2) x) 0 := by
          rw [dotProduct, dist_eq_norm, PiLp.norm_eq_of_L2]
          simp [pow_two]
    have hdot :
        x ⬝ᵥ xStar ≤ l1Norm xStar * dist (WithLp.toLp (p := 2) x) 0 := by
      calc
        x ⬝ᵥ xStar = xStar ⬝ᵥ x := by rw [dotProduct_comm]
        _ ≤ l1Norm xStar * ‖x‖ :=
          section13_dotProduct_le_l1Norm_mul_norm (n := n) xStar x
        _ ≤ l1Norm xStar * dist (WithLp.toLp (p := 2) x) 0 := by
          gcongr
    have hyoung :
        dist (WithLp.toLp (p := 2) x) 0 * l1Norm xStar ≤
          Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p / p +
            Real.rpow (l1Norm xStar) q / q :=
      Real.young_inequality_of_nonneg
        (a := dist (WithLp.toLp (p := 2) x) 0) (b := l1Norm xStar)
        dist_nonneg hl1_nonneg hpq
    have hsum :
        x ⬝ᵥ xStar ≤
          ((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) +
            ((1 / q) * Real.rpow (l1Norm xStar) q) := by
      have hyoung' :
          l1Norm xStar * dist (WithLp.toLp (p := 2) x) 0 ≤
            ((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) +
              ((1 / q) * Real.rpow (l1Norm xStar) q) := by
        simpa [mul_comm, div_eq_mul_inv, one_div, mul_left_comm, mul_assoc, add_comm,
          add_left_comm, add_assoc] using hyoung
      exact le_trans hdot hyoung'
    have hsumE :
        (((x ⬝ᵥ xStar : ℝ)) : EReal) ≤
          (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) +
              ((1 / q) * Real.rpow (l1Norm xStar) q) : ℝ)) : EReal) := by
      exact_mod_cast hsum
    rw [EReal.sub_le_iff_le_add]
    · simpa [g, add_comm, add_left_comm, add_assoc] using hsumE
    · left
      simpa [g] using
        (EReal.coe_ne_bot ((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p))
    · left
      simpa [g] using
        (EReal.coe_ne_top ((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p))
  have hdom :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g) = Set.univ := by
    ext x
    rw [effectiveDomain_eq]
    constructor
    · intro _
      simp
    · intro _
      constructor
      · simp
      · rw [lt_top_iff_ne_top, fenchelConjugate_eq_iSup]
        -- The Fenchel range terms admit a uniform Young-type upper bound, so their `iSup` is finite.
        exact ne_of_lt (lt_of_le_of_lt (iSup_le (fun y => hterm_le x y)) (EReal.coe_lt_top _))
  exact ⟨hg_smooth, hdom⟩

/-- Helper for Text 26.3.3.1: the shifted Euclidean `p`-power kernel in the `WithLp` coordinate
model is exactly the scaled real distance-power expression from the textbook. -/
lemma helperForText_26_3_3_1_scaledEuclideanNormRpow_kernel_eq
    {n : ℕ} {p : ℝ} (hp : 1 < p) :
    let g : (Fin n → ℝ) → EReal :=
      fun x => (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) : ℝ)) : EReal)
    ∀ x z : Fin n → ℝ,
      g (x - z) =
        (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) (WithLp.toLp (p := 2) z)) p) :
            ℝ)) : EReal) := by
  intro g x z
  -- The `WithLp` map turns subtraction in coordinates into the Euclidean distance between the two
  -- corresponding textbook points.
  simp [g, dist_eq_norm, PiLp.norm_eq_of_L2, pow_two]

/-- Helper for Text 26.3.3.1: the `WithLp` infimal convolution with the indicator of the
transported set is exactly the scaled textbook envelope. -/
lemma helperForText_26_3_3_1_withLpEnvelope_eq_scaledInfimalConvolution
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC_nonempty : C.Nonempty)
    {p : ℝ} (hp : 1 < p) :
    let Cfin : Set (Fin n → ℝ) := (WithLp.toLp (p := 2)) ⁻¹' C
    let g : (Fin n → ℝ) → EReal :=
      fun x => (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) : ℝ)) : EReal)
    ∀ x : Fin n → ℝ,
      infimalConvolution g (indicatorFunction Cfin) x =
        (((((1 / p) *
            sInf
              ((fun y : EuclideanSpace ℝ (Fin n) =>
                  Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)) :
            ℝ)) : EReal) := by
  intro Cfin g x
  set S : Set EReal :=
    {r : EReal | ∃ z : Fin n → ℝ, r = indicatorFunction Cfin z + g (x - z)}
  have hS :
      infimalConvolution g (indicatorFunction Cfin) x = sInf S := by
    -- Start from the parameter form of infimal convolution and swap the summands into the kernel
    -- plus indicator order used below.
    simp [S, infimalConvolution_eq_sInf_param]
  have hsubset1 :
      Set.range (fun z : Cfin => g (x - z)) ⊆ S := by
    intro r hr
    rcases hr with ⟨z, rfl⟩
    refine ⟨z, ?_⟩
    simp [indicatorFunction, z.property]
  have hsubset2 :
      S ⊆ insert ⊤ (Set.range (fun z : Cfin => g (x - z))) := by
    intro r hr
    rcases hr with ⟨z, rfl⟩
    by_cases hz : z ∈ Cfin
    · right
      refine ⟨⟨z, hz⟩, ?_⟩
      simp [indicatorFunction, hz]
    · left
      have hg_ne_bot : g (x - z) ≠ ⊥ := by
        simpa [g] using
          (EReal.coe_ne_bot ((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) (x - z)) 0) p))
      simpa [indicatorFunction, hz] using (EReal.top_add_of_ne_bot hg_ne_bot)
  have hEqRange :
      Set.range (fun z : Cfin => g (x - z)) =
        Set.range
          (fun y : C =>
            (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) : ℝ)) : EReal)) := by
    ext r
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨⟨WithLp.toLp (p := 2) z, z.property⟩, ?_⟩
      -- The kernel rewrite isolates the exact distance expression seen in the textbook formula.
      simpa [g] using
        helperForText_26_3_3_1_scaledEuclideanNormRpow_kernel_eq
          (n := n) (p := p) hp x z
    · rintro ⟨y, rfl⟩
      refine ⟨⟨(y : Fin n → ℝ), ?_⟩, ?_⟩
      · simpa [Cfin, Section10.toLp_coeFn_eq] using y.property
      · simpa [g, Section10.toLp_coeFn_eq] using
          helperForText_26_3_3_1_scaledEuclideanNormRpow_kernel_eq
            (n := n) (p := p) hp x (y : Fin n → ℝ)
  let T : Set ℝ :=
    (fun y : EuclideanSpace ℝ (Fin n) =>
      Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C
  have hT_nonempty : T.Nonempty := by
    rcases hC_nonempty with ⟨y, hy⟩
    exact ⟨Real.rpow (dist (WithLp.toLp (p := 2) x) y) p, ⟨y, hy, rfl⟩⟩
  have hT_bddBelow : BddBelow T := by
    refine ⟨0, ?_⟩
    intro r hr
    rcases hr with ⟨y, hy, rfl⟩
    exact Real.rpow_nonneg dist_nonneg _
  have hScaleImage :
      ((fun y : EuclideanSpace ℝ (Fin n) =>
          (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) : ℝ)) : EReal)) '' C) =
        (fun μ : ℝ => (μ : EReal)) '' ((1 / p) • T) := by
    ext r
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨(1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p, ?_, rfl⟩
      exact ⟨Real.rpow (dist (WithLp.toLp (p := 2) x) y) p, ⟨y, hy, rfl⟩, by simp [smul_eq_mul]⟩
    · rintro ⟨μ, hμ, rfl⟩
      rcases hμ with ⟨t, ht, hμeq⟩
      rcases ht with ⟨y, hy, rfl⟩
      subst μ
      refine ⟨y, hy, ?_⟩
      simp [smul_eq_mul]
  have hp_inv_pos : 0 < 1 / p := by
    have hp_pos : 0 < p := by linarith
    exact one_div_pos.mpr hp_pos
  have hT_coe :
      sInf ((fun μ : ℝ => (μ : EReal)) '' T) = ((sInf T : ℝ) : EReal) :=
    sInf_coe_image_eq_sInf_real (A := T) hT_nonempty hT_bddBelow
  have hEqImage :
      Set.range
          (fun y : C =>
            (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) : ℝ)) : EReal)) =
        ((fun y : EuclideanSpace ℝ (Fin n) =>
            (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) : ℝ)) : EReal)) '' C) := by
    ext r
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.property, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  calc
    infimalConvolution g (indicatorFunction Cfin) x = sInf S := hS
    _ = sInf (Set.range (fun z : Cfin => g (x - z))) := by
      -- Points outside `Cfin` contribute `⊤`, so only the range over `Cfin` affects the infimum.
      exact le_antisymm (sInf_le_sInf hsubset1) (sInf_le_sInf_of_subset_insert_top hsubset2)
    _ =
        sInf
          (Set.range
            (fun y : C =>
              (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) : ℝ)) : EReal))) := by
      rw [hEqRange]
    _ =
        sInf
          ((fun y : EuclideanSpace ℝ (Fin n) =>
              (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) : ℝ)) : EReal)) '' C) := by
      rw [hEqImage]
    _ =
        sInf ((fun μ : ℝ => (μ : EReal)) '' ((1 / p) • T)) := by
      rw [hScaleImage]
    _ = (((1 / p : ℝ) : EReal) * sInf ((fun μ : ℝ => (μ : EReal)) '' T)) := by
      simpa [smul_eq_mul] using (sInf_image_real_smul (S := T) (t := 1 / p) hp_inv_pos)
    _ = (((((1 / p) * sInf T) : ℝ)) : EReal) := by
      rw [hT_coe]
      simp [EReal.coe_mul]
    _ =
        (((((1 / p) *
            sInf
              ((fun y : EuclideanSpace ℝ (Fin n) =>
                  Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)) :
            ℝ)) : EReal) := by
      simp [T]

/-- Helper for Text 26.3.3.1: Corollary 26.3.2 makes the `WithLp`-coordinate envelope
differentiable, and converting back from `EReal` gives an ordinary real derivative everywhere. -/
lemma helperForText_26_3_3_1_withLpEnvelope_differentiable
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {p : ℝ} (hp : 1 < p) :
    let fFin : (Fin n → ℝ) → ℝ :=
      fun x =>
        sInf
          ((fun y : EuclideanSpace ℝ (Fin n) =>
              Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)
    Differentiable ℝ fFin := by
  intro fFin
  let Cfin : Set (Fin n → ℝ) := (WithLp.toLp (p := 2)) ⁻¹' C
  let g : (Fin n → ℝ) → EReal :=
    fun x => (((((1 / p) * Real.rpow (dist (WithLp.toLp (p := 2) x) 0) p) : ℝ)) : EReal)
  rcases
      helperForText_26_3_3_1_scaledEuclideanNormRpow_closedProper_and_eRealDifferentiable
        (n := n) (p := p) hp with
    ⟨hg_proper, hg_closed, _⟩
  rcases
      helperForText_26_3_3_1_scaledEuclideanNormRpow_essentiallySmooth_and_conjugateDomain_univ
        (n := n) (p := p) hp with
    ⟨hg_smooth, hg_domUniv⟩
  rcases
      helperForText_26_3_3_1_preimageIndicator_qualification
        (C := C) hC_nonempty hC_closed hC_convex with
    ⟨hInd_proper, hInd_closed, hInd_ri⟩
  have hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n g)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ))
              (fenchelConjugate n (indicatorFunction Cfin)))) := by
    rcases hInd_ri with ⟨x, hx⟩
    -- The left conjugate domain is all of `ℝⁿ`, so the qualification reduces to the indicator
    -- witness already proved above.
    refine ⟨x, ?_, hx⟩
    have hx_univ : x ∈ euclideanRelativeInterior_fin n (Set.univ : Set (Fin n → ℝ)) := by
      exact helperForTheorem_23_4_mem_relativeInterior_of_mem_interior (by simp)
    rw [hg_domUniv]
    exact hx_univ
  let F : (Fin n → ℝ) → EReal := infimalConvolution g (indicatorFunction Cfin)
  have hFsmooth : IsEssentiallySmooth F := by
    -- Corollary 26.3.2 applies exactly to the left kernel and the transported indicator.
    simpa [F] using
      essentiallySmooth_infimalConvolution_of_essentiallySmooth_left_and_commonRelativeInterior_conjugateEffectiveDomain
        (f₁ := g) (f₂ := indicatorFunction Cfin) hg_proper hg_closed hInd_proper hInd_closed hg_smooth hri
  rcases hFsmooth with ⟨hFproperOn, _, grad, hgradMem, hgradUnique, _⟩
  have hFconv : ConvexFunction F := by
    simpa [ConvexFunction] using hFproperOn.1
  have hdomF :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ := by
    ext x
    rw [effectiveDomain_eq]
    constructor
    · intro _
      simp
    · intro _
      have hxEq :=
        helperForText_26_3_3_1_withLpEnvelope_eq_scaledInfimalConvolution
          (C := C) hC_nonempty (p := p) hp x
      constructor
      · simp
      · have hFx :
            F x =
              (((((1 / p) *
                  sInf
                    ((fun y : EuclideanSpace ℝ (Fin n) =>
                        Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)) :
                  ℝ)) : EReal) := by
            simpa [F, g, Cfin] using hxEq
        rw [lt_top_iff_ne_top]
        simpa [hFx] using
          (EReal.coe_ne_top
            ((1 / p) *
              sInf
                ((fun y : EuclideanSpace ℝ (Fin n) =>
                    Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)))
  have hFint :
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) = Set.univ := by
    simpa [hdomF]
  have hFfinite : ∀ x : Fin n → ℝ, F x ≠ ⊤ ∧ F x ≠ ⊥ := by
    intro x
    have hxEq :=
      helperForText_26_3_3_1_withLpEnvelope_eq_scaledInfimalConvolution
        (C := C) hC_nonempty (p := p) hp x
    have hFx :
        F x =
          (((((1 / p) *
              sInf
                ((fun y : EuclideanSpace ℝ (Fin n) =>
                    Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)) :
              ℝ)) : EReal) := by
      simpa [F, g, Cfin] using hxEq
    constructor
    · simpa [hFx] using
        (EReal.coe_ne_top
          ((1 / p) *
            sInf
              ((fun y : EuclideanSpace ℝ (Fin n) =>
                  Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)))
    · simpa [hFx] using
        (EReal.coe_ne_bot
          ((1 / p) *
            sInf
              ((fun y : EuclideanSpace ℝ (Fin n) =>
                  Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)))
  have hEdiff : ∀ x : Fin n → ℝ, ERealDifferentiableAt F x := by
    intro x
    have hxInterior : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) := by
      simpa [hFint]
    have hxFinite : F x ≠ ⊤ ∧ F x ≠ ⊥ := hFfinite x
    -- The essential-smoothness gradient witness gives the unique subgradient at every point,
    -- because the effective-domain interior is all of `ℝⁿ`.
    refine (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient F hFconv x hxFinite).2 ?_
    refine ⟨grad x, ?_, ?_⟩
    · simpa [hFint] using hgradMem x hxInterior
    · intro y hy
      exact hgradUnique hxInterior (by simpa using hy)
  have hrealDiff :
      Differentiable ℝ (fun x => (F x).toReal) :=
    helperForText_26_3_3_1_realDifferentiable_of_ERealDifferentiable_everywhere hFfinite hEdiff
  have hp_ne : p ≠ 0 := by
    linarith
  have htoRealEq : (fun x => (F x).toReal) = fun x => (1 / p) * fFin x := by
    funext x
    have hxEq :=
      helperForText_26_3_3_1_withLpEnvelope_eq_scaledInfimalConvolution
        (C := C) hC_nonempty (p := p) hp x
    have hFx :
        F x =
          (((((1 / p) *
              sInf
                ((fun y : EuclideanSpace ℝ (Fin n) =>
                    Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)) :
              ℝ)) : EReal) := by
      simpa [F, g, Cfin] using hxEq
    rw [hFx]
    simpa [fFin, EReal.toReal_mul]
  have hscaled :
      Differentiable ℝ (fun x => (1 / p) * fFin x) := by
    -- The infimal-convolution rewrite makes the `EReal` envelope equal to the scaled real one.
    rw [← htoRealEq]
    exact hrealDiff
  have hunscaled :
      Differentiable ℝ (fun x => p * ((1 / p) * fFin x)) := by
    intro x
    exact (hscaled x).const_mul p
  -- The infimal-convolution identity is already real-valued, so `.toReal` removes only the
  -- harmless coercion.
  simpa [fFin, hp_ne, mul_assoc] using hunscaled

/-- Helper for Text 26.3.3.1: the differentiability step should come from Corollary 26.3.2 after
transporting the Euclidean set `C` to the coordinate model `Fin n → ℝ` and rewriting the
infimal convolution back to the textbook envelope. -/
lemma helperForText_26_3_3_1_differentiable_infDist_rpow
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {p : ℝ} (hp : 1 < p) :
    let f : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => sInf ((fun y : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) '' C)
    Differentiable ℝ f := by
  -- Route correction: the naive transport through `EuclideanSpace.equiv (Fin n) ℝ` changes the
  -- norm to the sup norm, so the differentiability step must go through the `WithLp` model.
  intro f
  let fFin : (Fin n → ℝ) → ℝ :=
    fun x =>
      sInf
        ((fun y : EuclideanSpace ℝ (Fin n) =>
            Real.rpow (dist (WithLp.toLp (p := 2) x) y) p) '' C)
  have hfFin :
      Differentiable ℝ fFin := by
    -- The coordinate-model envelope is differentiable by the previous Corollary 26.3.2 package.
    simpa [fFin] using
      helperForText_26_3_3_1_withLpEnvelope_differentiable
        (C := C) hC_nonempty hC_closed hC_convex hp
  have hcomp :
      Differentiable ℝ (fun x : EuclideanSpace ℝ (Fin n) => fFin (x : Fin n → ℝ)) := by
    -- Composing with the `WithLp` linear equivalence returns to the Euclidean textbook variable.
    simpa [fFin] using
      hfFin.comp ((WithLp.linearEquiv (2 : ENNReal) ℝ (Fin n → ℝ)).toContinuousLinearEquiv.differentiable)
  simpa [f, fFin, Section10.toLp_coeFn_eq] using hcomp

/-- Helper for Text 26.3.3.1: the convexity and differentiability of the distance-power envelope
should follow from Corollary 26.3.2 applied in the coordinate model and then transported back to
the Euclidean textbook function. -/
lemma helperForText_26_3_3_1_convex_differentiable_core
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n)))
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)
    {p : ℝ} (hp : 1 < p) :
    let f : EuclideanSpace ℝ (Fin n) → ℝ :=
      fun x => sInf ((fun y : EuclideanSpace ℝ (Fin n) => Real.rpow (dist x y) p) '' C)
    ConvexOn ℝ Set.univ f ∧ Differentiable ℝ f := by
  dsimp
  constructor
  · -- The convexity part can be proved directly from approximate minimizers inside `C`.
    exact helperForText_26_3_3_1_convex_infDist_rpow (C := C) hC_nonempty hC_convex hp
  · -- The differentiability part remains the coordinate-model Corollary 26.3.2 step.
    exact
      helperForText_26_3_3_1_differentiable_infDist_rpow
        (C := C) hC_nonempty hC_closed hC_convex hp

end Section26
end Chap05
