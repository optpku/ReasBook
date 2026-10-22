/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part18

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- Helper for Theorem 26.6: the dual whole-space Legendre package transfers to the real-valued
branch `x* ↦ (f*(x*)).toReal`, keeping strict convexity, differentiability, co-finiteness, and a
pointwise `EReal` gradient witness for the prescribed selector. -/
lemma helperForTheorem_26_6_dualRealBranch_properties_from_wholeSpacePackage
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hbij : Function.Bijective (gradient f))
    (gradStar : (Fin n → ℝ) → (Fin n → ℝ))
    (hRightInv :
      ∀ xStar : Fin n → ℝ,
        let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
        euclideanGradientAt fFin (gradStar xStar) = xStar) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    let fStar : (Fin n → ℝ) → ℝ := fun xStar => (fenchelConjugate n F xStar).toReal
    Differentiable ℝ fStar ∧
      StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fStar ∧
        IsCofiniteFiniteConvexFunction fStar ∧
          ((fun xStar : Fin n → ℝ => (fStar xStar : EReal)) = fenchelConjugate n F) ∧
            (∀ xStar : Fin n → ℝ,
              ∃ hDiff : ERealDifferentiableAt (fenchelConjugate n F) xStar,
                erealGradientAt hDiff = gradStar xStar) := by
  intro fFin F fStar
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ x : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F x,
          erealGradientAt hDiff = euclideanGradientAt fFin x) ∧
        IsEssentiallySmooth F := by
    -- Reuse the primal whole-space lift package before passing to the dual branch.
    simpa [fFin, F] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with
    ⟨hproper, hclosed, hdom, hgradWitness, _hsmooth⟩
  choose hdiffAll hgradEq using hgradWitness
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hclosedConv : ClosedConvexFunction F := ⟨hconv, hclosed⟩
  have hproperStarOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
    proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn
  have hproperStar :
      ProperConvexERealFunction (F := (Fin n → ℝ)) (fenchelConjugate n F) :=
    helperForLemma_26_2_properConvexERealFunction hproperStarOn
  have hclosedStar : LowerSemicontinuous (fenchelConjugate n F) := by
    simpa using (fenchelConjugate_closedConvex (n := n) (f := F)).1
  have hconvStar : ConvexFunction (fenchelConjugate n F) := by
    simpa [ConvexFunction] using hproperStarOn.1
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Convexity again transports through the Euclidean-coordinate identification.
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hcofiniteData :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ ∧
        ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
    -- The primal equivalence already turns surjectivity of the gradient into co-finiteness.
    have hprimal :=
      helperForTheorem_26_6_bijective_iff_strictConvex_and_cofinite
        (f := f) hf_convex hf_differentiable
    have hcofinite : IsCofiniteFiniteConvexFunction fFin := hprimal.1 hbij |>.2
    exact
      (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
        (f := fFin) hfFin_convex).1 hcofinite
  have hInjectiveSubdiff :
      IsOneToOneMultivaluedMap (subdifferentialAt F) := by
    -- Gradient injectivity is the one-to-one subdifferential hypothesis needed by Theorem 26.5.
    exact
      (helperForTheorem_26_6_gradientInjective_iff_subdifferentialOneToOne
        (f := f) hf_convex hf_differentiable).1 hbij.1
  have hLegendreInterior :
      IsLegendreTypeOn
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F := by
    -- Proposition 26.4.1.5 upgrades the subdifferential hypothesis to Legendre type.
    exact
      (subdifferential_oneToOne_iff_restriction_isLegendreTypeOn_interior
        (f := F) hproper hclosed).1 hInjectiveSubdiff
  have hLegendrePackageRaw :=
    legendreTypeOn_interior_iff_conjugate_legendreTypeOn_interior_with_mutualLegendreConjugacy
      (f := F) hproper hclosed
  have hLegStar :
      IsLegendreTypeOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) := by
    -- The whole-space domain hypotheses collapse both interior effective domains to `univ`.
    have hLegStarRaw :=
      hLegendrePackageRaw.1.1
        (show
          IsLegendreTypeOn
            (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F from by
            simpa [hdom] using hLegendreInterior)
    simpa [hdom, hcofiniteData.1] using hLegStarRaw
  have hLegendrePackage :=
    hLegendrePackageRaw.2
      (show
        IsLegendreTypeOn
          (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F from by
          simpa [hdom] using hLegendreInterior)
  rcases hLegendrePackage with
    ⟨L, hLtarget, _hLconj, LStar, _hLStarTarget, _hLStarConj,
      grad, gradStarLeg, hLfun, _hLStarFun, hGradMem, hGradUnique,
      hGradStarMem, hGradStarUnique, _hHomeomorphPkg⟩
  have hGradEq :
      ∀ x : Fin n → ℝ, grad x = euclideanGradientAt fFin x := by
    intro x
    have hxSub :
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt F x := by
      simpa [hdom] using hGradMem x (by simp [hdom])
    have hxPre :
        grad x ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F x) := by
      simpa [subdifferentialAt] using hxSub
    -- On the primal side, the unique subgradient is the Euclidean gradient.
    calc
      grad x = erealGradientAt (hdiffAll x) := by
        exact
          helperForTheorem_25_5_subgradientPreimage_eq_gradient
            (f := F) hconv (x := x) (hdiffAll x) hxPre
      _ = euclideanGradientAt fFin x := hgradEq x
  have hRightInvLeg :
      ∀ xStar : Fin n → ℝ, euclideanGradientAt fFin (gradStarLeg xStar) = xStar := by
    intro xStar
    have hxDualSub :
        dotProductEquiv ℝ (Fin n) (gradStarLeg xStar) ∈
          subdifferentialAt (fenchelConjugate n F) xStar := by
      simpa [hcofiniteData.1] using hGradStarMem xStar (by simp [hcofiniteData.1])
    have hxDualEuclidean :
        IsEuclideanSubgradientAt (fenchelConjugate n F) xStar (gradStarLeg xStar) := by
      simpa [IsEuclideanSubgradientAt] using hxDualSub
    have hxPrimalEuclidean :
        IsEuclideanSubgradientAt F (gradStarLeg xStar) xStar :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := F) hclosedConv hproperOn (gradStarLeg xStar) xStar).1 hxDualEuclidean
    have hxPrimalSub :
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt F (gradStarLeg xStar) := by
      simpa [IsEuclideanSubgradientAt] using hxPrimalEuclidean
    -- Applying the primal uniqueness clause identifies the selector as the inverse branch.
    have hxEq : xStar = grad (gradStarLeg xStar) :=
      hGradUnique (by simp [hdom]) hxPrimalSub
    simpa [hGradEq (gradStarLeg xStar)] using hxEq.symm
  have hSelectorEqLeg :
      ∀ xStar : Fin n → ℝ,
        gradStarLeg xStar =
          (EuclideanSpace.equiv (Fin n) ℝ)
            (Function.invFun (gradient f) ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar)) := by
    -- Both selectors solve the same right-inverse equation against the primal coordinate gradient.
    exact
      helperForTheorem_26_6_dualSelector_eq_transport_invFun
        (f := f) hf_differentiable hbij gradStarLeg
        (by
          intro xStar
          simpa [fFin, e] using hRightInvLeg xStar)
  have hSelectorEq :
      ∀ xStar : Fin n → ℝ,
        gradStar xStar =
          (EuclideanSpace.equiv (Fin n) ℝ)
            (Function.invFun (gradient f) ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar)) := by
    -- The prescribed selector satisfies the same equation, so it matches the transported inverse.
    exact
      helperForTheorem_26_6_dualSelector_eq_transport_invFun
        (f := f) hf_differentiable hbij gradStar
        (by
          intro xStar
          simpa [fFin, e] using hRightInv xStar)
  have hGradStarEq : ∀ xStar : Fin n → ℝ, gradStarLeg xStar = gradStar xStar := by
    intro xStar
    rw [hSelectorEqLeg xStar, hSelectorEq xStar]
  have hLiftEq :
      (fun xStar : Fin n → ℝ => (fStar xStar : EReal)) = fenchelConjugate n F := by
    -- Finite-everywhere dual values allow us to pass from `toReal` back to the original conjugate.
    simpa [fStar] using
      helperForTheorem_26_6_fenchelConjugate_toReal_coe_eq_of_finiteEverywhere
        (F := F) hcofiniteData.1 hproperStarOn
  have hLegendrePackStar :
      IsLegendreTypeOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) ↔
        StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ))
          (fun xStar => ((fenchelConjugate n F xStar).toReal)) ∧
          IsEssentiallySmooth (fenchelConjugate n F) := by
    simpa [hcofiniteData.1] using
      (helperForProposition_26_4_1_5_isLegendreTypeOn_interior_iff_strictConvexOn_and_essentiallySmooth
        (f := fenchelConjugate n F) hproperStar)
  have hStrict :
      StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fStar := by
    -- The dual branch inherits strict convexity from the dual Legendre-type package.
    simpa [fStar] using (hLegendrePackStar.1 hLegStar).1
  have hfiniteStar :
      ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊤ : EReal) ∧
        fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
    intro xStar
    constructor
    · -- Membership in the effective domain of `f*` rules out `+∞`.
      have hxDom :
          xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) := by
        simpa [hcofiniteData.1]
      rw [effectiveDomain_eq] at hxDom
      exact lt_top_iff_ne_top.mp hxDom.2
    · -- Properness on `univ` rules out `-∞`.
      exact hproperStarOn.2.2 xStar (by simp)
  have hERealGradWitness :
      ∀ xStar : Fin n → ℝ,
        ∃ hDiff : ERealDifferentiableAt (fenchelConjugate n F) xStar,
          erealGradientAt hDiff = gradStar xStar := by
    intro xStar
    have hDiffLeg : ERealDifferentiableAt (fenchelConjugate n F) xStar := by
      -- Unique dual subgradients force differentiability at every dual point.
      refine
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (fenchelConjugate n F) hconvStar xStar (hfiniteStar xStar)).2 ?_
      refine ⟨gradStarLeg xStar, ?_, ?_⟩
      · simpa [hcofiniteData.1] using hGradStarMem xStar (by simp [hcofiniteData.1])
      · intro y hy
        exact hGradStarUnique (by simp [hcofiniteData.1]) hy
    have hDiffLegGrad : gradStarLeg xStar = erealGradientAt hDiffLeg := by
      have huniq :=
        (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
          (fenchelConjugate n F) hconvStar xStar (hfiniteStar xStar)).1 hDiffLeg
      exact
        huniq.2.2 _ (by simpa [hcofiniteData.1] using hGradStarMem xStar (by simp [hcofiniteData.1]))
    refine ⟨hDiffLeg, ?_⟩
    calc
      erealGradientAt hDiffLeg = gradStarLeg xStar := hDiffLegGrad.symm
      _ = gradStar xStar := hGradStarEq xStar
  have hDiff :
      Differentiable ℝ fStar := by
    -- Everywhere-finite `EReal` differentiability turns into ordinary differentiability on `fStar`.
    have hEDiffAll : ∀ xStar : Fin n → ℝ, ERealDifferentiableAt (fenchelConjugate n F) xStar := by
      intro xStar
      exact (hERealGradWitness xStar).1
    simpa [fStar] using
      helperForText_26_3_3_1_realDifferentiable_of_ERealDifferentiable_everywhere
        hfiniteStar hEDiffAll
  have hbiconj :
      fenchelConjugate n (fenchelConjugate n F) = F := by
    -- Closed convexity of the primal lift gives the biconjugacy rewrite needed for co-finiteness.
    simpa using
      fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := F)
        hclosed hconv (fun x => hproperOn.2.2 x (by simp))
  have hcofinite :
      IsCofiniteFiniteConvexFunction fStar := by
    -- Co-finiteness of the real dual branch is exactly finite-everywhere-ness of its conjugate.
    refine
      (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
        (f := fStar) hStrict.convexOn).2 ?_
    constructor
    · simpa [hLiftEq, hbiconj] using hdom
    · intro x
      simpa [F, hLiftEq, hbiconj] using hproperOn.2.2 x (by simp)
  exact ⟨hDiff, hStrict, hcofinite, hLiftEq, hERealGradWitness⟩

/-- Helper for Theorem 26.6: after passing to the real-valued dual branch, the ordinary Euclidean
gradient is exactly the selector already identified with the transported inverse of `∇ f`. -/
lemma helperForTheorem_26_6_dualRealGradient_eq_selector
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hbij : Function.Bijective (gradient f))
    (gradStar : (Fin n → ℝ) → (Fin n → ℝ))
    (hRightInv :
      ∀ xStar : Fin n → ℝ,
        let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
        euclideanGradientAt fFin (gradStar xStar) = xStar) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    let fStar : (Fin n → ℝ) → ℝ := fun xStar => (fenchelConjugate n F xStar).toReal
    ∀ xStar : Fin n → ℝ, euclideanGradientAt fStar xStar = gradStar xStar := by
  intro fFin F fStar
  rcases
      helperForTheorem_26_6_dualRealBranch_properties_from_wholeSpacePackage
        (f := f) hf_convex hf_differentiable hbij gradStar hRightInv with
    ⟨hDiff, _hStrict, _hcofinite, hLiftEq, hERealGradWitness⟩
  intro xStar
  have hDiffAt : DifferentiableAt ℝ fStar xStar := hDiff.differentiableAt
  rcases
      (helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
        (hCopen := isOpen_univ) (C := (Set.univ : Set (Fin n → ℝ)))
        (f := fStar) (x := xStar) (by simp) hDiffAt) with
    ⟨hExtDiff, hExtGradEq⟩
  rcases hERealGradWitness xStar with ⟨hStarDiff, hStarGradEq⟩
  have hgradEq :
      erealGradientAt hExtDiff = erealGradientAt hStarDiff := by
    -- Rewrite the `univ`-extension witness through `hLiftEq` and compare it to the dual witness.
    have hExtHasGradLift :
        HasERealGradientAt (fun y : Fin n → ℝ => (fStar y : EReal)) xStar
          (erealGradientAt hExtDiff) := by
      simpa [indicatorFunction] using ERealDifferentiableAt.hasERealGradientAt hExtDiff
    have hExtHasGradConj :
        HasERealGradientAt (fenchelConjugate n F) xStar (erealGradientAt hExtDiff) := by
      rw [← hLiftEq]
      exact hExtHasGradLift
    exact
      erealGradient_unique
        (ERealDifferentiableAt.eventually_finiteValuedWithin_punctured hStarDiff)
        hExtHasGradConj
        (ERealDifferentiableAt.hasERealGradientAt hStarDiff)
  calc
    euclideanGradientAt fStar xStar = erealGradientAt hExtDiff := hExtGradEq.symm
    _ = erealGradientAt hStarDiff := hgradEq
    _ = gradStar xStar := hStarGradEq

/-- Helper for Theorem 26.6: under gradient bijectivity, the Fenchel conjugate of the lifted
function is real-valued everywhere and matches the inverse-gradient formula, with biconjugacy
recovering the original function. -/
lemma helperForTheorem_26_6_dualWitness
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hbij : Function.Bijective (gradient f)) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    ∃ fStar : (Fin n → ℝ) → ℝ,
      Differentiable ℝ fStar ∧
        StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fStar ∧
          IsCofiniteFiniteConvexFunction fStar ∧
            (∀ xStar : Fin n → ℝ,
              fStar xStar =
                gradientLegendreConjugate f ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar)) ∧
                  ((fun xStar : Fin n → ℝ => (fStar xStar : EReal)) =
                    fenchelConjugate n (fun x => (fFin x : EReal))) ∧
                    gradientLegendreConjugate
                        (fun xStar : EuclideanSpace ℝ (Fin n) =>
                          fStar ((EuclideanSpace.equiv (Fin n) ℝ) xStar)) =
                      f := by
  intro fFin
  let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ x : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F x,
          erealGradientAt hDiff = euclideanGradientAt fFin x) ∧
        IsEssentiallySmooth F := by
    -- Reuse the primal whole-space lift package for the dual assembly.
    simpa [fFin, F] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with
    ⟨hproper, _hclosed, hdom, _hgradWitness, _hsmooth⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hproperStarOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
    proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Convexity again transports through the Euclidean-coordinate identification.
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hcofiniteData :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ ∧
        ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
    -- The already-proved primal equivalence supplies the finite-everywhere dual-domain data.
    have hprimal :=
      helperForTheorem_26_6_bijective_iff_strictConvex_and_cofinite
        (f := f) hf_convex hf_differentiable
    have hcofinite : IsCofiniteFiniteConvexFunction fFin := hprimal.1 hbij |>.2
    exact
      (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
        (f := fFin) hfFin_convex).1 hcofinite
  rcases
      helperForTheorem_26_6_wholeSpaceLegendrePackage_from_bijectiveGradient
        (f := f) hf_convex hf_differentiable hbij with
    ⟨L, hLtarget, hLconj, LStar, hLStarTarget, hLStarConj,
      gradStar, hLfun, hLStarFun, hRightInv, _hLeftInv⟩
  let fStar : (Fin n → ℝ) → ℝ := fun xStar => (fenchelConjugate n F xStar).toReal
  have hLiftEq :
      (fun xStar : Fin n → ℝ => (fStar xStar : EReal)) = fenchelConjugate n F := by
    -- The dual conjugate is finite everywhere, so coercing `toReal` back to `EReal` recovers it.
    simpa [fStar] using
      helperForTheorem_26_6_fenchelConjugate_toReal_coe_eq_of_finiteEverywhere
        (F := F) hcofiniteData.1 hproperStarOn
  have hSelectorEq :
      ∀ xStar : Fin n → ℝ,
        gradStar xStar =
          (EuclideanSpace.equiv (Fin n) ℝ)
            (Function.invFun (gradient f) ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar)) := by
    -- The right-inverse property from the whole-space package identifies the abstract selector.
    exact
      helperForTheorem_26_6_dualSelector_eq_transport_invFun
        (f := f) hf_differentiable hbij gradStar
        (by
          intro xStar
          simpa [fFin, e] using hRightInv xStar)
  have hValueFormula :
      ∀ xStar : Fin n → ℝ,
        fStar xStar =
          gradientLegendreConjugate f ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar) := by
    intro xStar
    have hSource : gradStar xStar ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) := by
      simp [hdom]
    have hTo :
        L.toFun (gradStar xStar) = xStar := by
      -- The whole-space package says the primal coordinate gradient is the dual selector's inverse.
      calc
        L.toFun (gradStar xStar) = euclideanGradientAt fFin (gradStar xStar) := by
          rw [hLfun]
        _ = xStar := hRightInv xStar
    have hValueEReal :
        fenchelConjugate n F xStar =
          ((((dotProduct (gradStar xStar) xStar : ℝ) : EReal) - F (gradStar xStar))) := by
      -- Evaluate the Legendre value formula at the selector point and rewrite `L.conjFun`.
      calc
        fenchelConjugate n F xStar = L.conjFun xStar := (hLconj (by simp : xStar ∈ Set.univ)).symm
        _ = L.conjFun (L.toFun (gradStar xStar)) := by rw [hTo]
        _ =
            ((((dotProduct (gradStar xStar) (L.toFun (gradStar xStar)) : ℝ) : EReal) -
              F (gradStar xStar))) := L.value_eq hSource
        _ = ((((dotProduct (gradStar xStar) xStar : ℝ) : EReal) - F (gradStar xStar))) := by
              rw [hTo]
    have hFormulaEReal :
        ((fStar xStar : ℝ) : EReal) =
          (((dotProduct (gradStar xStar) xStar - fFin (gradStar xStar) : ℝ) : EReal)) := by
      calc
        ((fStar xStar : ℝ) : EReal) = fenchelConjugate n F xStar := by
          simpa [fStar] using congrFun hLiftEq xStar
        _ = ((((dotProduct (gradStar xStar) xStar : ℝ) : EReal) - F (gradStar xStar))) :=
          hValueEReal
        _ = (((dotProduct (gradStar xStar) xStar - fFin (gradStar xStar) : ℝ) : EReal)) := by
          simp [F, EReal.coe_sub]
    -- Convert the `EReal` identity back to a real-valued identity and substitute the selector.
    have hFormulaReal := congrArg EReal.toReal hFormulaEReal
    simpa [fStar, gradientLegendreConjugate, fFin, e, hSelectorEq xStar] using hFormulaReal
  have hDualBranchProps :
      Differentiable ℝ fStar ∧
        StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fStar ∧
          IsCofiniteFiniteConvexFunction fStar ∧
            ((fun xStar : Fin n → ℝ => (fStar xStar : EReal)) = fenchelConjugate n F) ∧
              (∀ xStar : Fin n → ℝ,
                ∃ hDiff : ERealDifferentiableAt (fenchelConjugate n F) xStar,
                  erealGradientAt hDiff = gradStar xStar) := by
    -- Route correction: instead of mixing the real dual branch into the final assembly, first
    -- rebuild its differentiable/strict-convex/co-finite package from the whole-space dual data.
    simpa [fFin, F, fStar] using
      helperForTheorem_26_6_dualRealBranch_properties_from_wholeSpacePackage
        (f := f) hf_convex hf_differentiable hbij gradStar
        (by
          intro xStar
          simpa [fFin, e] using hRightInv xStar)
  rcases hDualBranchProps with
    ⟨hDiffStar, hStrictStar, hCofiniteStar, _hLiftEqAgain, _hERealGradWitness⟩
  have hDualGradEq :
      ∀ xStar : Fin n → ℝ, euclideanGradientAt fStar xStar = gradStar xStar := by
    -- The ordinary real gradient of the dual branch is the same selector used in the value formula.
    simpa [fFin, F, fStar] using
      helperForTheorem_26_6_dualRealGradient_eq_selector
        (f := f) hf_convex hf_differentiable hbij gradStar
        (by
          intro xStar
          simpa [fFin, e] using hRightInv xStar)
  let g : EuclideanSpace ℝ (Fin n) → ℝ := fun xStarE => fStar (e xStarE)
  have hGradGOfGradF :
      ∀ x : EuclideanSpace ℝ (Fin n), gradient g (gradient f x) = x := by
    intro x
    have hDiffAtStar : DifferentiableAt ℝ fStar (e (gradient f x)) :=
      hDiffStar.differentiableAt
    apply e.injective
    -- Transport the dual real gradient back to source coordinates and then substitute the selector.
    calc
      e (gradient g (gradient f x)) = euclideanGradientAt fStar (e (gradient f x)) := by
        simpa [g, e] using
          helperForText_26_4_0_2_sourceGradient_transport
            (f := fStar) (x := e (gradient f x)) hDiffAtStar
      _ = gradStar (e (gradient f x)) := hDualGradEq (e (gradient f x))
      _ =
          e
            (Function.invFun (gradient f)
              ((EuclideanSpace.equiv (Fin n) ℝ).symm (e (gradient f x)))) := by
        rw [hSelectorEq (e (gradient f x))]
      _ = e x := by
        have hInvSelf : Function.invFun (gradient f) (gradient f x) = x :=
          Function.leftInverse_invFun hbij.1 x
        simpa using congrArg e hInvSelf
  have hRightInverseGF : Function.RightInverse (gradient f) (gradient g) := by
    intro x
    exact hGradGOfGradF x
  have hLeftInverseFG : Function.LeftInverse (gradient f) (gradient g) := by
    intro y
    rcases hbij.2 y with ⟨x, rfl⟩
    exact congrArg (gradient f) (hGradGOfGradF x)
  have hGradGInjective : Function.Injective (gradient g) :=
    hLeftInverseFG.injective
  have hGradGSurjective : Function.Surjective (gradient g) :=
    hRightInverseGF.surjective
  have hInvGradG :
      ∀ x : EuclideanSpace ℝ (Fin n), Function.invFun (gradient g) x = gradient f x := by
    intro x
    -- Injectivity of `∇ g` identifies the chosen inverse branch with the known preimage `∇ f x`.
    apply hGradGInjective
    calc
      gradient g (Function.invFun (gradient g) x) = x :=
        Function.rightInverse_invFun hGradGSurjective x
      _ = gradient g (gradient f x) := by rw [hGradGOfGradF x]
  refine ⟨fStar, hDiffStar, hStrictStar, hCofiniteStar, hValueFormula, hLiftEq, ?_⟩
  funext x
  -- Evaluate the dual value formula at `∇ f x`, then replace the dual inverse by the known branch.
  rw [gradientLegendreConjugate, hInvGradG x]
  change dotProduct (fun i => gradient f x i) (fun i => x i) - fStar (e (gradient f x)) = f x
  rw [hValueFormula (e (gradient f x))]
  have hdot :
      dotProduct (fun i => gradient f x i) (fun i => x i) =
        dotProduct (fun i => x i) (fun i => gradient f x i) := by
    exact dotProduct_comm _ _
  have hArg :
      ((EuclideanSpace.equiv (Fin n) ℝ).symm (e (gradient f x))) = gradient f x := by
    simp [e]
  have hInvSelf : Function.invFun (gradient f) (gradient f x) = x :=
    Function.leftInverse_invFun hbij.1 x
  rw [gradientLegendreConjugate, hArg, hInvSelf]
  simp [hdot]

-- Proof sketch: use Corollary 26.3.1 together with the differentiability hypothesis to identify
-- `∂ f` with the singleton-valued gradient map on all of `ℝ^n`, then combine Theorem 26.5 with
-- the Chapter 13 co-finiteness criterion to characterize surjectivity of `∇ f` by co-finiteness
-- and to identify the Fenchel conjugate with the inverse-gradient formula. Apply the same
-- argument to the dual function to obtain involutivity.
/-- Theorem 26.6: let `f` be a differentiable convex function on `ℝ^n`. Then the gradient map
`∇ f` is one-to-one from `ℝ^n` onto itself if and only if `f` is strictly convex and co-finite.
In that case there exists a differentiable strictly convex co-finite function `fStar` on `ℝ^n`
such that `fStar` coincides with the inverse-gradient Legendre conjugate formula
`fStar x* = ⟪(∇ f)⁻¹ x*, x*⟫ - f ((∇ f)⁻¹ x*)`, the standard `EReal` lift of `fStar` is the
Fenchel conjugate of the standard lift of `f`, and the Legendre conjugate of `fStar` is `f`. -/
theorem gradient_bijective_iff_strictConvex_and_cofinite_with_legendre_conjugate_properties
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    (Function.Bijective (gradient f) ↔
      StrictConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f ∧
        IsCofiniteFiniteConvexFunction fFin) ∧
      (Function.Bijective (gradient f) →
        ∃ fStar : (Fin n → ℝ) → ℝ,
          Differentiable ℝ fStar ∧
            StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fStar ∧
              IsCofiniteFiniteConvexFunction fStar ∧
                (∀ xStar : Fin n → ℝ,
                  fStar xStar =
                    gradientLegendreConjugate f ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar)) ∧
                  ((fun xStar : Fin n → ℝ => (fStar xStar : EReal)) =
                    fenchelConjugate n (fun x => (fFin x : EReal))) ∧
                    gradientLegendreConjugate
                        (fun xStar : EuclideanSpace ℝ (Fin n) =>
                          fStar ((EuclideanSpace.equiv (Fin n) ℝ) xStar)) =
                      f) := by
  intro fFin
  constructor
  · -- The primal equivalence is now isolated to the gradient-image/co-finiteness conversion.
    exact
      helperForTheorem_26_6_bijective_iff_strictConvex_and_cofinite
        (f := f) hf_convex hf_differentiable
  · intro hbij
    -- The dual witness is isolated to the whole-space specialization of Theorem 26.5.
    exact
      helperForTheorem_26_6_dualWitness
        (f := f) hf_convex hf_differentiable hbij

-- Proof sketch: use the Chapter 13 characterization of co-finiteness via the recession
-- behavior of a convex function together with the differentiability/subdifferential
-- correspondence from Chapters 23 and 24 to identify recession growth with the coercive
-- properness of the gradient map, which is equivalent to the sequencewise blow-up of
-- `‖∇ f (xᵢ)‖` along every sequence escaping to infinity.
/-- Helper for Lemma 26.7: on the coordinate lift of a differentiable convex function, every
subgradient agrees with the Euclidean gradient. -/
lemma helperForLemma_26_7_primalSubgradient_eq_coordinateGradient
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    {x xStar : Fin n → ℝ} :
    let fFin : (Fin n → ℝ) → ℝ := fun y => f ((EuclideanSpace.equiv (Fin n) ℝ).symm y)
    let F : (Fin n → ℝ) → EReal := fun y => (fFin y : EReal)
    dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt F x →
      xStar = euclideanGradientAt fFin x := by
  intro fFin F hxSub
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    -- Reuse the standard coordinate-lift package to access differentiability at every point.
    simpa [fFin, F] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with ⟨hproper, _hclosed, _hdom, hgradWitness, _hES⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  rcases hgradWitness x with ⟨hDiff, hGradEq⟩
  have huniq :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      F hconv x (ERealDifferentiableAt.finiteAt hDiff)).1 hDiff
  -- Differentiability makes the displayed subgradient equal to the coordinate gradient.
  calc
    xStar = erealGradientAt hDiff := by
      exact huniq.2.2 _ hxSub
    _ = euclideanGradientAt fFin x := hGradEq

/-- Helper for Lemma 26.7: a primal gradient value becomes a Euclidean subgradient of the Fenchel
conjugate at the corresponding dual point. -/
lemma helperForLemma_26_7_dualSubgradient_of_gradientValue
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (x : EuclideanSpace ℝ (Fin n)) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let fFin : (Fin n → ℝ) → ℝ := fun y => f (e.symm y)
    let F : (Fin n → ℝ) → EReal := fun y => (fFin y : EReal)
    IsEuclideanSubgradientAt (fenchelConjugate n F) (e (gradient f x)) (e x) := by
  intro e fFin F
  have hfFin_differentiable : Differentiable ℝ fFin := by
    -- The coordinate lift stays differentiable because `e.symm` is linear.
    simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    -- Reuse the standard coordinate package to put the primal lift into the Chapter 23 framework.
    simpa [fFin, F, e] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with ⟨hproper, hclosed, _hdom, hgradWitness, _hES⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hclosedConv : ClosedConvexFunction F := ⟨hconv, hclosed⟩
  rcases hgradWitness (e x) with ⟨hDiff, hGradEq⟩
  have hPrimalCore :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      F hconv (e x) (ERealDifferentiableAt.finiteAt hDiff)).1 hDiff
  have hTransport : e (gradient f x) = euclideanGradientAt fFin (e x) := by
    -- Transport the source-space gradient to the coordinate model used by the Fenchel machinery.
    simpa [fFin, e] using
      (helperForText_26_4_0_2_sourceGradient_transport
        (f := fFin) (x := e x) hfFin_differentiable.differentiableAt)
  have hPrimalEuclidean : IsEuclideanSubgradientAt F (e x) (e (gradient f x)) := by
    -- The coordinate gradient is the unique primal subgradient at `e x`.
    rw [hTransport]
    simpa [IsEuclideanSubgradientAt, hGradEq] using hPrimalCore.1
  -- Corollary 23.5.1 transports the primal witness to a dual subgradient of the conjugate.
  exact
    (euclidean_subgradient_fenchelConjugate_iff
      (f := F) hclosedConv hproperOn (e x) (e (gradient f x))).2 hPrimalEuclidean

/-- Helper for Lemma 26.7: a bounded set stays bounded under a continuous linear map. -/
lemma helperForLemma_26_7_boundedImage_of_boundedSet_underContinuousLinearMap
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) {s : Set E} (hs : Bornology.IsBounded s) :
    Bornology.IsBounded (L '' s) := by
  -- Control the image norms by the operator norm of `L`.
  rcases (isBounded_iff_forall_norm_le (s := s)).1 hs with ⟨R, hR⟩
  refine (isBounded_iff_forall_norm_le (s := L '' s)).2 ?_
  refine ⟨‖L‖ * R, ?_⟩
  intro y hy
  rcases hy with ⟨x, hx, rfl⟩
  exact
    le_trans (L.le_opNorm x)
      (mul_le_mul_of_nonneg_left (hR x hx) (norm_nonneg _))

/-- Helper for Lemma 26.7: a convergent sequence in a metric space has bounded range. -/
lemma helperForLemma_26_7_boundedRange_of_tendsto
    {X : Type*} [PseudoMetricSpace X] {u : ℕ → X} {x : X}
    (hu : Filter.Tendsto u Filter.atTop (nhds x)) :
    Bornology.IsBounded (Set.range u) := by
  -- Convergence traps the tail in one closed ball, and the finite head is bounded separately.
  have htail : ∀ᶠ n in Filter.atTop, u n ∈ Metric.closedBall x 1 := by
    exact hu (Metric.closedBall_mem_nhds x (by norm_num))
  rcases Filter.eventually_atTop.mp htail with ⟨N, hN⟩
  have hheadFinite : (u '' Set.Iic N).Finite := (Set.finite_Iic N).image u
  have hheadBounded : Bornology.IsBounded (u '' Set.Iic N) := hheadFinite.isBounded
  have htailBounded : Bornology.IsBounded (Metric.closedBall x 1) :=
    Metric.isBounded_closedBall
  have hrangeSubset : Set.range u ⊆ u '' Set.Iic N ∪ Metric.closedBall x 1 := by
    intro y hy
    rcases hy with ⟨n, rfl⟩
    by_cases hn : n ≤ N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr (hN n (Nat.le_of_lt (Nat.lt_of_not_ge hn)))
  exact (hheadBounded.union htailBounded).subset hrangeSubset

/-- Helper for Lemma 26.7: if the range of a sequence in a normed space is unbounded, then one
can extract a subsequence whose norms dominate the index. -/
lemma helperForLemma_26_7_extraction_of_unboundedRange
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℕ → E}
    (hu : ¬ Bornology.IsBounded (Set.range u)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k : ℕ, (k : ℝ) ≤ ‖u (φ k)‖ := by
  have hfreq : ∀ K : ℕ, ∃ᶠ i : ℕ in Filter.atTop, (K : ℝ) ≤ ‖u i‖ := by
    intro K
    by_contra hK
    have hEventBase :
        ∀ᶠ i : ℕ in Filter.atTop, ¬ (K : ℝ) ≤ ‖u i‖ :=
      Filter.not_frequently.mp hK
    have hEvent : ∀ᶠ i : ℕ in Filter.atTop, ‖u i‖ < K := by
      -- Negating the frequent lower bound turns the tail into a uniform closed-ball bound.
      filter_upwards [hEventBase] with i hi
      exact lt_of_not_ge hi
    rcases Filter.eventually_atTop.mp hEvent with ⟨N, hN⟩
    have hheadFinite : (u '' Set.Iic N).Finite := (Set.finite_Iic N).image u
    have hheadBounded : Bornology.IsBounded (u '' Set.Iic N) := hheadFinite.isBounded
    have htailBounded : Bornology.IsBounded (Metric.closedBall (0 : E) K) :=
      Metric.isBounded_closedBall
    have hrangeSubset : Set.range u ⊆ u '' Set.Iic N ∪ Metric.closedBall (0 : E) K := by
      intro y hy
      rcases hy with ⟨i, rfl⟩
      by_cases hi : i ≤ N
      · exact Or.inl ⟨i, hi, rfl⟩
      · exact Or.inr (by
          have hlt : ‖u i‖ < (K : ℝ) := hN i (Nat.le_of_lt (Nat.lt_of_not_ge hi))
          have hle : ‖u i‖ ≤ (K : ℝ) := le_of_lt hlt
          simpa [Metric.mem_closedBall, dist_eq_norm] using hle)
    exact hu ((hheadBounded.union htailBounded).subset hrangeSubset)
  -- Diagonal extraction turns the frequent lower bounds into one strict-mono subsequence.
  rcases Filter.extraction_forall_of_frequently hfreq with ⟨φ, hφ, hφprop⟩
  exact ⟨φ, hφ, hφprop⟩

/-- Helper for Lemma 26.7: bounded dual values force bounded primal witness ranges for Fenchel
subgradients. -/
lemma helperForLemma_26_7_boundedPrimalWitnessRange_of_boundedDualValues
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hSeq :
      ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (fun i : ℕ => ‖xSeq i‖) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun i : ℕ => ‖gradient f (xSeq i)‖) Filter.atTop Filter.atTop)
    (xStarSeq xSeq : ℕ → Fin n → ℝ) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let fFin : (Fin n → ℝ) → ℝ := fun y => f (e.symm y)
    let F : (Fin n → ℝ) → EReal := fun y => (fFin y : EReal)
    Bornology.IsBounded (Set.range xStarSeq) →
      (∀ i : ℕ, IsEuclideanSubgradientAt (fenchelConjugate n F) (xStarSeq i) (xSeq i)) →
      Bornology.IsBounded (Set.range xSeq) := by
  intro e fFin F hDualBounded hWitness
  have hfFin_differentiable : Differentiable ℝ fFin := by
    -- The coordinate lift stays differentiable because `e.symm` is linear.
    simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    -- Reuse the standard coordinate package before switching to dual witnesses.
    simpa [fFin, F, e] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with ⟨hproper, hclosed, _hdom, _hgradWitness, _hES⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hclosedConv : ClosedConvexFunction F := ⟨hconv, hclosed⟩
  by_contra hPrimalUnbounded
  let primalSeq : ℕ → EuclideanSpace ℝ (Fin n) := fun i => e.symm (xSeq i)
  have hPrimalSeqUnbounded : ¬ Bornology.IsBounded (Set.range primalSeq) := by
    intro hPrimalBounded
    have hImageBounded :
        Bornology.IsBounded
          ((e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)) '' Set.range primalSeq) :=
      helperForLemma_26_7_boundedImage_of_boundedSet_underContinuousLinearMap
        (L := (e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))) hPrimalBounded
    have hImageEq :
        ((e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)) '' Set.range primalSeq) =
          Set.range xSeq := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with ⟨i, rfl⟩
        exact ⟨i, by simp [primalSeq]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨primalSeq i, ⟨i, rfl⟩, by simp [primalSeq]⟩
    exact hPrimalUnbounded (hImageEq ▸ hImageBounded)
  rcases
      helperForLemma_26_7_extraction_of_unboundedRange
        (u := primalSeq) hPrimalSeqUnbounded with
    ⟨φ, hφmono, hφnorm⟩
  have hNormTend :
      Filter.Tendsto (fun k : ℕ => ‖primalSeq (φ k)‖) Filter.atTop Filter.atTop := by
    -- The extracted subsequence has norms eventually above every real threshold.
    rw [Filter.tendsto_atTop]
    intro R
    filter_upwards [Filter.eventually_ge_atTop (Nat.ceil R)] with k hk
    have hRle : R ≤ (k : ℝ) := by
      exact le_trans (Nat.le_ceil R) (by exact_mod_cast hk)
    exact le_trans hRle (hφnorm k)
  have hDualSubgradientEq :
      ∀ i : ℕ, xStarSeq i = e (gradient f (primalSeq i)) := by
    intro i
    -- Convert the dual witness to a primal subgradient, then identify it with the gradient.
    have hPrimalWitness :
        IsEuclideanSubgradientAt F (xSeq i) (xStarSeq i) :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := F) hclosedConv hproperOn (xSeq i) (xStarSeq i)).1 (hWitness i)
    have hPrimalSub :
        dotProductEquiv ℝ (Fin n) (xStarSeq i) ∈ subdifferentialAt F (xSeq i) := by
      simpa [IsEuclideanSubgradientAt] using hPrimalWitness
    have hCoordGrad :
        xStarSeq i = euclideanGradientAt fFin (xSeq i) :=
      helperForLemma_26_7_primalSubgradient_eq_coordinateGradient
        (f := f) hf_convex hf_differentiable hPrimalSub
    have hTransport :
        e (gradient f (primalSeq i)) = euclideanGradientAt fFin (xSeq i) := by
      simpa [primalSeq, fFin, e] using
        (helperForText_26_4_0_2_sourceGradient_transport
          (f := fFin) (x := xSeq i) hfFin_differentiable.differentiableAt)
    exact hCoordGrad.trans hTransport.symm
  have hDualSubseqBounded :
      Bornology.IsBounded (Set.range fun k : ℕ => xStarSeq (φ k)) :=
    hDualBounded.subset (by
      intro y hy
      rcases hy with ⟨k, rfl⟩
      exact ⟨φ k, rfl⟩)
  have hGradSubseqBounded :
      Bornology.IsBounded (Set.range fun k : ℕ => gradient f (primalSeq (φ k))) := by
    -- Rewrite the gradient subsequence as the image of the bounded dual subsequence under `e.symm`.
    have hImageBounded :
        Bornology.IsBounded
          (((e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))) ''
            Set.range (fun k : ℕ => xStarSeq (φ k))) :=
      helperForLemma_26_7_boundedImage_of_boundedSet_underContinuousLinearMap
        (L := (e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))) hDualSubseqBounded
    have hImageEq :
        (((e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n))) ''
            Set.range (fun k : ℕ => xStarSeq (φ k))) =
          Set.range (fun k : ℕ => gradient f (primalSeq (φ k))) := by
      ext y
      constructor
      · rintro ⟨xStar, hxStar, rfl⟩
        rcases hxStar with ⟨k, rfl⟩
        refine ⟨k, ?_⟩
        calc
          gradient f (primalSeq (φ k)) = e.symm (e (gradient f (primalSeq (φ k)))) := by simp
          _ = e.symm (xStarSeq (φ k)) := by rw [hDualSubgradientEq (φ k)]
      · rintro ⟨k, rfl⟩
        refine ⟨xStarSeq (φ k), ⟨k, rfl⟩, ?_⟩
        calc
          e.symm (xStarSeq (φ k)) = e.symm (e (gradient f (primalSeq (φ k)))) := by
            rw [hDualSubgradientEq (φ k)]
          _ = gradient f (primalSeq (φ k)) := by simp
    exact hImageEq ▸ hImageBounded
  rcases
      (isBounded_iff_forall_norm_le
        (s := Set.range fun k : ℕ => gradient f (primalSeq (φ k)))).1
        hGradSubseqBounded with
    ⟨R, hR⟩
  have hGradNotTend :
      ¬ Filter.Tendsto
        (fun k : ℕ => ‖gradient f (primalSeq (φ k))‖)
        Filter.atTop Filter.atTop := by
    intro hGradTend
    have hEventuallySmall :
        ∀ᶠ k : ℕ in Filter.atTop, ‖gradient f (primalSeq (φ k))‖ ≤ R :=
      Filter.Eventually.of_forall (fun k => hR _ ⟨k, rfl⟩)
    have hEventuallyLarge :
        ∀ᶠ k : ℕ in Filter.atTop, R + 1 ≤ ‖gradient f (primalSeq (φ k))‖ :=
      (Filter.tendsto_atTop.1 hGradTend) (R + 1)
    have hFalse : ∀ᶠ k : ℕ in Filter.atTop, False :=
      (hEventuallySmall.and hEventuallyLarge).mono (fun _ hk =>
        (not_le_of_gt (lt_add_of_pos_right R zero_lt_one))
          (le_trans hk.2 hk.1))
    rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
    exact hN N le_rfl
  -- The escaping primal subsequence violates the sequencewise blow-up hypothesis.
  exact
    hGradNotTend
      (hSeq (fun k : ℕ => primalSeq (φ k)) hNormTend)

/-- Helper for Lemma 26.7: co-finiteness makes the dual effective domain equal to all of `ℝⁿ`,
so bounded dual values force bounded primal witness ranges for Fenchel subgradients. -/
lemma helperForLemma_26_7_boundedPrimalWitnessRange_of_boundedDualValues_of_cofinite
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (xStarSeq xSeq : ℕ → Fin n → ℝ) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let fFin : (Fin n → ℝ) → ℝ := fun y => f (e.symm y)
    let F : (Fin n → ℝ) → EReal := fun y => (fFin y : EReal)
    IsCofiniteFiniteConvexFunction fFin →
      Bornology.IsBounded (Set.range xStarSeq) →
      (∀ i : ℕ, IsEuclideanSubgradientAt (fenchelConjugate n F) (xStarSeq i) (xSeq i)) →
      Bornology.IsBounded (Set.range xSeq) := by
  intro e fFin F hcofinite hDualBounded hWitness
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Convexity transports through the Euclidean-coordinate identification.
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    -- Reuse the primal coordinate package before applying boundedness on the dual side.
    simpa [fFin, F, e] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with ⟨hproper, _hclosed, _hdom, _hgradWitness, _hES⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hproperStarOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
    proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn
  have hDualDomUniv :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ :=
    (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
      (f := fFin) hfFin_convex).1 hcofinite |>.1
  rcases (isBounded_iff_forall_norm_le (s := Set.range xStarSeq)).1 hDualBounded with ⟨R, hR⟩
  have hBallClosed : IsClosed (Metric.closedBall (0 : Fin n → ℝ) R) :=
    Metric.isClosed_closedBall
  have hBallBounded : Bornology.IsBounded (Metric.closedBall (0 : Fin n → ℝ) R) :=
    Metric.isBounded_closedBall
  have hBallInterior :
      Metric.closedBall (0 : Fin n → ℝ) R ⊆
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) := by
    -- Co-finiteness turns the dual effective domain into the whole space.
    simpa [hDualDomUniv]
  have hImageBounded :
      Bornology.IsBounded
        (subdifferentialImageOn (fenchelConjugate n F) (Metric.closedBall (0 : Fin n → ℝ) R)) :=
    helperForTheorem_5_24_10_subdifferentialImageOn_isBounded
      (f := fenchelConjugate n F) hproperStarOn hBallClosed hBallBounded hBallInterior
  have hRangeSubset :
      Set.range xSeq ⊆
        subdifferentialImageOn (fenchelConjugate n F) (Metric.closedBall (0 : Fin n → ℝ) R) := by
    intro y hy
    rcases hy with ⟨i, rfl⟩
    have hxStarBall : xStarSeq i ∈ Metric.closedBall (0 : Fin n → ℝ) R := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hR (xStarSeq i) ⟨i, rfl⟩
    have hxSub :
        xSeq i ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹'
          subdifferentialAt (fenchelConjugate n F) (xStarSeq i)) := by
      simpa [IsEuclideanSubgradientAt] using hWitness i
    -- Each witness lies in the subdifferential image over the bounded dual ball.
    exact Set.mem_iUnion.2 ⟨xStarSeq i, Set.mem_iUnion.2 ⟨hxStarBall, hxSub⟩⟩
  exact hImageBounded.subset hRangeSubset

/-- Helper for Lemma 26.7: if gradient norms blow up along every escaping primal sequence, then
the effective domain of the dual subdifferential is closed. -/
lemma helperForLemma_26_7_dualSubdifferentialEffectiveDomain_isClosed_of_gradientNormBlowup
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hSeq :
      ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (fun i : ℕ => ‖xSeq i‖) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun i : ℕ => ‖gradient f (xSeq i)‖) Filter.atTop Filter.atTop) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let fFin : (Fin n → ℝ) → ℝ := fun y => f (e.symm y)
    let F : (Fin n → ℝ) → EReal := fun y => (fFin y : EReal)
    IsClosed (subdifferentialEffectiveDomain (fenchelConjugate n F)) := by
  intro e fFin F
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    -- Reuse the standard coordinate package before passing to the dual graph.
    simpa [fFin, F, e] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with ⟨hproper, hclosed, _hdom, _hgradWitness, _hES⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hproperStarOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
    proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn
  have hclosedStar : LowerSemicontinuous (fenchelConjugate n F) := by
    simpa using (fenchelConjugate_closedConvex (n := n) (f := F)).1
  have hconvStar : ConvexFunction (fenchelConjugate n F) := by
    simpa [ConvexFunction] using hproperStarOn.1
  have hclosedConvStar : ClosedConvexFunction (fenchelConjugate n F) := ⟨hconvStar, hclosedStar⟩
  rw [← isSeqClosed_iff_isClosed]
  intro xStarSeq xStar hxSeq hxTend
  have hDualBounded :
      Bornology.IsBounded (Set.range xStarSeq) :=
    helperForLemma_26_7_boundedRange_of_tendsto hxTend
  have hxNonempty :
      ∀ i : ℕ, Set.Nonempty (subdifferentialAt (fenchelConjugate n F) (xStarSeq i)) := by
    intro i
    exact
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
        (fenchelConjugate n F) (xStarSeq i)).1 (hxSeq i)
  choose xDualSeq hxDualSub using hxNonempty
  let xSeq : ℕ → Fin n → ℝ := fun i => (dotProductEquiv ℝ (Fin n)).symm (xDualSeq i)
  have hPrimalBounded :
      Bornology.IsBounded (Set.range xSeq) :=
    helperForLemma_26_7_boundedPrimalWitnessRange_of_boundedDualValues
      (f := f) hf_convex hf_differentiable hSeq xStarSeq xSeq hDualBounded
        (fun i => by
          simpa [xSeq, IsEuclideanSubgradientAt] using hxDualSub i)
  rcases
      tendsto_subseq_of_bounded hPrimalBounded (fun i => ⟨i, rfl⟩) with
    ⟨xLimit, _hxLimit, φ, hφmono, hxTendSub⟩
  have hxStarTendSub :
      Filter.Tendsto (fun i : ℕ => xStarSeq (φ i)) Filter.atTop (nhds xStar) :=
    hxTend.comp hφmono.tendsto_atTop
  have hLimitSub :
      dotProductEquiv ℝ (Fin n) xLimit ∈ subdifferentialAt (fenchelConjugate n F) xStar :=
    (subdifferential_limit_mem_and_isClosed_graph
      (f := fenchelConjugate n F) hclosedConvStar hproperStarOn).1
      (x := xStar) (xStar := xLimit)
      (fun i => xStarSeq (φ i)) (fun i => xSeq (φ i))
      (fun i => by
        simpa [xSeq] using hxDualSub (φ i))
      hxStarTendSub hxTendSub
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fenchelConjugate n F) xStar).2
      ⟨dotProductEquiv ℝ (Fin n) xLimit, hLimitSub⟩

/-- Helper for Lemma 26.7: under the sequencewise gradient blow-up hypothesis, the effective
domain of the dual subdifferential is exactly the interior of the effective domain of the Fenchel
conjugate. -/
lemma helperForLemma_26_7_dualSubdifferentialEffectiveDomain_eq_interior_of_gradientNormBlowup
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hSeq :
      ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (fun i : ℕ => ‖xSeq i‖) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun i : ℕ => ‖gradient f (xSeq i)‖) Filter.atTop Filter.atTop) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let fFin : (Fin n → ℝ) → ℝ := fun y => f (e.symm y)
    let F : (Fin n → ℝ) → EReal := fun y => (fFin y : EReal)
    subdifferentialEffectiveDomain (fenchelConjugate n F) =
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) := by
  intro e fFin F
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    -- Reuse the primal coordinate package before applying Theorem 23.4 to the dual function.
    simpa [fFin, F, e] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with ⟨hproper, hclosed, _hdom, _hgradWitness, _hES⟩
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hproperStarOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
    proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn
  ext xStar
  constructor
  · intro hxDom
    have hxSubNonempty :
        Set.Nonempty (subdifferentialAt (fenchelConjugate n F) xStar) := by
      exact
        (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
          (fenchelConjugate n F) xStar).1 hxDom
    have hxFiberBounded :
        Bornology.IsBounded
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fenchelConjugate n F) xStar) := by
      by_contra hFiberUnbounded
      have hChoose :
          ∀ k : ℕ,
            ∃ x : Fin n → ℝ,
              x ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹'
                subdifferentialAt (fenchelConjugate n F) xStar) ∧
                (k : ℝ) ≤ ‖x‖ := by
        intro k
        by_contra hk
        apply hFiberUnbounded
        refine
          (isBounded_iff_forall_norm_le
            (s := ((dotProductEquiv ℝ (Fin n)) ⁻¹'
              subdifferentialAt (fenchelConjugate n F) xStar))).2 ?_
        refine ⟨k, ?_⟩
        intro x hx
        exact le_of_not_ge (fun hxk => hk ⟨x, hx, hxk⟩)
      choose xSeq hxSeqMem hxSeqNorm using hChoose
      have hConstDualBounded :
          Bornology.IsBounded (Set.range fun _ : ℕ => xStar) := by
        refine (isBounded_iff_forall_norm_le (s := Set.range fun _ : ℕ => xStar)).2 ?_
        refine ⟨‖xStar‖, ?_⟩
        intro y hy
        rcases hy with ⟨i, rfl⟩
        simp
      have hSeqBounded :
          Bornology.IsBounded (Set.range xSeq) :=
        helperForLemma_26_7_boundedPrimalWitnessRange_of_boundedDualValues
          (f := f) hf_convex hf_differentiable hSeq (fun _ : ℕ => xStar) xSeq
            hConstDualBounded
            (fun i => by
              simpa [IsEuclideanSubgradientAt] using hxSeqMem i)
      rcases (isBounded_iff_forall_norm_le (s := Set.range xSeq)).1 hSeqBounded with ⟨R, hR⟩
      let K : ℕ := Nat.ceil R + 1
      have hKR : R < (K : ℝ) := by
        have hCeil : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
        have hLt : (Nat.ceil R : ℝ) < K := by
          norm_num [K]
        exact lt_of_le_of_lt hCeil hLt
      have hKle : (K : ℝ) ≤ ‖xSeq K‖ := hxSeqNorm K
      have hKmem : xSeq K ∈ Set.range xSeq := ⟨K, rfl⟩
      have hRle : ‖xSeq K‖ ≤ R := hR _ hKmem
      exact (not_le_of_gt hKR) (le_trans hKle hRle)
    -- Theorem 23.4 turns nonempty bounded dual fibers into interior membership.
    exact
      (((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
        (fenchelConjugate n F) hproperStarOn xStar).2.2.1).1
          ⟨hxSubNonempty, hxFiberBounded⟩)
  · intro hxInt
    have hxSub :
        Set.Nonempty (subdifferentialAt (fenchelConjugate n F) xStar) ∧
          Bornology.IsBounded
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt (fenchelConjugate n F) xStar) := by
      exact
        (((subdifferential_empty_off_effectiveDomain_nonempty_on_relativeInterior_and_bounded_iff_mem_interior
          (fenchelConjugate n F) hproperStarOn xStar).2.2.1).2 hxInt)
    exact
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
        (fenchelConjugate n F) xStar).2 hxSub.1

/-- Helper for Lemma 26.7: the sequencewise gradient blow-up hypothesis forces the Fenchel
conjugate of the coordinate lift to be finite everywhere, hence the coordinate lift is
co-finite. -/
lemma helperForLemma_26_7_cofinite_of_gradientNormBlowup
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hSeq :
      ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (fun i : ℕ => ‖xSeq i‖) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun i : ℕ => ‖gradient f (xSeq i)‖) Filter.atTop Filter.atTop) :
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let fFin : (Fin n → ℝ) → ℝ := fun x => f (e.symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    IsCofiniteFiniteConvexFunction fFin := by
  intro e fFin F
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Convexity transports through the Euclidean-coordinate identification.
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hInteriorEq :
      subdifferentialEffectiveDomain (fenchelConjugate n F) =
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) :=
    helperForLemma_26_7_dualSubdifferentialEffectiveDomain_eq_interior_of_gradientNormBlowup
      (f := f) hf_convex hf_differentiable hSeq
  have hClosedDom :
      IsClosed (subdifferentialEffectiveDomain (fenchelConjugate n F)) :=
    helperForLemma_26_7_dualSubdifferentialEffectiveDomain_isClosed_of_gradientNormBlowup
      (f := f) hf_convex hf_differentiable hSeq
  have hInteriorNonempty :
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F))).Nonempty := by
    -- A single primal point already produces one dual subgradient, hence one interior dual point.
    have hZeroWitness :
        IsEuclideanSubgradientAt (fenchelConjugate n F)
          (e (gradient f 0)) (e (0 : EuclideanSpace ℝ (Fin n))) := by
      simpa [F, fFin, e] using
        helperForLemma_26_7_dualSubgradient_of_gradientValue
          (f := f) hf_convex hf_differentiable (0 : EuclideanSpace ℝ (Fin n))
    have hZeroDom :
        e (gradient f 0) ∈ subdifferentialEffectiveDomain (fenchelConjugate n F) := by
      exact
        (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
          (fenchelConjugate n F) (e (gradient f 0))).2
          ⟨dotProductEquiv ℝ (Fin n) (e (0 : EuclideanSpace ℝ (Fin n))), by
            simpa [IsEuclideanSubgradientAt] using hZeroWitness⟩
    exact ⟨e (gradient f 0), by simpa [hInteriorEq] using hZeroDom⟩
  have hInteriorClopen :
      IsClopen
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F))) := by
    constructor
    · simpa [hInteriorEq] using hClosedDom
    · exact isOpen_interior
  have hInteriorUniv :
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) = Set.univ := by
    rcases (isClopen_iff.1 hInteriorClopen) with hEmpty | hUniv
    · cases hInteriorNonempty.ne_empty hEmpty
    · exact hUniv
  have hDomUniv :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ := by
    ext xStar
    constructor
    · intro _hxStar
      simp
    · intro _hxStar
      exact interior_subset (by simpa [hInteriorUniv])
  have hproper :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ y : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F y,
          erealGradientAt hDiff = euclideanGradientAt fFin y) ∧
        IsEssentiallySmooth F := by
    simpa [fFin, F, e] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper.1
  have hNeBot :
      ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
    intro xStar
    exact
      (proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn).2.2 xStar (by simp)
  exact
    (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
      (f := fFin) hfFin_convex).2
      ⟨hDomUniv, hNeBot⟩

/-- Lemma 26.7: let `f` be a differentiable convex function on `ℝ^n`. Then `f` is co-finite if
and only if, for every sequence `xᵢ` with `‖xᵢ‖ → +∞`, one has `‖∇ f (xᵢ)‖ → +∞`. -/
lemma isCofiniteFiniteConvexFunction_iff_gradientNorm_tendsto_atTop_along_sequences
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    IsCofiniteFiniteConvexFunction fFin ↔
      ∀ xSeq : ℕ → EuclideanSpace ℝ (Fin n),
        Filter.Tendsto (fun i : ℕ => ‖xSeq i‖) Filter.atTop Filter.atTop →
        Filter.Tendsto (fun i : ℕ => ‖gradient f (xSeq i)‖) Filter.atTop Filter.atTop := by
  intro fFin
  constructor
  · intro hcofinite xSeq hxTend
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    by_contra hGradNotTend
    rcases
        helperForTheorem_26_1_exists_strictMono_boundedSubsequence_of_not_tendsto_atTop
          (a := fun i : ℕ => ‖gradient f (xSeq i)‖)
          (ha_nonneg := fun i => norm_nonneg (gradient f (xSeq i)))
          hGradNotTend with
      ⟨R, _hRnonneg, φ, hφmono, hφBounded⟩
    have hGradientSubseqBounded :
        Bornology.IsBounded (Set.range fun k : ℕ => gradient f (xSeq (φ k))) := by
      -- The extracted subsequence keeps the gradient norm uniformly bounded by `R`.
      refine (isBounded_iff_forall_norm_le (s := Set.range fun k : ℕ => gradient f (xSeq (φ k)))).2 ?_
      refine ⟨R, ?_⟩
      intro y hy
      rcases hy with ⟨k, rfl⟩
      exact hφBounded k
    have hDualSubseqImageBounded :
        Bornology.IsBounded
          (((e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)) ''
            Set.range (fun k : ℕ => gradient f (xSeq (φ k))))) :=
      helperForLemma_26_7_boundedImage_of_boundedSet_underContinuousLinearMap
        (L := (e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ))) hGradientSubseqBounded
    have hDualSubseqImageEq :
        (((e : EuclideanSpace ℝ (Fin n) →L[ℝ] (Fin n → ℝ)) ''
            Set.range (fun k : ℕ => gradient f (xSeq (φ k))))) =
          Set.range (fun k : ℕ => e (gradient f (xSeq (φ k)))) := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with ⟨k, rfl⟩
        exact ⟨k, rfl⟩
      · rintro ⟨k, rfl⟩
        exact ⟨gradient f (xSeq (φ k)), ⟨k, rfl⟩, rfl⟩
    have hDualSubseqBounded :
        Bornology.IsBounded (Set.range fun k : ℕ => e (gradient f (xSeq (φ k)))) :=
      hDualSubseqImageEq ▸ hDualSubseqImageBounded
    have hDualWitness :
        ∀ k : ℕ,
          IsEuclideanSubgradientAt (fenchelConjugate n F)
            (e (gradient f (xSeq (φ k)))) (e (xSeq (φ k))) := by
      intro k
      -- The primal gradient value produces the dual Fenchel subgradient at each subsequence term.
      simpa [F, fFin, e] using
        helperForLemma_26_7_dualSubgradient_of_gradientValue
          (f := f) hf_convex hf_differentiable (xSeq (φ k))
    have hCoordinateSubseqBounded :
        Bornology.IsBounded (Set.range fun k : ℕ => e (xSeq (φ k))) :=
      helperForLemma_26_7_boundedPrimalWitnessRange_of_boundedDualValues_of_cofinite
        (f := f) hf_convex hf_differentiable
        (xStarSeq := fun k : ℕ => e (gradient f (xSeq (φ k))))
        (xSeq := fun k : ℕ => e (xSeq (φ k)))
        hcofinite hDualSubseqBounded hDualWitness
    have hPrimalSubseqImageBounded :
        Bornology.IsBounded
          (((e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) ''
            Set.range (fun k : ℕ => e (xSeq (φ k))))) :=
      helperForLemma_26_7_boundedImage_of_boundedSet_underContinuousLinearMap
        (L := (e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)))
        hCoordinateSubseqBounded
    have hPrimalSubseqImageEq :
        (((e.symm : (Fin n → ℝ) →L[ℝ] EuclideanSpace ℝ (Fin n)) ''
            Set.range (fun k : ℕ => e (xSeq (φ k))))) =
          Set.range (fun k : ℕ => xSeq (φ k)) := by
      ext y
      constructor
      · rintro ⟨xCoord, hxCoord, rfl⟩
        rcases hxCoord with ⟨k, rfl⟩
        refine ⟨k, ?_⟩
        simp [e]
      · rintro ⟨k, rfl⟩
        exact ⟨e (xSeq (φ k)), ⟨k, rfl⟩, by simp [e]⟩
    have hPrimalSubseqBounded :
        Bornology.IsBounded (Set.range fun k : ℕ => xSeq (φ k)) :=
      hPrimalSubseqImageEq ▸ hPrimalSubseqImageBounded
    have hxSubseqTend :
        Filter.Tendsto (fun k : ℕ => ‖xSeq (φ k)‖) Filter.atTop Filter.atTop :=
      hxTend.comp hφmono.tendsto_atTop
    rcases
        (isBounded_iff_forall_norm_le (s := Set.range fun k : ℕ => xSeq (φ k))).1
          hPrimalSubseqBounded with
      ⟨M, hM⟩
    have hEventuallySmall :
        ∀ᶠ k : ℕ in Filter.atTop, ‖xSeq (φ k)‖ ≤ M :=
      Filter.Eventually.of_forall (fun k => hM _ ⟨k, rfl⟩)
    have hEventuallyLarge :
        ∀ᶠ k : ℕ in Filter.atTop, M + 1 ≤ ‖xSeq (φ k)‖ :=
      (Filter.tendsto_atTop.1 hxSubseqTend) (M + 1)
    have hFalse : ∀ᶠ k : ℕ in Filter.atTop, False :=
      (hEventuallySmall.and hEventuallyLarge).mono (fun _ hk =>
        (not_le_of_gt (lt_add_of_pos_right M zero_lt_one))
          (le_trans hk.2 hk.1))
    rcases Filter.eventually_atTop.mp hFalse with ⟨N, hN⟩
    exact hN N le_rfl
  · intro hSeq
    exact
      helperForLemma_26_7_cofinite_of_gradientNormBlowup
        (f := f) hf_convex hf_differentiable hSeq

end Section26
end Chap05
