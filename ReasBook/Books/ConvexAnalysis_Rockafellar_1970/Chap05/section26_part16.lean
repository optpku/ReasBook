/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part15

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

-- Proof sketch: specialize the definition of Legendre type to
-- `C = int (dom f)`, then combine Corollary 26.3.1 with the auxiliary facts that for a closed
-- proper convex function this interior is open and convex and that `f` is finite on it.
/-- Proposition 26.4.1.5: if `f` is a closed proper convex function on `ℝ^n` and
`C = int (dom f)`, then `∂ f` is one-to-one if and only if the restriction `(C, f|_C)` is of
Legendre type. -/
theorem subdifferential_oneToOne_iff_restriction_isLegendreTypeOn_interior
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    IsOneToOneMultivaluedMap (subdifferentialAt f) ↔ IsLegendreTypeOn C f := by
  intro C
  -- Rewrite Corollary 26.3.1 through the local Legendre-type packaging for `C = int (dom f)`.
  have hpack :
      IsLegendreTypeOn C f ↔
        StrictConvexOn ℝ C (fun x => (f x).toReal) ∧ IsEssentiallySmooth f := by
    simpa [C] using
      (helperForProposition_26_4_1_5_isLegendreTypeOn_interior_iff_strictConvexOn_and_essentiallySmooth
        (f := f) hf)
  rw [hpack]
  exact
    subdifferential_oneToOne_iff_strictConvexOn_interior_and_essentiallySmooth
      (f := f) hf hf_closed

-- Proof sketch: use Proposition 26.4.1.5 on both `f` and `f*`, combine it with Theorem 23.5 to
-- transfer one-to-one subdifferential data across Fenchel conjugation, and then package the
-- resulting unique subgradient selections on `C` and `C*` into mutually inverse Legendre
-- conjugate packages and a homeomorphism between the two interior effective domains.
/-- Theorem 26.5: let `f` be a closed convex function with
`C = int (dom f)` and `C* = int (dom f*)`. Then `(C, f)` is of Legendre type if and only if
`(C*, f*)` is of Legendre type. When this holds, `(C*, f*)` is the Legendre conjugate of
`(C, f)` and conversely; moreover there are unique-subgradient maps `grad` on `C` and `gradStar`
on `C*` whose restrictions define inverse homeomorphisms between `C` and `C*`. -/
theorem legendreTypeOn_interior_iff_conjugate_legendreTypeOn_interior_with_mutualLegendreConjugacy
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f) :
    let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
    let CStar : Set (Fin n → ℝ) :=
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar)
    (IsLegendreTypeOn C f ↔ IsLegendreTypeOn CStar fStar) ∧
      (IsLegendreTypeOn C f →
        ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
          L.target = CStar ∧
          Set.EqOn L.conjFun fStar CStar ∧
          ∃ LStar :
              LegendreConjugatePackageOn
                (fun xStar x : Fin n → ℝ => dotProduct x xStar) CStar fStar,
            LStar.target = C ∧
            Set.EqOn LStar.conjFun f C ∧
            ∃ grad gradStar : (Fin n → ℝ) → (Fin n → ℝ),
              L.toFun = grad ∧
              LStar.toFun = gradStar ∧
              (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
              (∀ ⦃x xStar⦄, x ∈ C →
                dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
                  xStar = grad x) ∧
              (∀ xStar ∈ CStar,
                dotProductEquiv ℝ (Fin n) (gradStar xStar) ∈ subdifferentialAt fStar xStar) ∧
              (∀ ⦃xStar x⦄, xStar ∈ CStar →
                dotProductEquiv ℝ (Fin n) x ∈ subdifferentialAt fStar xStar →
                  x = gradStar xStar) ∧
              ∃ h : {x // x ∈ C} ≃ₜ {xStar // xStar ∈ CStar},
                (∀ x : {x // x ∈ C}, ((h x : {xStar // xStar ∈ CStar}) : Fin n → ℝ) = grad x.1) ∧
                ∀ xStar : {xStar // xStar ∈ CStar},
                  ((h.symm xStar : {x // x ∈ C}) : Fin n → ℝ) = gradStar xStar.1) := by
  intro C fStar CStar
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hconv, hf_closed⟩
  have hneBot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
    intro x
    exact hproper.2.2 x (by simp)
  have hproperStar : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
    simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hfStar : ProperConvexERealFunction (F := (Fin n → ℝ)) fStar :=
    helperForLemma_26_2_properConvexERealFunction hproperStar
  have hconvStar : ConvexFunction fStar := by
    simpa [ConvexFunction] using hproperStar.1
  have hfStar_closed : LowerSemicontinuous fStar := by
    simpa [fStar] using (fenchelConjugate_closedConvex (n := n) (f := f)).1
  have hbiconj : fenchelConjugate n fStar = f := by
    simpa [fStar] using
      fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f)
        hf_closed hconv hneBot
  have hLegendrePack :
      IsLegendreTypeOn C f ↔
        StrictConvexOn ℝ C (fun x => (f x).toReal) ∧ IsEssentiallySmooth f := by
    simpa [C] using
      (helperForProposition_26_4_1_5_isLegendreTypeOn_interior_iff_strictConvexOn_and_essentiallySmooth
        (f := f) hf)
  have hLegendrePackStar :
      IsLegendreTypeOn CStar fStar ↔
        StrictConvexOn ℝ CStar (fun x => (fStar x).toReal) ∧ IsEssentiallySmooth fStar := by
    simpa [CStar, fStar] using
      (helperForProposition_26_4_1_5_isLegendreTypeOn_interior_iff_strictConvexOn_and_essentiallySmooth
        (f := fStar) hfStar)
  -- First rewrite Legendre type through one-to-one subdifferential data on `f` and `f*`.
  have hOneToOneIff :
      IsOneToOneMultivaluedMap (subdifferentialAt f) ↔
        IsOneToOneMultivaluedMap (subdifferentialAt fStar) := by
    constructor
    · intro hOneToOne
      constructor
      · -- The inverse single-valued fibers of `∂ f` become ordinary single-valued fibers of `∂ f*`.
        exact
          (helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
            (f := f) hf hf_closed).1 hOneToOne.2
      · -- Applying the same bridge to `f*` and rewriting `(f*)* = f` recovers injectivity on the dual side.
        have hSingleBiconj :
            IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n fStar)) := by
          simpa [hbiconj] using hOneToOne.1
        exact
          (helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
            (f := fStar) hfStar hfStar_closed).2 hSingleBiconj
    · intro hOneToOneStar
      constructor
      · -- The dual inverse-single-valued clause becomes single-valuedness of `∂((f*)*) = ∂f`.
        have hSingleBiconj :
            IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n fStar)) :=
          (helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
            (f := fStar) hfStar hfStar_closed).1 hOneToOneStar.2
        simpa [hbiconj] using hSingleBiconj
      · -- Ordinary single-valuedness of `∂ f*` transports back to inverse single-valuedness of `∂ f`.
        exact
          (helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
            (f := f) hf hf_closed).2 hOneToOneStar.1
  have hLegendreIff : IsLegendreTypeOn C f ↔ IsLegendreTypeOn CStar fStar := by
    calc
      IsLegendreTypeOn C f ↔ IsOneToOneMultivaluedMap (subdifferentialAt f) := by
        simpa using
          (subdifferential_oneToOne_iff_restriction_isLegendreTypeOn_interior
            (f := f) hf hf_closed).symm
      _ ↔ IsOneToOneMultivaluedMap (subdifferentialAt fStar) := hOneToOneIff
      _ ↔ IsLegendreTypeOn CStar fStar := by
        simpa [fStar, CStar] using
          (subdifferential_oneToOne_iff_restriction_isLegendreTypeOn_interior
            (f := fStar) hfStar hfStar_closed)
  refine ⟨hLegendreIff, ?_⟩
  intro hLeg
  have hLegStar : IsLegendreTypeOn CStar fStar := hLegendreIff.1 hLeg
  have hf_smooth : IsEssentiallySmooth f := (hLegendrePack.1 hLeg).2
  have hfStar_smooth : IsEssentiallySmooth fStar := (hLegendrePackStar.1 hLegStar).2
  have hSubdiffDomainEqC :
      subdifferentialEffectiveDomain f = C := by
    simpa [C] using
      (helperForCorollary_26_3_1_subdifferentialEffectiveDomain_eq_interior_of_essentiallySmooth
        (f := f) hf hf_closed hf_smooth)
  have hSubdiffDomainEqCStar :
      subdifferentialEffectiveDomain fStar = CStar := by
    simpa [CStar, fStar] using
      (helperForCorollary_26_3_1_subdifferentialEffectiveDomain_eq_interior_of_essentiallySmooth
        (f := fStar) hfStar hfStar_closed hfStar_smooth)
  rcases hLeg with ⟨hC_nonempty, _hC_open, _hC_convex, hC_finite, _hC_strict, hSmoothOn⟩
  rcases hSmoothOn with ⟨hproperC, gradWitness, hgradWitnessMem, hgradWitnessUnique, _hgradBlowup⟩
  -- On a Legendre-type pair, the local unique subgradient witness produces differentiability on `C`.
  have hdiff : ∀ x ∈ C, ERealDifferentiableAt f x := by
    intro x hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      constructor
      · exact hC_finite x hx
      · exact hproperC.2.2 x hx
    refine
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hconv x hxFinite).2 ?_
    refine ⟨gradWitness x, ?_, ?_⟩
    · exact hgradWitnessMem x hx
    · intro y hy
      exact hgradWitnessUnique hx hy
  let grad : (Fin n → ℝ) → (Fin n → ℝ) := interiorGradientMap f hdiff
  have hGradMem :
      ∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x := by
    intro x hx
    simpa [grad, C] using
      (helperForText_26_4_1_2_interiorGradient_mem_subdifferentialAt
        (f := f) (hf := hf) (hdiff := hdiff) hx)
  have hGradUnique :
      ∀ {x xStar}, x ∈ C →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x := by
    intro x xStar hx hxSub
    simpa [grad, C] using
      (helperForText_26_4_1_2_subgradient_eq_interiorGradient
        (f := f) (hf := hf) (hdiff := hdiff) hx hxSub)
  have hGradImageRaw :
      subdifferentialEffectiveDomain fStar = grad '' C := by
    simpa [grad, C, fStar] using
      (helperForText_26_4_1_2_subdifferentialEffectiveDomain_eq_interiorGradientImage
        (f := f) (hf := hf) (hf_closed := hf_closed) (hf_smooth := hf_smooth) (hdiff := hdiff))
  have hGradImage : CStar = grad '' C := by
    rw [← hSubdiffDomainEqCStar]
    exact hGradImageRaw
  have hGradCont :
      Continuous (fun x : {x // x ∈ C} => grad x) := by
    simpa [grad, C] using
      (helperForText_26_4_1_2_interiorGradient_continuousOn_interior
        (f := f) (hf := hf) (hdiff := hdiff))
  have hPrimalPackage :
      ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
        L.toFun = grad ∧
        L.target = grad '' C ∧
        Set.EqOn L.conjFun fStar L.target := by
    rcases
        (show
          ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
            L.toFun = grad ∧
            L.target = grad '' C ∧
            Set.EqOn L.conjFun fStar L.target ∧
            L.target ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar from by
          simpa [C, fStar, grad] using
            closedProperConvex_has_legendreConjugatePackageOn_interior_eq_fenchelConjugate
              (f := f) hf hf_closed hC_nonempty hdiff) with
      ⟨L, hLfun, hLtarget, hLconj, _hLsubset⟩
    exact ⟨L, hLfun, hLtarget, hLconj⟩
  rcases hPrimalPackage with ⟨L, hLfun, hLtargetRaw, hLconjRaw⟩
  have hLtarget : L.target = CStar := by
    calc
      L.target = grad '' C := hLtargetRaw
      _ = CStar := hGradImage.symm
  have hLconj : Set.EqOn L.conjFun fStar CStar := by
    intro x hx
    have hxTarget : x ∈ L.target := by
      simpa [hLtarget] using hx
    exact hLconjRaw hxTarget
  rcases hLegStar with
    ⟨hCStar_nonempty, _hCStar_open, _hCStar_convex, hCStar_finite, _hCStar_strict, hSmoothOnStar⟩
  rcases hSmoothOnStar with
    ⟨hproperCStar, gradStarWitness, hgradStarWitnessMem, hgradStarWitnessUnique, _hgradStarBlowup⟩
  -- The same local-differentiability construction applies to the conjugate side.
  have hdiffStar : ∀ x ∈ CStar, ERealDifferentiableAt fStar x := by
    intro x hx
    have hxFinite : fStar x ≠ ⊤ ∧ fStar x ≠ ⊥ := by
      constructor
      · exact hCStar_finite x hx
      · exact hproperCStar.2.2 x hx
    refine
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        fStar hconvStar x hxFinite).2 ?_
    refine ⟨gradStarWitness x, ?_, ?_⟩
    · exact hgradStarWitnessMem x hx
    · intro y hy
      exact hgradStarWitnessUnique hx hy
  let gradStar : (Fin n → ℝ) → (Fin n → ℝ) := interiorGradientMap fStar hdiffStar
  have hGradStarMem :
      ∀ xStar ∈ CStar,
        dotProductEquiv ℝ (Fin n) (gradStar xStar) ∈ subdifferentialAt fStar xStar := by
    intro xStar hxStar
    simpa [gradStar, CStar] using
      (helperForText_26_4_1_2_interiorGradient_mem_subdifferentialAt
        (f := fStar) (hf := hfStar) (hdiff := hdiffStar) hxStar)
  have hGradStarUnique :
      ∀ {xStar x}, xStar ∈ CStar →
        dotProductEquiv ℝ (Fin n) x ∈ subdifferentialAt fStar xStar →
          x = gradStar xStar := by
    intro xStar x hxStar hxSub
    simpa [gradStar, CStar] using
      (helperForText_26_4_1_2_subgradient_eq_interiorGradient
        (f := fStar) (hf := hfStar) (hdiff := hdiffStar) hxStar hxSub)
  have hGradStarImageRaw :
      subdifferentialEffectiveDomain (fenchelConjugate n fStar) = gradStar '' CStar := by
    simpa [gradStar, CStar] using
      (helperForText_26_4_1_2_subdifferentialEffectiveDomain_eq_interiorGradientImage
        (f := fStar) (hf := hfStar) (hf_closed := hfStar_closed)
        (hf_smooth := hfStar_smooth) (hdiff := hdiffStar))
  have hGradStarImage : C = gradStar '' CStar := by
    rw [← hSubdiffDomainEqC]
    simpa [hbiconj] using hGradStarImageRaw
  have hGradStarCont :
      Continuous (fun xStar : {xStar // xStar ∈ CStar} => gradStar xStar) := by
    simpa [gradStar, CStar] using
      (helperForText_26_4_1_2_interiorGradient_continuousOn_interior
        (f := fStar) (hf := hfStar) (hdiff := hdiffStar))
  have hDualPackage :
      ∃ LStar :
          LegendreConjugatePackageOn
            (fun xStar x : Fin n → ℝ => dotProduct x xStar) CStar fStar,
        LStar.toFun = gradStar ∧
        LStar.target = gradStar '' CStar ∧
        Set.EqOn LStar.conjFun (fenchelConjugate n fStar) LStar.target := by
    rcases
        (show
          ∃ LStarRaw :
              LegendreConjugatePackageOn
                (fun xStar x : Fin n → ℝ => dotProduct xStar x) CStar fStar,
            LStarRaw.toFun = gradStar ∧
            LStarRaw.target = gradStar '' CStar ∧
            Set.EqOn LStarRaw.conjFun (fenchelConjugate n fStar) LStarRaw.target ∧
            LStarRaw.target ⊆
              effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n fStar) from by
          simpa [CStar, gradStar] using
            closedProperConvex_has_legendreConjugatePackageOn_interior_eq_fenchelConjugate
              (f := fStar) hfStar hfStar_closed hCStar_nonempty hdiffStar) with
      ⟨LStarRaw, hLStarRawFun, hLStarRawTarget, hLStarRawConj, _hLStarRawSubset⟩
    -- Commute the Euclidean pairing so the dual package matches the theorem statement exactly.
    have hLStarFiber :
        ∀ ⦃xStar₁ xStar₂ x⦄,
          xStar₁ ∈ CStar →
          xStar₂ ∈ CStar →
          LStarRaw.toFun xStar₁ = x →
          LStarRaw.toFun xStar₂ = x →
          ((((fun xStar x : Fin n → ℝ => dotProduct x xStar) xStar₁ x : ℝ) : EReal) - fStar xStar₁) =
            ((((fun xStar x : Fin n → ℝ => dotProduct x xStar) xStar₂ x : ℝ) : EReal) - fStar xStar₂) := by
      intro xStar₁ xStar₂ x hxStar₁ hxStar₂ hx₁ hx₂
      simpa [dotProduct_comm] using
        LStarRaw.fiber_well_defined hxStar₁ hxStar₂ hx₁ hx₂
    have hLStarValue :
        ∀ ⦃xStar⦄, xStar ∈ CStar →
          LStarRaw.conjFun (LStarRaw.toFun xStar) =
            ((((fun xStar x : Fin n → ℝ => dotProduct x xStar) xStar (LStarRaw.toFun xStar) : ℝ) :
              EReal) - fStar xStar) := by
      intro xStar hxStar
      simpa [dotProduct_comm] using LStarRaw.value_eq hxStar
    let LStar :
        LegendreConjugatePackageOn
          (fun xStar x : Fin n → ℝ => dotProduct x xStar) CStar fStar :=
      { target := LStarRaw.target
        conjFun := LStarRaw.conjFun
        toFun := LStarRaw.toFun
        image_eq := LStarRaw.image_eq
        fiber_well_defined := hLStarFiber
        value_eq := hLStarValue }
    have hLStarFun : LStar.toFun = gradStar := hLStarRawFun
    have hLStarTarget : LStar.target = gradStar '' CStar := hLStarRawTarget
    have hLStarConj : Set.EqOn LStar.conjFun (fenchelConjugate n fStar) LStar.target := hLStarRawConj
    exact ⟨LStar, hLStarFun, hLStarTarget, hLStarConj⟩
  rcases hDualPackage with ⟨LStar, hLStarFun, hLStarTargetRaw, hLStarConjRaw⟩
  have hLStarTarget : LStar.target = C := by
    calc
      LStar.target = gradStar '' CStar := hLStarTargetRaw
      _ = C := hGradStarImage.symm
  have hLStarConj : Set.EqOn LStar.conjFun f C := by
    intro x hx
    have hxTarget : x ∈ LStar.target := by
      simpa [hLStarTarget] using hx
    calc
      LStar.conjFun x = fenchelConjugate n fStar x := hLStarConjRaw hxTarget
      _ = f x := by simp [hbiconj]
  -- The primal and dual gradients land in the opposite interior domains by the image identities.
  have hGradMapsToCStar : ∀ x : {x // x ∈ C}, grad x.1 ∈ CStar := by
    intro x
    have hxImage : grad x.1 ∈ grad '' C := by
      exact ⟨x.1, x.2, rfl⟩
    simpa [hGradImage] using hxImage
  have hGradStarMapsToC : ∀ xStar : {xStar // xStar ∈ CStar}, gradStar xStar.1 ∈ C := by
    intro xStar
    have hxImage : gradStar xStar.1 ∈ gradStar '' CStar := by
      exact ⟨xStar.1, xStar.2, rfl⟩
    simpa [hGradStarImage] using hxImage
  let toDual : {x // x ∈ C} → {xStar // xStar ∈ CStar} :=
    fun x => ⟨grad x.1, hGradMapsToCStar x⟩
  let toPrimal : {xStar // xStar ∈ CStar} → {x // x ∈ C} :=
    fun xStar => ⟨gradStar xStar.1, hGradStarMapsToC xStar⟩
  have hToPrimalLeft : Function.LeftInverse toPrimal toDual := by
    intro x
    apply Subtype.ext
    have hxPrimalSub :
        dotProductEquiv ℝ (Fin n) (grad x.1) ∈ subdifferentialAt f x.1 :=
      hGradMem x.1 x.2
    have hxPrimalEuclidean :
        IsEuclideanSubgradientAt f x.1 (grad x.1) := by
      simpa [IsEuclideanSubgradientAt] using hxPrimalSub
    have hxDualEuclidean :
        IsEuclideanSubgradientAt fStar (grad x.1) x.1 :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x.1 (grad x.1)).2 hxPrimalEuclidean
    have hxDualSub :
        dotProductEquiv ℝ (Fin n) x.1 ∈ subdifferentialAt fStar (grad x.1) := by
      simpa [fStar, IsEuclideanSubgradientAt] using hxDualEuclidean
    have hxGrad : grad x.1 ∈ CStar := hGradMapsToCStar x
    have hxEq : x.1 = gradStar (grad x.1) :=
      hGradStarUnique hxGrad hxDualSub
    exact hxEq.symm
  have hToDualRight : Function.RightInverse toPrimal toDual := by
    intro xStar
    apply Subtype.ext
    have hxDualSub :
        dotProductEquiv ℝ (Fin n) (gradStar xStar.1) ∈ subdifferentialAt fStar xStar.1 :=
      hGradStarMem xStar.1 xStar.2
    have hxDualEuclidean :
        IsEuclideanSubgradientAt fStar xStar.1 (gradStar xStar.1) := by
      simpa [IsEuclideanSubgradientAt] using hxDualSub
    have hxPrimalEuclidean :
        IsEuclideanSubgradientAt f (gradStar xStar.1) xStar.1 :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper (gradStar xStar.1) xStar.1).1
        (by simpa [fStar] using hxDualEuclidean)
    have hxPrimalSub :
        dotProductEquiv ℝ (Fin n) xStar.1 ∈ subdifferentialAt f (gradStar xStar.1) := by
      simpa [IsEuclideanSubgradientAt] using hxPrimalEuclidean
    have hxGradStar : gradStar xStar.1 ∈ C := hGradStarMapsToC xStar
    have hxEq : xStar.1 = grad (gradStar xStar.1) :=
      hGradUnique hxGradStar hxPrimalSub
    exact hxEq.symm
  have hToDualCont : Continuous toDual := by
    simpa [toDual] using hGradCont.subtype_mk hGradMapsToCStar
  have hToPrimalCont : Continuous toPrimal := by
    simpa [toPrimal] using hGradStarCont.subtype_mk hGradStarMapsToC
  let hEquiv : {x // x ∈ C} ≃ {xStar // xStar ∈ CStar} :=
    { toFun := toDual
      invFun := toPrimal
      left_inv := hToPrimalLeft
      right_inv := hToDualRight }
  let hHomeomorph : {x // x ∈ C} ≃ₜ {xStar // xStar ∈ CStar} :=
    { toEquiv := hEquiv
      continuous_toFun := hToDualCont
      continuous_invFun := hToPrimalCont }
  have hHomeomorphApply :
      ∀ x : {x // x ∈ C},
        ((hHomeomorph x : {xStar // xStar ∈ CStar}) : Fin n → ℝ) = grad x.1 := by
    intro x
    rfl
  have hHomeomorphSymmApply :
      ∀ xStar : {xStar // xStar ∈ CStar},
        ((hHomeomorph.symm xStar : {x // x ∈ C}) : Fin n → ℝ) = gradStar xStar.1 := by
    intro xStar
    rfl
  -- Package the primal/dual gradient data into the theorem's nested existential form.
  refine ⟨L, hLtarget, hLconj, LStar, hLStarTarget, hLStarConj,
    grad, gradStar, hLfun, hLStarFun, hGradMem, ?_, hGradStarMem, ?_, ?_⟩
  · intro x xStar hx hxSub
    exact hGradUnique hx hxSub
  · intro xStar x hxStar hxSub
    exact hGradStarUnique hxStar hxSub
  · refine ⟨hHomeomorph, hHomeomorphApply, hHomeomorphSymmApply⟩

end Section26
end Chap05
