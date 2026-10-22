/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part17

section Chap05
section Section26

attribute [local instance] Classical.propDecidable

/-- The Chapter 13 co-finiteness predicate for the standard `EReal` lift of a real-valued
convex function on `ℝ^n`. -/
abbrev IsCofiniteFiniteConvexFunction {n : ℕ} (f : (Fin n → ℝ) → ℝ) : Prop :=
  CoFiniteConvexFunction (fun x => (f x : EReal))

/-- Helper for Text 26.5.0.2: transporting a finite convex function on `ℝ^n` through the
`WithLp` identification yields a proper convex `EReal`-valued lift on the whole space. -/
lemma helperForText_26_5_0_2_properLift {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ))
      (fun x => (f x : EReal)) := by
  let fEuclidean : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x
  let toFunctionLin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin n → ℝ)).toLinearMap
  -- Reinterpret the same formula on the Euclidean-space model of `ℝ^n`.
  have hfEuclidean_convex :
      ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) fEuclidean := by
    have hfEuclidean_convex' :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (Fin n → ℝ))) (f := f) hf_convex toFunctionLin
    simpa [fEuclidean, toFunctionLin, WithLp.coe_linearEquiv] using hfEuclidean_convex'
  -- Section 10 already proves properness for the transported `EReal` lift.
  simpa [fEuclidean] using
    (Section10.properConvexFunctionOn_univ_coe_comp_toLp_of_convexOn
      (n := n) (f := fEuclidean) hfEuclidean_convex)

/-- Helper for Text 26.5.0.2: the standard `EReal` lift of a finite convex function on `ℝ^n`
is closed convex. -/
lemma helperForText_26_5_0_2_closedLift {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    ClosedConvexFunction (fun x => (f x : EReal)) := by
  let fEuclidean : EuclideanSpace ℝ (Fin n) → ℝ := fun x => f x
  let toFunctionLin : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (Fin n → ℝ) :=
    (WithLp.linearEquiv (p := (2 : ENNReal)) (K := ℝ) (V := Fin n → ℝ)).toLinearMap
  -- Reinterpret convexity on the Euclidean-space presentation used by Section 10.
  have hfEuclidean_convex :
      ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) fEuclidean := by
    have hfEuclidean_convex' :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (Fin n → ℝ))) (f := f) hf_convex toFunctionLin
    simpa [fEuclidean, toFunctionLin, WithLp.coe_linearEquiv] using hfEuclidean_convex'
  -- The Chapter 10 transport theorem then gives closed convexity of the standard lift.
  simpa [fEuclidean] using
    (Section10.closedConvexFunction_coe_comp_toLp_of_convexOn
      (n := n) (f := fEuclidean) hfEuclidean_convex)

-- Proof sketch: pass from the finite convex function `f` to its standard `EReal` lift on
-- `ℝ^n`, use finite convexity on the whole space to obtain the closed convex hypotheses needed
-- for Corollary 13.3.1, and then rewrite the conclusion in terms of the helper predicate above.
/-- Text 26.5.0.2: a finite convex function `f` on `ℝ^n` is co-finite exactly when its epigraph
contains no non-vertical half-lines, equivalently when its recession function takes the value
`+∞` on every nonzero direction; by Corollary 13.3.1, this occurs precisely when the Fenchel
conjugate of the standard `EReal` lift of `f` is finite everywhere, i.e.
`dom f* = ℝ^n`. -/
theorem isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere {n : ℕ}
    (f : (Fin n → ℝ) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) f) :
    IsCofiniteFiniteConvexFunction f ↔
      (effectiveDomain (Set.univ : Set (Fin n → ℝ))
          (fenchelConjugate n (fun x => (f x : EReal))) = Set.univ ∧
        ∀ xStar : Fin n → ℝ,
          fenchelConjugate n (fun x => (f x : EReal)) xStar ≠ (⊥ : EReal)) := by
  -- First package the real-valued convex function as a closed convex `EReal` lift.
  have hclosed : ClosedConvexFunction (fun x => (f x : EReal)) :=
    helperForText_26_5_0_2_closedLift f hf_convex
  -- Then Corollary 13.3.1 is exactly the desired equivalence after unfolding the abbreviation.
  simpa [IsCofiniteFiniteConvexFunction] using
    (effectiveDomain_fenchelConjugate_eq_univ_iff_coFinite
      (n := n) (f := fun x => (f x : EReal)) hclosed).symm

/-- The inverse-gradient Legendre conjugate candidate attached to a differentiable convex function
on `ℝ^n`. -/
noncomputable def gradientLegendreConjugate {n : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun xStar =>
    let x := Function.invFun (gradient f) xStar
    dotProduct (fun i => x i) (fun i => xStar i) - f x

/-- Helper for Theorem 26.6: the standard coordinate lift of a differentiable convex function on
`ℝ^n` is proper, closed, everywhere differentiable, and essentially smooth on the whole space. -/
lemma helperForTheorem_26_6_coordinateLiftPackage
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
      LowerSemicontinuous F ∧
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
      (∀ x : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F x,
        erealGradientAt hDiff = euclideanGradientAt fFin x) ∧
      IsEssentiallySmooth F := by
  intro fFin F
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Transport convexity through the coordinate equivalence to work in `Fin n → ℝ`.
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hproperOn :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForText_26_5_0_2_properLift fFin hfFin_convex
  have hproper : ProperConvexERealFunction (F := (Fin n → ℝ)) F :=
    helperForTheorem_21_3_properConvexEReal_of_properConvexFunctionOn_univ F hproperOn
  have hclosed : LowerSemicontinuous F :=
    (helperForText_26_5_0_2_closedLift fFin hfFin_convex).2
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hfFin_differentiable : Differentiable ℝ fFin := by
    -- Differentiability is preserved by the linear coordinate change.
    simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
  have hgradWitnessRaw :
      ∀ x : Fin n → ℝ,
        ∃ hDiff : ERealDifferentiableAt
            (fun y => (fFin y : EReal) + indicatorFunction Set.univ y) x,
        erealGradientAt hDiff = euclideanGradientAt fFin x := by
    intro x
    have hdiffAt : DifferentiableAt ℝ fFin x := hfFin_differentiable.differentiableAt
    -- Corollary 25.5.1 identifies the `EReal` lift gradient with the Euclidean gradient.
    rcases
        (helperForCorollary_25_5_1_extension_differentiableAt_and_gradient_eq
          (hCopen := isOpen_univ) (C := (Set.univ : Set (Fin n → ℝ)))
          (f := fFin) (x := x) (by simp) hdiffAt) with
      ⟨hDiff, hEq⟩
    exact ⟨hDiff, hEq⟩
  have hgradWitness :
      ∀ x : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F x,
        erealGradientAt hDiff = euclideanGradientAt fFin x := by
    intro x
    rcases hgradWitnessRaw x with ⟨hDiff, hEq⟩
    have hDiffF : ERealDifferentiableAt F x := by
      simpa [F, indicatorFunction] using hDiff
    have hgradEqF : erealGradientAt hDiffF = erealGradientAt hDiff := by
      exact
        erealGradient_unique
          (ERealDifferentiableAt.eventually_finiteValuedWithin_punctured hDiffF)
          (ERealDifferentiableAt.hasERealGradientAt hDiffF)
          (by simpa [F, indicatorFunction] using ERealDifferentiableAt.hasERealGradientAt hDiff)
    exact ⟨hDiffF, hgradEqF.trans hEq⟩
  choose hdiffAll hgradEq using hgradWitness
  have hdom : effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ := by
    -- Finiteness at every point collapses the effective domain to all of `ℝ^n`.
    ext x
    constructor
    · intro hx
      simp
    · intro hx
      rw [effectiveDomain_eq]
      refine ⟨by simp, ?_⟩
      exact lt_top_iff_ne_top.mpr (ERealDifferentiableAt.finiteAt (hdiffAll x)).1
  have hsmooth :
      IsEssentiallySmooth F := by
    -- The Chapter 26 global packaging converts everywhere differentiability into essential
    -- smoothness once properness and convexity are available.
    exact
      (helperForText_26_3_3_2_closedProper_and_essentiallySmooth_of_convex_and_everywhereDifferentiable
        hconv hdiffAll).2.2
  exact ⟨hproper, hclosed, hdom, (fun x => ⟨hdiffAll x, hgradEq x⟩), hsmooth⟩

/-- Helper for Theorem 26.6: after lifting to coordinates, injectivity of the Euclidean gradient
is exactly one-to-one-ness of the subdifferential multivalued map. -/
lemma helperForTheorem_26_6_gradientInjective_iff_subdifferentialOneToOne
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    Function.Injective (gradient f) ↔ IsOneToOneMultivaluedMap (subdifferentialAt F) := by
  intro fFin F
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  rcases helperForTheorem_26_6_coordinateLiftPackage
      (f := f) hf_convex hf_differentiable with
    ⟨hproper, hclosed, _hdom, hgradWitness, hsmooth⟩
  choose hdiffAll hgradEq using hgradWitness
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hsingle :
      IsSingleValuedMultivaluedMap (subdifferentialAt F) :=
    (subdifferential_singleValued_iff_essentiallySmooth
      (f := F) hproper hclosed).1.2 hsmooth
  have hfFin_differentiable : Differentiable ℝ fFin := by
    -- Reuse the transported differentiability to compare the Euclidean and coordinate gradients.
    simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
  constructor
  · intro hInjective
    refine ⟨hsingle, ?_⟩
    intro xStar x hx y hy
    have hxPre :
        (dotProductEquiv ℝ (Fin n)).symm xStar ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F x) := by
      simpa [subdifferentialAt] using hx
    have hyPre :
        (dotProductEquiv ℝ (Fin n)).symm xStar ∈
          ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F y) := by
      simpa [subdifferentialAt] using hy
    have hxGrad :
        (dotProductEquiv ℝ (Fin n)).symm xStar = euclideanGradientAt fFin x := by
      calc
        (dotProductEquiv ℝ (Fin n)).symm xStar = erealGradientAt (hdiffAll x) := by
          exact helperForTheorem_25_5_subgradientPreimage_eq_gradient
            (f := F) hconv (x := x) (hdiffAll x) hxPre
        _ = euclideanGradientAt fFin x := hgradEq x
    have hyGrad :
        (dotProductEquiv ℝ (Fin n)).symm xStar = euclideanGradientAt fFin y := by
      calc
        (dotProductEquiv ℝ (Fin n)).symm xStar = erealGradientAt (hdiffAll y) := by
          exact helperForTheorem_25_5_subgradientPreimage_eq_gradient
            (f := F) hconv (x := y) (hdiffAll y) hyPre
        _ = euclideanGradientAt fFin y := hgradEq y
    have hgradEqEuclid :
        gradient f (e.symm x) = gradient f (e.symm y) := by
      have hcoordEq :
          e (gradient f (e.symm x)) = e (gradient f (e.symm y)) := by
        calc
          e (gradient f (e.symm x)) = euclideanGradientAt fFin x := by
            simpa [fFin, e] using
              (helperForText_26_4_0_2_sourceGradient_transport
                (f := fFin) (x := x) hfFin_differentiable.differentiableAt)
          _ = (dotProductEquiv ℝ (Fin n)).symm xStar := hxGrad.symm
          _ = euclideanGradientAt fFin y := hyGrad
          _ = e (gradient f (e.symm y)) := by
            simpa [fFin, e] using
              (helperForText_26_4_0_2_sourceGradient_transport
                (f := fFin) (x := y) hfFin_differentiable.differentiableAt).symm
      exact e.injective hcoordEq
    have hxyEuclid : e.symm x = e.symm y := hInjective hgradEqEuclid
    exact e.symm.injective hxyEuclid
  · intro hOneToOne
    intro x y hxy
    have hxSub :
        dotProductEquiv ℝ (Fin n) (euclideanGradientAt fFin (e x)) ∈
          subdifferentialAt F (e x) := by
      have hpre :
          erealGradientAt (hdiffAll (e x)) ∈
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F (e x)) :=
        helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
          (f := F) hconv (x := e x) (hdiffAll (e x))
      have hpre' :
          euclideanGradientAt fFin (e x) ∈
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F (e x)) := by
        simpa [hgradEq (e x)] using hpre
      simpa [subdifferentialAt] using hpre'
    have hySub :
        dotProductEquiv ℝ (Fin n) (euclideanGradientAt fFin (e y)) ∈
          subdifferentialAt F (e y) := by
      have hpre :
          erealGradientAt (hdiffAll (e y)) ∈
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F (e y)) :=
        helperForTheorem_25_5_gradient_mem_subdifferentialPreimage
          (f := F) hconv (x := e y) (hdiffAll (e y))
      have hpre' :
          euclideanGradientAt fFin (e y) ∈
            ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F (e y)) := by
        simpa [hgradEq (e y)] using hpre
      simpa [subdifferentialAt] using hpre'
    have hxCoord :
        e (gradient f x) = euclideanGradientAt fFin (e x) := by
      simpa [fFin, e] using
        (helperForText_26_4_0_2_sourceGradient_transport
          (f := fFin) (x := e x) hfFin_differentiable.differentiableAt)
    have hyCoord :
        e (gradient f y) = euclideanGradientAt fFin (e y) := by
      simpa [fFin, e] using
        (helperForText_26_4_0_2_sourceGradient_transport
          (f := fFin) (x := e y) hfFin_differentiable.differentiableAt)
    have hcoordEq :
        euclideanGradientAt fFin (e x) = euclideanGradientAt fFin (e y) := by
      calc
        euclideanGradientAt fFin (e x) = e (gradient f x) := hxCoord.symm
        _ = e (gradient f y) := by simpa using congrArg e hxy
        _ = euclideanGradientAt fFin (e y) := hyCoord
    have hdualEq :
        dotProductEquiv ℝ (Fin n) (euclideanGradientAt fFin (e x)) =
          dotProductEquiv ℝ (Fin n) (euclideanGradientAt fFin (e y)) := by
      exact congrArg (dotProductEquiv ℝ (Fin n)) hcoordEq
    have hxyFin : e x = e y := by
      exact hOneToOne.2 _ (hdualEq ▸ hxSub) hySub
    exact e.injective hxyFin

/-- Helper for Theorem 26.6: strict convexity is invariant under the standard coordinate
identification between `EuclideanSpace ℝ (Fin n)` and `Fin n → ℝ`. -/
lemma helperForTheorem_26_6_strictConvex_transport_univ
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    StrictConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f ↔
      StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
  intro fFin
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  constructor
  · intro hStrict
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hxy' : e.symm x ≠ e.symm y := by
      intro hEq
      apply hxy
      exact e.symm.injective hEq
    -- Transport the strict inequality through the linear coordinate equivalence.
    have hcore :=
      hStrict.2 (x := e.symm x) (by simp) (y := e.symm y) (by simp) hxy' ha hb hab
    simpa [fFin, e.map_add, e.map_smul, add_comm, add_left_comm, add_assoc] using hcore
  · intro hStrict
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have hxy' : e x ≠ e y := by
      intro hEq
      apply hxy
      exact e.injective hEq
    -- The converse direction is the same argument with the equivalence reversed.
    have hcore :=
      hStrict.2 (x := e x) (by simp) (y := e y) (by simp) hxy' ha hb hab
    simpa [fFin, e.map_add, e.map_smul, add_comm, add_left_comm, add_assoc] using hcore

/-- Helper for Theorem 26.6: once the gradient is injective, Theorem 26.5 identifies the
whole-space gradient image with the interior effective domain of the Fenchel conjugate. -/
lemma helperForTheorem_26_6_gradientImage_eq_interior_conjugateDomain_univ
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hInjective : Function.Injective (gradient f)) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) =
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) := by
  intro fFin F
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ x : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F x,
          erealGradientAt hDiff = euclideanGradientAt fFin x) ∧
        IsEssentiallySmooth F := by
    simpa [fFin, F] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with
    ⟨hproper, hclosed, hdom, hgradWitness, hsmooth⟩
  choose hdiffAll hgradEq using hgradWitness
  have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
    helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
  have hconv : ConvexFunction F := by
    simpa [ConvexFunction] using hproperOn.1
  have hInjectiveBridge :
      Function.Injective (gradient f) ↔ IsOneToOneMultivaluedMap (subdifferentialAt F) := by
    simpa [fFin, F] using
      (helperForTheorem_26_6_gradientInjective_iff_subdifferentialOneToOne
        (f := f) hf_convex hf_differentiable)
  have hInjectiveSubdiff :
      IsOneToOneMultivaluedMap (subdifferentialAt F) := by
    -- The already-proved bridge turns gradient injectivity into injectivity of `∂F`.
    exact hInjectiveBridge.1 hInjective
  have hLegendreInterior :
      IsLegendreTypeOn
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F := by
    -- Proposition 26.4.1.5 packages the injective subdifferential as whole-space Legendre type.
    exact
      (subdifferential_oneToOne_iff_restriction_isLegendreTypeOn_interior
        (f := F) hproper hclosed).1 hInjectiveSubdiff
  have hLegendrePackageRaw :=
    legendreTypeOn_interior_iff_conjugate_legendreTypeOn_interior_with_mutualLegendreConjugacy
      (f := F) hproper hclosed
  have hLegendrePackage :=
    hLegendrePackageRaw.2
      (show
        IsLegendreTypeOn
          (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F from by
          simpa [hdom] using hLegendreInterior)
  rcases hLegendrePackage with
    ⟨L, hLtarget, _hLconj, _LStar, _hLStarTarget, _hLStarConj,
      grad, _gradStar, hLfun, _hLStarFun, hGradMem, _hGradUnique,
      _hGradStarMem, _hGradStarUnique, _hHomeomorphPkg⟩
  have hAbstractGradEq :
      ∀ x : Fin n → ℝ, grad x = euclideanGradientAt fFin x := by
    intro x
    have hxSub :
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt F x := by
      exact hGradMem x (by simpa [hdom])
    have hxPre :
        grad x ∈ ((dotProductEquiv ℝ (Fin n)) ⁻¹' subdifferentialAt F x) := by
      simpa [subdifferentialAt] using hxSub
    -- Uniqueness of the gradient identifies the abstract Legendre selector with `∇f`.
    calc
      grad x = erealGradientAt (hdiffAll x) := by
        exact
          helperForTheorem_25_5_subgradientPreimage_eq_gradient
            (f := F) hconv (x := x) (hdiffAll x) hxPre
      _ = euclideanGradientAt fFin x := hgradEq x
  have hLfunEq : ∀ x : Fin n → ℝ, L.toFun x = grad x := by
    intro x
    simpa [hLfun]
  -- Theorem 26.5 now upgrades the abstract target equality to the concrete gradient image.
  calc
    euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) =
        grad '' (Set.univ : Set (Fin n → ℝ)) := by
          ext xStar
          constructor
          · intro hxStar
            rcases hxStar with ⟨x, _, rfl⟩
            exact ⟨x, by simp, hAbstractGradEq x⟩
          · intro hxStar
            rcases hxStar with ⟨x, _, rfl⟩
            exact ⟨x, by simp, (hAbstractGradEq x).symm⟩
    _ = grad '' interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) := by
          simpa [hdom]
    _ = L.toFun '' interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F) := by
          ext xStar
          constructor
          · intro hxStar
            rcases hxStar with ⟨x, hx, rfl⟩
            exact ⟨x, hx, hLfunEq x⟩
          · intro hxStar
            rcases hxStar with ⟨x, hx, rfl⟩
            exact ⟨x, hx, (hLfunEq x).symm⟩
    _ = L.target := L.image_eq.symm
    _ = interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) :=
          hLtarget

/-- Helper for Theorem 26.6: the remaining primal equivalence asks for the gradient-image to be
identified with the interior of the dual effective domain, so that surjectivity becomes
co-finiteness via Chapter 13. -/
lemma helperForTheorem_26_6_bijective_iff_strictConvex_and_cofinite
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    Function.Bijective (gradient f) ↔
      StrictConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f ∧
        IsCofiniteFiniteConvexFunction fFin := by
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
    simpa [fFin, F] using
      helperForTheorem_26_6_coordinateLiftPackage
        (f := f) hf_convex hf_differentiable
  rcases hcoordPackage with
    ⟨hproper, hclosed, hdom, _hgradWitness, hsmooth⟩
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hInjectiveIff :
      Function.Injective (gradient f) ↔ IsOneToOneMultivaluedMap (subdifferentialAt F) := by
    simpa [fFin, F] using
      (helperForTheorem_26_6_gradientInjective_iff_subdifferentialOneToOne
        (f := f) hf_convex hf_differentiable)
  have hStrictIff :
      IsOneToOneMultivaluedMap (subdifferentialAt F) ↔
        StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Corollary 26.3.1 collapses to the whole-space strict convexity criterion because `dom F = univ`.
    have hcore :=
      subdifferential_oneToOne_iff_strictConvexOn_interior_and_essentiallySmooth
        (f := F) hproper hclosed
    constructor
    · intro hOneToOne
      have hPair := hcore.1 hOneToOne
      simpa [F, hdom] using hPair.1
    · intro hStrict
      exact
        hcore.2 (by
          refine ⟨?_, hsmooth⟩
          simpa [F, hdom] using hStrict)
  constructor
  · intro hbij
    have hStrictFin : StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin :=
      hStrictIff.1 (hInjectiveIff.1 hbij.1)
    have hStrict :
        StrictConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f := by
      exact (helperForTheorem_26_6_strictConvex_transport_univ (f := f)).2 hStrictFin
    have hImage :
        euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) =
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) := by
      exact
        helperForTheorem_26_6_gradientImage_eq_interior_conjugateDomain_univ
          (f := f) hf_convex hf_differentiable hbij.1
    have hfFin_differentiable : Differentiable ℝ fFin := by
      simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
    have hGradImageUniv :
        euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) = Set.univ := by
      ext xStar
      constructor
      · intro _hxStar
        simp
      · intro _hxStar
        rcases hbij.2 (e.symm xStar) with ⟨x, hx⟩
        refine ⟨e x, by simp, ?_⟩
        calc
          euclideanGradientAt fFin (e x) = e (gradient f x) := by
            simpa [fFin, e] using
              (helperForText_26_4_0_2_sourceGradient_transport
                (f := fFin) (x := e x) hfFin_differentiable.differentiableAt).symm
          _ = e (e.symm xStar) := by rw [hx]
          _ = xStar := by simp
    have hInteriorConj :
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) =
          Set.univ := by
      calc
        interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) =
            euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) := hImage.symm
        _ = Set.univ := hGradImageUniv
    have hdomConj :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ := by
      ext xStar
      constructor
      · intro _hxStar
        simp
      · intro _hxStar
        have hxInterior :
            xStar ∈
              interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) := by
          simpa [hInteriorConj]
        exact interior_subset hxInterior
    have hproperOn : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) F :=
      helperForTheorem_25_6_properConvexFunctionOn (f := F) hproper
    have hproperStarOn :
        ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) :=
      proper_fenchelConjugate_of_proper (n := n) (f := F) hproperOn
    have hneBot :
        ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
      intro xStar
      exact hproperStarOn.2.2 xStar (by simp)
    have hCofinite :
        IsCofiniteFiniteConvexFunction fFin := by
      exact
        (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
          (f := fFin) hfFin_convex).2 ⟨hdomConj, hneBot⟩
    exact ⟨hStrict, hCofinite⟩
  · rintro ⟨hStrict, hCofinite⟩
    have hStrictFin : StrictConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
      exact (helperForTheorem_26_6_strictConvex_transport_univ (f := f)).1 hStrict
    have hInjective : Function.Injective (gradient f) := by
      exact hInjectiveIff.mpr (hStrictIff.mpr hStrictFin)
    have hcofiniteData :
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ ∧
          ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
      exact
        (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
          (f := fFin) hfFin_convex).1 hCofinite
    have hImage :
        euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) =
          interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) := by
      exact
        helperForTheorem_26_6_gradientImage_eq_interior_conjugateDomain_univ
          (f := f) hf_convex hf_differentiable hInjective
    have hGradImageUniv :
        euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) = Set.univ := by
      simpa [hcofiniteData.1] using hImage
    have hfFin_differentiable : Differentiable ℝ fFin := by
      simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
    have hSurjective : Function.Surjective (gradient f) := by
      intro xStar
      have hxFin :
          e xStar ∈ euclideanGradientAt fFin '' (Set.univ : Set (Fin n → ℝ)) := by
        simpa [hGradImageUniv]
      rcases hxFin with ⟨y, _, hy⟩
      refine ⟨e.symm y, ?_⟩
      apply e.injective
      calc
        e (gradient f (e.symm y)) = euclideanGradientAt fFin y := by
          simpa [fFin, e] using
            helperForText_26_4_0_2_sourceGradient_transport
              (f := fFin) (x := y) hfFin_differentiable.differentiableAt
        _ = e xStar := hy
    exact ⟨hInjective, hSurjective⟩

/-- Helper for Theorem 26.6: specializing Theorem 26.5 to the whole-space lift of `f`
packages the primal and dual Legendre data on `Set.univ`, together with a two-sided inverse
between the primal coordinate gradient and the dual selector. -/
lemma helperForTheorem_26_6_wholeSpaceLegendrePackage_from_bijectiveGradient
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ConvexOn ℝ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) f)
    (hf_differentiable : Differentiable ℝ f)
    (hbij : Function.Bijective (gradient f)) :
    let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
    let F : (Fin n → ℝ) → EReal := fun x => (fFin x : EReal)
    ∃ L :
        LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar)
          (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F,
      L.target = Set.univ ∧
      Set.EqOn L.conjFun (fenchelConjugate n F) Set.univ ∧
      ∃ LStar :
          LegendreConjugatePackageOn (fun xStar x : Fin n → ℝ => dotProduct x xStar)
            (interior
              (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)))
            (fenchelConjugate n F),
        LStar.target = Set.univ ∧
        Set.EqOn LStar.conjFun F Set.univ ∧
        ∃ gradStar : (Fin n → ℝ) → (Fin n → ℝ),
          L.toFun = euclideanGradientAt fFin ∧
          LStar.toFun = gradStar ∧
          (∀ xStar : Fin n → ℝ, euclideanGradientAt fFin (gradStar xStar) = xStar) ∧
          (∀ x : Fin n → ℝ, gradStar (euclideanGradientAt fFin x) = x) := by
  intro fFin F
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  have hcoordPackage :
      ProperConvexERealFunction (F := (Fin n → ℝ)) F ∧
        LowerSemicontinuous F ∧
        effectiveDomain (Set.univ : Set (Fin n → ℝ)) F = Set.univ ∧
        (∀ x : Fin n → ℝ, ∃ hDiff : ERealDifferentiableAt F x,
          erealGradientAt hDiff = euclideanGradientAt fFin x) ∧
        IsEssentiallySmooth F := by
    -- The coordinate lift already packages the primal function as a global Legendre candidate.
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
  have hfFin_convex : ConvexOn ℝ (Set.univ : Set (Fin n → ℝ)) fFin := by
    -- Convexity transports through the standard Euclidean-coordinate equivalence.
    have htransport :=
      ConvexOn.comp_linearMap (s := (Set.univ : Set (EuclideanSpace ℝ (Fin n)))) (f := f)
        hf_convex e.symm.toLinearMap
    simpa [fFin, e] using htransport
  have hcofiniteData :
      effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ ∧
        ∀ xStar : Fin n → ℝ, fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
    -- The primal half of Theorem 26.6 has already reduced surjectivity to co-finiteness.
    have hprimal :=
      helperForTheorem_26_6_bijective_iff_strictConvex_and_cofinite
        (f := f) hf_convex hf_differentiable
    have hcofinite : IsCofiniteFiniteConvexFunction fFin := hprimal.1 hbij |>.2
    exact
      (isCofiniteFiniteConvexFunction_iff_fenchelConjugate_finiteEverywhere
        (f := fFin) hfFin_convex).1 hcofinite
  have hInjectiveSubdiff :
      IsOneToOneMultivaluedMap (subdifferentialAt F) := by
    -- Gradient injectivity is equivalent to one-to-one-ness of the lifted subdifferential.
    exact
      (helperForTheorem_26_6_gradientInjective_iff_subdifferentialOneToOne
        (f := f) hf_convex hf_differentiable).1 hbij.1
  have hLegendreInterior :
      IsLegendreTypeOn
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F := by
    -- Proposition 26.4.1.5 turns the one-to-one subdifferential into Legendre type.
    exact
      (subdifferential_oneToOne_iff_restriction_isLegendreTypeOn_interior
        (f := F) hproper hclosed).1 hInjectiveSubdiff
  have hLegendrePackageRaw :=
    legendreTypeOn_interior_iff_conjugate_legendreTypeOn_interior_with_mutualLegendreConjugacy
      (f := F) hproper hclosed
  have hLegendrePackage :=
    hLegendrePackageRaw.2
      (show
        IsLegendreTypeOn
          (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) F)) F from by
          simpa [hdom] using hLegendreInterior)
  rcases hLegendrePackage with
    ⟨L, hLtarget, hLconj, LStar, hLStarTarget, hLStarConj,
      grad, gradStar, hLfun, hLStarFun, hGradMem, hGradUnique,
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
    -- The unique primal subgradient is the actual coordinate gradient.
    calc
      grad x = erealGradientAt (hdiffAll x) := by
        exact
          helperForTheorem_25_5_subgradientPreimage_eq_gradient
            (f := F) hconv (x := x) (hdiffAll x) hxPre
      _ = euclideanGradientAt fFin x := hgradEq x
  have hRightInv :
      ∀ xStar : Fin n → ℝ, euclideanGradientAt fFin (gradStar xStar) = xStar := by
    intro xStar
    have hxDualSub :
        dotProductEquiv ℝ (Fin n) (gradStar xStar) ∈
          subdifferentialAt (fenchelConjugate n F) xStar := by
      simpa [hcofiniteData.1] using hGradStarMem xStar (by simp [hcofiniteData.1])
    have hxDualEuclidean :
        IsEuclideanSubgradientAt (fenchelConjugate n F) xStar (gradStar xStar) := by
      simpa [IsEuclideanSubgradientAt] using hxDualSub
    have hxPrimalEuclidean :
        IsEuclideanSubgradientAt F (gradStar xStar) xStar :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := F) hclosedConv hproperOn (gradStar xStar) xStar).1 hxDualEuclidean
    have hxPrimalSub :
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt F (gradStar xStar) := by
      simpa [IsEuclideanSubgradientAt] using hxPrimalEuclidean
    -- Transport the dual selector back through Fenchel conjugacy and use primal uniqueness.
    have hxEq : xStar = grad (gradStar xStar) :=
      hGradUnique (by simp [hdom]) hxPrimalSub
    simpa [hGradEq (gradStar xStar)] using hxEq.symm
  have hLeftInv :
      ∀ x : Fin n → ℝ, gradStar (euclideanGradientAt fFin x) = x := by
    intro x
    have hxPrimalSub :
        dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt F x := by
      simpa [hdom] using hGradMem x (by simp [hdom])
    have hxPrimalEuclidean :
        IsEuclideanSubgradientAt F x (grad x) := by
      simpa [IsEuclideanSubgradientAt] using hxPrimalSub
    have hxDualEuclidean :
        IsEuclideanSubgradientAt (fenchelConjugate n F) (grad x) x :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := F) hclosedConv hproperOn x (grad x)).2 hxPrimalEuclidean
    have hxDualSub :
        dotProductEquiv ℝ (Fin n) x ∈ subdifferentialAt (fenchelConjugate n F) (grad x) := by
      simpa [IsEuclideanSubgradientAt] using hxDualEuclidean
    -- The dual unique subgradient turns the abstract selector into the actual inverse branch.
    have hxEq : x = gradStar (grad x) :=
      hGradStarUnique (by simp [hcofiniteData.1]) hxDualSub
    simpa [hGradEq x] using hxEq.symm
  exact
    ⟨L, by simpa [hcofiniteData.1] using hLtarget,
      by simpa [hcofiniteData.1] using hLconj,
      LStar, by simpa [hdom] using hLStarTarget,
      by simpa [hdom] using hLStarConj,
      gradStar, hLfun.trans (by
        funext x
        exact hGradEq x),
      hLStarFun, hRightInv, hLeftInv⟩

/-- Helper for Theorem 26.6: any selector whose image under the lifted coordinate gradient is the
identity must coincide with the transported inverse of `gradient f`. -/
lemma helperForTheorem_26_6_dualSelector_eq_transport_invFun
    {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_differentiable : Differentiable ℝ f)
    (hbij : Function.Bijective (gradient f))
    (g : (Fin n → ℝ) → (Fin n → ℝ))
    (hselector : ∀ xStar : Fin n → ℝ,
      let fFin : (Fin n → ℝ) → ℝ := fun x => f ((EuclideanSpace.equiv (Fin n) ℝ).symm x)
      euclideanGradientAt fFin (g xStar) = xStar) :
    ∀ xStar : Fin n → ℝ,
      g xStar =
        (EuclideanSpace.equiv (Fin n) ℝ)
          (Function.invFun (gradient f) ((EuclideanSpace.equiv (Fin n) ℝ).symm xStar)) := by
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (Fin n) ℝ
  let fFin : (Fin n → ℝ) → ℝ := fun x => f (e.symm x)
  have hfFin_differentiable : Differentiable ℝ fFin := by
    -- Differentiability is preserved by the Euclidean-coordinate transport.
    simpa [fFin, e] using hf_differentiable.comp e.symm.differentiable
  intro xStar
  have hselector' : euclideanGradientAt fFin (g xStar) = xStar := by
    simpa [fFin, e] using hselector xStar
  have hgradAtSelector :
      gradient f (e.symm (g xStar)) = e.symm xStar := by
    apply e.injective
    -- The transport lemma rewrites the Euclidean gradient equality back in source coordinates.
    calc
      e (gradient f (e.symm (g xStar))) = euclideanGradientAt fFin (g xStar) := by
        simpa [fFin, e] using
          (helperForText_26_4_0_2_sourceGradient_transport
            (f := fFin) (x := g xStar) hfFin_differentiable.differentiableAt)
      _ = xStar := hselector'
      _ = e (e.symm xStar) := by simp
  have hpreimageEq :
      e.symm (g xStar) =
        Function.invFun (gradient f) (e.symm xStar) := by
    apply hbij.1
    calc
      gradient f (e.symm (g xStar)) = e.symm xStar := hgradAtSelector
      _ = gradient f (Function.invFun (gradient f) (e.symm xStar)) := by
        symm
        exact Function.rightInverse_invFun hbij.2 (e.symm xStar)
  -- Apply the coordinate equivalence again to return to the `Fin n → ℝ` presentation.
  simpa [e] using congrArg e hpreimageEq

/-- Helper for Theorem 26.6: if the Fenchel conjugate is finite everywhere, coercing its
`toReal` branch back to `EReal` recovers the conjugate itself pointwise. -/
lemma helperForTheorem_26_6_fenchelConjugate_toReal_coe_eq_of_finiteEverywhere
    {n : ℕ} (F : (Fin n → ℝ) → EReal)
    (hdomStar : effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) = Set.univ)
    (hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F)) :
    (fun xStar : Fin n → ℝ => (((fenchelConjugate n F xStar).toReal : ℝ) : EReal)) =
      fenchelConjugate n F := by
  funext xStar
  have hxTop : fenchelConjugate n F xStar ≠ (⊤ : EReal) := by
    -- Membership in the full effective domain rules out the value `+∞`.
    have hxDom : xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n F) := by
      simpa [hdomStar]
    rw [effectiveDomain_eq] at hxDom
    exact lt_top_iff_ne_top.mp hxDom.2
  have hxBot : fenchelConjugate n F xStar ≠ (⊥ : EReal) := by
    -- Properness on `univ` rules out the value `-∞`.
    exact hproperStar.2.2 xStar (by simp)
  simpa using
    (helperForCorollary_19_3_4_eq_coe_toReal_of_ne_top_ne_bot hxTop hxBot).symm

end Section26
end Chap05
