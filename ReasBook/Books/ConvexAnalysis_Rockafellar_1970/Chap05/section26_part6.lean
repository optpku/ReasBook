/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part3
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part5

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped ConvexAnalysis Pointwise

-- Proof sketch: apply Theorem 26.4 to obtain a Legendre-conjugate package on
-- `C = int (dom f)`, use Theorem 26.3 to see that `f*` is essentially strictly convex because
-- `f` is essentially smooth, identify `D` with `dom ∂(f*)`, and then combine the defining
-- strict-convexity clause with the relative-interior inclusion from Text 26.2.1.
/-- Corollary 26.4.1: if `f` is an essentially smooth closed proper convex function and
`C = int (dom f)`, then its Legendre conjugate `(D, g)` is well-defined with
`D = {x* | ∂(f*)(x*) ≠ ∅}`; moreover
`ri (dom f*) ⊆ D ⊆ dom f*`, the function `g` is the restriction of `f*` to `D`, and `g` is
strictly convex on every convex subset of `D`. -/
theorem essentiallySmooth_has_legendreConjugatePackageOn_subdifferentialEffectiveDomain_conjugate
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hf_smooth : IsEssentiallySmooth f) :
    let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    let fStar := fenchelConjugate n f
    let D := subdifferentialEffectiveDomain fStar
    ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
      L.target = D ∧
      Set.EqOn L.conjFun fStar D ∧
      euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) ⊆ D ∧
      D ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar ∧
      ∀ ⦃S : Set (Fin n → ℝ)⦄, S ⊆ D → Convex ℝ S →
        StrictConvexOn ℝ S (fun x => (fStar x).toReal) := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let D : Set (Fin n → ℝ) := subdifferentialEffectiveDomain fStar
  change ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
      L.target = D ∧
      Set.EqOn L.conjFun fStar D ∧
      euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) ⊆ D ∧
      D ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar ∧
      ∀ ⦃S : Set (Fin n → ℝ)⦄, S ⊆ D → Convex ℝ S →
        StrictConvexOn ℝ S (fun x => (fStar x).toReal)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hconv, hf_closed⟩
  rcases (show
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        C.Nonempty ∧
          ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
            (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
            (∀ ⦃x xStar⦄, x ∈ C →
              dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
                xStar = grad x) ∧
            ∀ (xSeq : ℕ → Fin n → ℝ) (x : Fin n → ℝ),
              (∀ i : ℕ, xSeq i ∈ C) →
              Filter.Tendsto xSeq Filter.atTop (nhds x) →
              x ∈ frontier C →
              Filter.Tendsto (fun i : ℕ => ‖grad (xSeq i)‖) Filter.atTop Filter.atTop from by
        simpa [IsEssentiallySmooth, C] using hf_smooth) with
    ⟨_, hC_nonempty, grad, hgradMem, hgradUnique, _⟩
  rcases
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := f) hf hf_closed).2 hf_smooth with
    ⟨gradSingleton, hsingleton, hOffInterior⟩
  have hOffC : ∀ x : Fin n → ℝ, x ∉ C → subdifferentialAt f x = ∅ := by
    intro x hx
    simpa [C] using hOffInterior x hx
  have hdiff : ∀ x ∈ C, ERealDifferentiableAt f x := by
    intro x hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      constructor
      · exact
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hx)
      · exact hproper.2.2 x (by simp)
    -- The essential-smooth singleton subgradient determines the differentiability witness on `C`.
    refine
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hconv x hxFinite).2 ?_
    refine ⟨grad x, ?_, ?_⟩
    · simpa using hgradMem x hx
    · intro y hy
      exact hgradUnique hx (by simpa using hy)
  have hPackage :
      ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
        L.toFun = interiorGradientMap f hdiff ∧
        L.target = interiorGradientMap f hdiff '' C ∧
        Set.EqOn L.conjFun fStar L.target ∧
        L.target ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar := by
    -- Theorem 26.4 supplies the Legendre package on `C = int (dom f)`.
    simpa [C, fStar] using
      closedProperConvex_has_legendreConjugatePackageOn_interior_eq_fenchelConjugate
        (f := f) hf hf_closed hC_nonempty hdiff
  rcases hPackage with ⟨L, hLfun, hLtargetImage, hLconjEq, _hLtargetSubset⟩
  have hInteriorGradientMem :
      ∀ {x : Fin n → ℝ}, x ∈ C →
        dotProductEquiv ℝ (Fin n) (interiorGradientMap f hdiff x) ∈ subdifferentialAt f x := by
    intro x hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := ERealDifferentiableAt.finiteAt (hdiff x hx)
    have huniq :=
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hconv x hxFinite).1 (hdiff x hx)
    have hxInterior :
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [C] using hx
    simpa [interiorGradientMap, hxInterior] using huniq.1
  have hTargetEq :
      interiorGradientMap f hdiff '' C = D := by
    ext xStar
    constructor
    · intro hxStar
      rcases hxStar with ⟨x, hxC, rfl⟩
      -- A primal gradient point becomes a conjugate subgradient point by Theorem 23.5.
      have hxPrimal :
          IsEuclideanSubgradientAt f x (interiorGradientMap f hdiff x) := by
        simpa [IsEuclideanSubgradientAt] using hInteriorGradientMem hxC
      have hxConj :
          IsEuclideanSubgradientAt fStar (interiorGradientMap f hdiff x) x :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x (interiorGradientMap f hdiff x)).2 hxPrimal
      exact
        (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
          fStar (interiorGradientMap f hdiff x)).2
          ⟨dotProductEquiv ℝ (Fin n) x, by
            simpa [fStar, IsEuclideanSubgradientAt] using hxConj⟩
    · intro hxStar
      rcases
          (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
            fStar xStar).1 hxStar with
        ⟨xDual, hxDual⟩
      let x : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
      have hxConj : IsEuclideanSubgradientAt fStar xStar x := by
        simpa [x, fStar, IsEuclideanSubgradientAt] using hxDual
      have hxPrimal : IsEuclideanSubgradientAt f x xStar :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x xStar).1 hxConj
      have hxSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x := by
        simpa [IsEuclideanSubgradientAt] using hxPrimal
      have hxC : x ∈ C := by
        by_contra hxNotC
        have hEmpty : subdifferentialAt f x = ∅ := hOffC x hxNotC
        simp [hEmpty] at hxSub
      have hxInteriorGradient :
          dotProductEquiv ℝ (Fin n) (interiorGradientMap f hdiff x) ∈ subdifferentialAt f x := by
        exact hInteriorGradientMem hxC
      have hxStarEqGrad : xStar = grad x := hgradUnique hxC hxSub
      have hInteriorGradientEqGrad :
          interiorGradientMap f hdiff x = grad x :=
        hgradUnique hxC hxInteriorGradient
      -- Both dual vectors lie in the singleton fiber prescribed by essential smoothness.
      refine ⟨x, hxC, ?_⟩
      exact hInteriorGradientEqGrad.trans hxStarEqGrad.symm
  have hLtarget : L.target = D := by
    calc
      L.target = interiorGradientMap f hdiff '' C := hLtargetImage
      _ = D := hTargetEq
  have hproperStar : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hriDomSubset :
      euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) ⊆ D :=
    (relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
      (f := fStar) hproperStar).1
  have hDSubset :
      D ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar :=
    (relativeInterior_subset_subdifferentialEffectiveDomain_subset_effectiveDomain
      (f := fStar) hproperStar).2
  have hfStar : ProperConvexERealFunction (F := (Fin n → ℝ)) fStar :=
    helperForLemma_26_2_properConvexERealFunction hproperStar
  have hfStar_closed : LowerSemicontinuous fStar :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).1
  have hneBot : ∀ x : Fin n → ℝ, f x ≠ (⊥ : EReal) := by
    intro x
    exact hproper.2.2 x (by simp)
  have hbiconj : fenchelConjugate n fStar = f :=
    fenchelConjugate_biconjugate_eq_of_closedConvex (n := n) (f := f)
      hf_closed hconv hneBot
  have hfStar_essStrict : IsEssentiallyStrictlyConvex fStar := by
    have hf_bismooth : IsEssentiallySmooth (fenchelConjugate n fStar) := by
      -- Rewriting `(f*)*` back to `f` puts Theorem 26.3 in the form of the given hypothesis.
      simpa [fStar, hbiconj] using hf_smooth
    exact
      (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
        (f := fStar) hfStar hfStar_closed).2 hf_bismooth
  refine ⟨L, hLtarget, ?_, hriDomSubset, hDSubset, ?_⟩
  · intro xStar hxStar
    have hxTarget : xStar ∈ L.target := by
      simpa [hLtarget] using hxStar
    simpa [fStar] using hLconjEq hxTarget
  · intro S hSSubset hSConv
    -- The conjugate is essentially strictly convex, so every convex subset of `D` inherits strict convexity.
    exact hfStar_essStrict.2 hSSubset hSConv

-- Proof sketch: start from Corollary 26.4.1, which provides the Legendre conjugate `g` on a set
-- `D`; identify `D` with the target of the packaged Legendre data and record that `f*` is a
-- closed proper convex extension agreeing with `g` on `D`. Then state the boundary clause purely
-- in terms of segments that remain inside `D`, and use the usual exterior characterization
-- outside `closure D`.
/-- Helper for Text 26.4.1.1: points of `ri D` already lie in `D`. -/
lemma helperForText_26_4_1_1_mem_target_of_mem_riTarget
    {n : ℕ} {D : Set (Fin n → ℝ)} {x : Fin n → ℝ}
    (hx : x ∈ euclideanRelativeInterior_fin n D) :
    x ∈ D := by
  -- Relative interior points lie in the underlying set.
  exact helperForTheorem_21_1_riFin_subset_C D hx

/-- Helper for Text 26.4.1.1: along a segment staying in `D`, the Legendre conjugate package and
the Fenchel conjugate agree eventually near the boundary endpoint. -/
lemma helperForText_26_4_1_1_segment_conjFun_eq_fenchel_along_Iio
    {n : ℕ} {C : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → EReal}
    {L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f}
    {fStar : (Fin n → ℝ) → EReal}
    (hEqOn : Set.EqOn L.conjFun fStar L.target)
    {xStar₀ xStar : Fin n → ℝ}
    (hSeg : ∀ t : ℝ, t ∈ Set.Iio (1 : ℝ) →
      (1 - t) • xStar₀ + t • xStar ∈ L.target) :
    (fun t : ℝ => L.conjFun ((1 - t) • xStar₀ + t • xStar)) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))]
      (fun t : ℝ => fStar ((1 - t) • xStar₀ + t • xStar)) := by
  have hIoo : Set.Ioo (0 : ℝ) 1 ∈ nhdsWithin 1 (Set.Iio 1) := by
    -- Near `1` from the left, one is automatically in the open interval `(0,1)`.
    rw [nhdsWithin]
    show Set.Ioo (0 : ℝ) 1 ∈ nhds (1 : ℝ) ⊓ Filter.principal (Set.Iio (1 : ℝ))
    refine Filter.mem_inf_of_inter
      (s := Set.Ioi (0 : ℝ)) (t := Set.Iio (1 : ℝ)) (u := Set.Ioo (0 : ℝ) 1)
      (Ioi_mem_nhds (show (0 : ℝ) < 1 by norm_num)) ?_ ?_
    · simp
    · intro t ht
      exact ht
  filter_upwards [hIoo] with t ht
  -- On the left-open segment, `g` and `f*` agree because every point stays inside `D`.
  exact hEqOn (hSeg t ht.2)

/-- Helper for Text 26.4.1.1: every finite point of `f*` lies in the closure of the Legendre
target once `ri (dom f*) ⊆ D`. -/
lemma helperForText_26_4_1_1_effectiveDomain_subset_closure_target
    {n : ℕ} {fStar : (Fin n → ℝ) → EReal} {D : Set (Fin n → ℝ)}
    (hproperStar : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar)
    (hriDomSubset :
      euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) ⊆ D) :
    effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar ⊆ closure D := by
  classical
  intro x hxDom
  let e := euclideanEquiv n
  let domStar : Set (Fin n → ℝ) := effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar
  have hdomConv : Convex ℝ domStar := by
    exact effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := fStar) hproperStar.1
  have hdomConvE : Convex ℝ (e.symm '' domStar) := by
    simpa [e, domStar] using hdomConv.linear_image (e.symm.toLinearMap)
  have hxDomE : e.symm x ∈ e.symm '' domStar := by
    exact ⟨x, hxDom, by simp [e]⟩
  have hxClosureE : e.symm x ∈ closure (e.symm '' domStar) := by
    exact subset_closure hxDomE
  have hclosureRiEq :
      closure (euclideanRelativeInterior n (e.symm '' domStar)) =
        closure (e.symm '' domStar) := by
    exact
      (euclidean_closure_relativeInterior_eq_and_relativeInterior_closure_eq n
        (e.symm '' domStar) hdomConvE).1
  have hxClosureRiE : e.symm x ∈ closure (euclideanRelativeInterior n (e.symm '' domStar)) := by
    -- Convexity upgrades membership in the domain to membership in the closure of its relative interior.
    simpa [hclosureRiEq] using hxClosureE
  have hxImage :
      x ∈ e '' closure (euclideanRelativeInterior n (e.symm '' domStar)) := by
    exact ⟨e.symm x, hxClosureRiE, by simp [e]⟩
  have hclosureImage :
      e '' closure (euclideanRelativeInterior n (e.symm '' domStar)) =
        closure (e '' euclideanRelativeInterior n (e.symm '' domStar)) := by
    simpa [e] using (e.toHomeomorph.image_closure (euclideanRelativeInterior n (e.symm '' domStar)))
  have hriImageSubset : e '' euclideanRelativeInterior n (e.symm '' domStar) ⊆ D := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    have hzriFin : (z : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n domStar := by
      exact
        (mem_euclideanRelativeInterior_fin_iff (n := n) (C := domStar) (x := (z : Fin n → ℝ))).2
          (by simpa [e, domStar] using hz)
    exact hriDomSubset hzriFin
  have hxClosureRiFin : x ∈ closure (e '' euclideanRelativeInterior n (e.symm '' domStar)) := by
    simpa [hclosureImage] using hxImage
  exact (closure_mono hriImageSubset) hxClosureRiFin

/-- Text 26.4.1.1: if `f` is an essentially smooth closed proper convex function and
`fStar = f*`, then the Legendre conjugate `(D, g)` from Corollary 26.4.1 satisfies `g = fStar`
on `D`; moreover `fStar` is a closed proper convex extension of that Legendre conjugate, boundary
values of `fStar` are obtained as limits of `g` along segments from points of `ri D`, and
`fStar xStar = +∞` for `xStar ∉ closure D`. -/
theorem essentiallySmooth_conjugate_extends_legendreConjugate_with_boundary_limits_and_exterior_top
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hf_smooth : IsEssentiallySmooth f) :
    let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    let fStar := fenchelConjugate n f
    ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
      L.target = subdifferentialEffectiveDomain fStar ∧
      ProperConvexERealFunction (F := (Fin n → ℝ)) fStar ∧
      LowerSemicontinuous fStar ∧
      Set.EqOn L.conjFun fStar L.target ∧
      (∀ ⦃xStar₀ xStar : Fin n → ℝ⦄,
          xStar₀ ∈ euclideanRelativeInterior_fin n L.target →
          xStar ∈ frontier L.target →
          (∀ t : ℝ, t ∈ Set.Iio (1 : ℝ) →
            (1 - t) • xStar₀ + t • xStar ∈ L.target) →
          Filter.Tendsto
            (fun t : ℝ => L.conjFun ((1 - t) • xStar₀ + t • xStar))
            (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
            (nhds (fStar xStar))) ∧
      ∀ ⦃xStar : Fin n → ℝ⦄, xStar ∉ closure L.target → fStar xStar = ⊤ := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  change ∃ L : LegendreConjugatePackageOn (fun x xStar : Fin n → ℝ => dotProduct x xStar) C f,
      L.target = subdifferentialEffectiveDomain fStar ∧
      ProperConvexERealFunction (F := (Fin n → ℝ)) fStar ∧
      LowerSemicontinuous fStar ∧
      Set.EqOn L.conjFun fStar L.target ∧
      (∀ ⦃xStar₀ xStar : Fin n → ℝ⦄,
          xStar₀ ∈ euclideanRelativeInterior_fin n L.target →
          xStar ∈ frontier L.target →
          (∀ t : ℝ, t ∈ Set.Iio (1 : ℝ) →
            (1 - t) • xStar₀ + t • xStar ∈ L.target) →
          Filter.Tendsto
            (fun t : ℝ => L.conjFun ((1 - t) • xStar₀ + t • xStar))
            (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
            (nhds (fStar xStar))) ∧
      ∀ ⦃xStar : Fin n → ℝ⦄, xStar ∉ closure L.target → fStar xStar = ⊤
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  rcases
      essentiallySmooth_has_legendreConjugatePackageOn_subdifferentialEffectiveDomain_conjugate
        (f := f) hf hf_closed hf_smooth with
    ⟨L, hLtarget, hEqOnDom, hriDomSubset, hTargetSubsetDom, _hStrict⟩
  have hproperStar : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) fStar := by
    simpa [fStar] using proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hfStar : ProperConvexERealFunction (F := (Fin n → ℝ)) fStar := by
    simpa [fStar] using helperForLemma_26_2_properConvexERealFunction hproperStar
  have hfStar_closed : LowerSemicontinuous fStar := by
    simpa [fStar] using (fenchelConjugate_closedConvex (n := n) (f := f)).1
  have hclosedStar : ClosedConvexFunction fStar := by
    refine ⟨?_, hfStar_closed⟩
    simpa [fStar] using (fenchelConjugate_closedConvex (n := n) (f := f)).2
  have hEqOnTarget : Set.EqOn L.conjFun fStar L.target := by
    intro x hx
    exact hEqOnDom (by simpa [hLtarget] using hx)
  have hdomClosure : effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar ⊆ closure L.target := by
    -- The relative interior control from Corollary 26.4.1 forces all finite points into `closure D`.
    refine
      helperForText_26_4_1_1_effectiveDomain_subset_closure_target
        (hproperStar := hproperStar) ?_
    intro x hx
    simpa [hLtarget] using hriDomSubset hx
  refine ⟨L, hLtarget, hfStar, hfStar_closed, hEqOnTarget, ?_, ?_⟩
  · intro xStar₀ xStar hxStar₀ri _hxStarFrontier hSeg
    have hxStar₀Target : xStar₀ ∈ L.target := by
      -- The segment-limit theorem needs a base point already in the target.
      exact helperForText_26_4_1_1_mem_target_of_mem_riTarget hxStar₀ri
    have hxStar₀Dom : xStar₀ ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar := by
      exact hTargetSubsetDom (by simpa [hLtarget] using hxStar₀Target)
    let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] (Fin n → ℝ) := EuclideanSpace.equiv (𝕜 := ℝ) (ι := Fin n)
    let xStar₀E : EuclideanSpace ℝ (Fin n) := e.symm xStar₀
    let xStarE : EuclideanSpace ℝ (Fin n) := e.symm xStar
    have hsegFStar :
        Filter.Tendsto
          (fun t : ℝ => fStar ((1 - t) • xStar₀ + t • xStar))
          (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
          (nhds (fStar xStar)) := by
      -- Corollary 7.5.1 computes the boundary value of the closed proper convex extension `f*`.
      simpa [xStar₀E, xStarE, e] using
        closedProperConvexFunction_eq_limit_along_segment
          (f := fStar) hclosedStar hproperStar
          (x := xStar₀E) (by simpa [xStar₀E, e] using hxStar₀Dom) xStarE
    have hEventuallyEq :
        (fun t : ℝ => L.conjFun ((1 - t) • xStar₀ + t • xStar)) =ᶠ[nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ))]
          (fun t : ℝ => fStar ((1 - t) • xStar₀ + t • xStar)) :=
      helperForText_26_4_1_1_segment_conjFun_eq_fenchel_along_Iio hEqOnTarget hSeg
    -- Along the segment inside `D`, `g` can replace `f*` in the limiting expression.
    exact Filter.Tendsto.congr' hEventuallyEq.symm hsegFStar
  · intro xStar hxNotClosure
    by_contra hxNotTop
    have hxDom : xStar ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar := by
      -- A non-`⊤` value is exactly a finite-domain point for the Fenchel conjugate.
      simpa [effectiveDomain_eq] using (lt_top_iff_ne_top.mpr hxNotTop)
    exact hxNotClosure (hdomClosure hxDom)

-- Proof sketch: combine Corollary 26.4.1, which identifies the Legendre target with
-- `dom ∂(f*)`, with Theorem 26.4, which realizes that target as the image of the gradient on
-- `C = int (dom f)` and gives the value formula there. The continuity of the restricted gradient
-- map is then the `C¹` regularity supplied by Theorem 25.5 on the interior differentiability set.
/-- Helper for Text 26.4.1.2: differentiability on `int (dom f)` makes every subgradient agree
with the chosen interior gradient. -/
lemma helperForText_26_4_1_2_interiorGradient_mem_subdifferentialAt
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x)
    {x : Fin n → ℝ}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    dotProductEquiv ℝ (Fin n) (interiorGradientMap f hdiff x) ∈ subdifferentialAt f x := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hcore :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      f hconv x (ERealDifferentiableAt.finiteAt (hdiff x hx))).1 (hdiff x hx)
  -- On the interior, `interiorGradientMap` is just the chosen differentiable gradient.
  simpa [interiorGradientMap, hx] using hcore.1

/-- Helper for Text 26.4.1.2: the Fenchel-Young identity rewrites the conjugate value at the
interior gradient into the standard subtraction formula. -/
lemma helperForText_26_4_1_2_fenchelConjugate_eq_dotSub_at_interiorGradient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x)
    {x : Fin n → ℝ}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)) :
    fenchelConjugate n f (interiorGradientMap f hdiff x) =
      (((dotProduct x (interiorGradientMap f hdiff x) : ℝ) : EReal) - f x) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hSub :
      IsEuclideanSubgradientAt f x (interiorGradientMap f hdiff x) := by
    -- The interior gradient yields the Euclidean subgradient needed for Fenchel-Young equality.
    simpa [IsEuclideanSubgradientAt] using
      helperForText_26_4_1_2_interiorGradient_mem_subdifferentialAt
        (f := f) (hf := hf) (hdiff := hdiff) hx
  have hFY :
      FenchelYoungEqualityAt f x (interiorGradientMap f hdiff x) := by
    -- The Chapter 23 equivalence turns the Euclidean subgradient into equality in Fenchel-Young.
    exact
      ((euclidean_subgradient_iff_fenchel_supremum_attainment_and_fenchelYoung
        f hproper x (interiorGradientMap f hdiff x)).1.out 0 3).1 hSub
  -- The textbook form is exactly the subtraction version of Fenchel-Young equality.
  exact
    helperForText_26_4_0_2_fenchelYoung_subtractionForm
      (F := f) (x := x) (xStar := interiorGradientMap f hdiff x) hproper hFY

/-- Helper for Text 26.4.1.2: differentiability on `int (dom f)` makes every subgradient agree
with the chosen interior gradient. -/
lemma helperForText_26_4_1_2_subgradient_eq_interiorGradient
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x)
    {x xStar : Fin n → ℝ}
    (hx : x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
    (hxSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x) :
    xStar = interiorGradientMap f hdiff x := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ :=
    ERealDifferentiableAt.finiteAt (hdiff x hx)
  have huniq :=
    (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
      f hconv x hxFinite).1 (hdiff x hx)
  have hGradEq : erealGradientAt (hdiff x hx) = interiorGradientMap f hdiff x := by
    simp [interiorGradientMap, hx]
  -- The differentiability theorem identifies every subgradient with the canonical gradient.
  exact (huniq.2.2 xStar (by simpa using hxSub)).trans hGradEq

/-- Helper for Text 26.4.1.2: on the interior effective domain, the differentiability set from
Theorem 25.5 is exactly the interior itself. -/
lemma helperForText_26_4_1_2_differentiabilitySet_eq_interior
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x) :
    {x | x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) ∧
        ERealDifferentiableAt f x} =
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  ext x
  constructor
  · intro hx
    -- Membership in the differentiability set already records interior membership.
    exact hx.1
  · intro hx
    -- Conversely, the supplied differentiability hypothesis fills in the second conjunct.
    exact ⟨hx, hdiff x hx⟩

/-- Helper for Text 26.4.1.2: the conjugate subdifferential domain is the image of the interior
gradient map. -/
lemma helperForText_26_4_1_2_subdifferentialEffectiveDomain_eq_interiorGradientImage
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hf_smooth : IsEssentiallySmooth f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x) :
    let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    let fStar := fenchelConjugate n f
    subdifferentialEffectiveDomain fStar = interiorGradientMap f hdiff '' C := by
  intro C fStar
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hconv, hf_closed⟩
  rcases (subdifferential_singleValued_iff_essentiallySmooth
      (f := f) hf hf_closed).2 hf_smooth with
    ⟨_grad, _hOnInterior, hOffInterior⟩
  have hOffC : ∀ x : Fin n → ℝ, x ∉ C → subdifferentialAt f x = ∅ := by
    intro x hx
    simpa [C] using hOffInterior x hx
  ext xStar
  constructor
  · intro hxStar
    rcases
        (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
          fStar xStar).1 hxStar with
      ⟨xDual, hxDual⟩
    let x : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
    have hxConj : IsEuclideanSubgradientAt fStar xStar x := by
      simpa [x, fStar, IsEuclideanSubgradientAt] using hxDual
    have hxPrimal : IsEuclideanSubgradientAt f x xStar :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x xStar).1 hxConj
    have hxSub : dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x := by
      simpa [IsEuclideanSubgradientAt] using hxPrimal
    have hxC : x ∈ C := by
      by_contra hxNotC
      have hEmpty : subdifferentialAt f x = ∅ := hOffC x hxNotC
      simp [hEmpty] at hxSub
    -- The recovered primal point must map back to `xStar` by uniqueness of the interior gradient.
    refine ⟨x, hxC, ?_⟩
    exact
      (helperForText_26_4_1_2_subgradient_eq_interiorGradient
        (f := f) (hf := hf) (hdiff := hdiff) hxC hxSub).symm
  · intro hxStar
    rcases hxStar with ⟨x, hxC, rfl⟩
    have hxPrimal :
        IsEuclideanSubgradientAt f x (interiorGradientMap f hdiff x) := by
      -- The interior gradient converts into an actual primal subgradient by differentiability.
      simpa [IsEuclideanSubgradientAt] using
        helperForText_26_4_1_2_interiorGradient_mem_subdifferentialAt
          (hf := hf) (hdiff := hdiff) hxC
    have hxConj :
        IsEuclideanSubgradientAt fStar (interiorGradientMap f hdiff x) x :=
      (euclidean_subgradient_fenchelConjugate_iff
        (f := f) hclosed hproper x (interiorGradientMap f hdiff x)).2 hxPrimal
    -- A conjugate subgradient witness is exactly the nonemptiness criterion for `dom ∂(f*)`.
    exact
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
        fStar (interiorGradientMap f hdiff x)).2
        ⟨dotProductEquiv ℝ (Fin n) x, by
          simpa [fStar, IsEuclideanSubgradientAt] using hxConj⟩

/-- Helper for Text 26.4.1.2: the interior gradient is continuous on `int (dom f)`. -/
lemma helperForText_26_4_1_2_interiorGradient_continuousOn_interior
    {n : ℕ} {f : (Fin n → ℝ) → EReal}
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x) :
    Continuous
      (fun x : {x // x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)} =>
        interiorGradientMap f hdiff x) := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  let D : Set (Fin n → ℝ) := {x | x ∈ C ∧ ERealDifferentiableAt f x}
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hGradContD :
      Continuous (fun x : {x // x ∈ D} => erealGradientAt x.2.2) := by
    -- Theorem 25.5 gives continuity on the differentiability subtype.
    simpa [C, D] using
      helperForTheorem_25_5_gradient_continuousOn_differentiabilitySet
        (f := f) hproper
  have hD_eq_C : D = C := by
    -- Here the differentiability set collapses to the whole interior by hypothesis.
    simpa [C, D] using
      helperForText_26_4_1_2_differentiabilitySet_eq_interior
        (f := f) (hdiff := hdiff)
  let toD : {x // x ∈ C} → {x // x ∈ D} :=
    fun x => ⟨x.1, hD_eq_C.symm ▸ x.2⟩
  have hToDContinuous : Continuous toD :=
    (Homeomorph.setCongr hD_eq_C.symm).continuous_toFun
  have hGradContC :
      Continuous (fun x : {x // x ∈ C} => erealGradientAt (toD x).2.2) :=
    hGradContD.comp hToDContinuous
  have hGradEq :
      (fun x : {x // x ∈ C} => erealGradientAt (toD x).2.2) =
        (fun x : {x // x ∈ C} => interiorGradientMap f hdiff x) := by
    funext x
    have hProof : (toD x).2.2 = hdiff x.1 x.2 := by
      apply Subsingleton.elim
    -- On the interior subtype, `interiorGradientMap` is exactly the chosen gradient witness.
    calc
      erealGradientAt (toD x).2.2 = erealGradientAt (hdiff x.1 x.2) := by rw [hProof]
      _ = interiorGradientMap f hdiff x := by
        simp [interiorGradientMap, C, x.2]
  exact hGradEq ▸ hGradContC

/-- Text 26.4.1.2: for an essentially smooth closed proper convex function, if
`C = int (dom f)`, `fStar = f*`, and `D = {x* | ∂(fStar)(x*) ≠ ∅}`, then there exists a
gradient map `grad` on `C` such that `grad` is a continuous map from `C` onto `D` and
`fStar (grad x) = ⟪x, grad x⟫ - f x` for every `x ∈ C`. Thus the Legendre conjugate may be
viewed as a generally nonconvex function on `C` via the parameterization `x* = grad x`. -/
theorem essentiallySmooth_gradient_parameterizes_conjugateDomain_and_conjugateValue_identity
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hf_smooth : IsEssentiallySmooth f) :
    let C := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
    let fStar := fenchelConjugate n f
    let D := subdifferentialEffectiveDomain fStar
    ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
      (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
      (∀ {x xStar}, x ∈ C →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x) ∧
      D = grad '' C ∧
      Continuous (fun x : {x // x ∈ C} => grad x) ∧
      ∀ x ∈ C, fStar (grad x) = (((dotProduct x (grad x) : ℝ) : EReal) - f x) := by
  let C : Set (Fin n → ℝ) := interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f)
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let D : Set (Fin n → ℝ) := subdifferentialEffectiveDomain fStar
  change ∃ grad : (Fin n → ℝ) → (Fin n → ℝ),
      (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad x) ∈ subdifferentialAt f x) ∧
      (∀ {x xStar}, x ∈ C →
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
          xStar = grad x) ∧
      D = grad '' C ∧
      Continuous (fun x : {x // x ∈ C} => grad x) ∧
      ∀ x ∈ C, fStar (grad x) = (((dotProduct x (grad x) : ℝ) : EReal) - f x)
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  rcases (show
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f ∧
        C.Nonempty ∧
          ∃ grad₀ : (Fin n → ℝ) → (Fin n → ℝ),
            (∀ x ∈ C, dotProductEquiv ℝ (Fin n) (grad₀ x) ∈ subdifferentialAt f x) ∧
            (∀ ⦃x xStar⦄, x ∈ C →
              dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x →
                xStar = grad₀ x) ∧
            ∀ (xSeq : ℕ → Fin n → ℝ) (x : Fin n → ℝ),
              (∀ i : ℕ, xSeq i ∈ C) →
              Filter.Tendsto xSeq Filter.atTop (nhds x) →
              x ∈ frontier C →
              Filter.Tendsto (fun i : ℕ => ‖grad₀ (xSeq i)‖) Filter.atTop Filter.atTop from by
        simpa [IsEssentiallySmooth, C] using hf_smooth) with
    ⟨_, _hC_nonempty, grad₀, hgradMem₀, hgradUnique₀, _⟩
  have hdiff :
      ∀ x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f),
        ERealDifferentiableAt f x := by
    intro x hx
    have hxC : x ∈ C := by
      simpa [C] using hx
    have hxFinite : f x ≠ ⊤ ∧ f x ≠ ⊥ := by
      constructor
      · exact
          mem_effectiveDomain_imp_ne_top
            (S := (Set.univ : Set (Fin n → ℝ))) (f := f) (interior_subset hx)
      · exact hproper.2.2 x (by simp)
    -- The essential-smooth singleton subgradient supplies the unique-gradient witness on `C`.
    refine
      (convexFunction_differentiableAt_iff_gradient_is_unique_subgradient
        f hconv x hxFinite).2 ?_
    refine ⟨grad₀ x, ?_, ?_⟩
    · simpa using hgradMem₀ x hxC
    · intro y hy
      exact hgradUnique₀ hxC (by simpa using hy)
  let grad : (Fin n → ℝ) → (Fin n → ℝ) := interiorGradientMap f hdiff
  refine ⟨grad, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxInterior :
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [C] using hx
    -- The interior gradient is a genuine subgradient at every interior point.
    simpa [grad] using
      helperForText_26_4_1_2_interiorGradient_mem_subdifferentialAt
        (hf := hf) (hdiff := hdiff) hxInterior
  · intro x xStar hx hxSub
    have hxInterior :
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [C] using hx
    -- Differentiability on `C` makes the subgradient unique, so it equals `grad x`.
    simpa [grad] using
      helperForText_26_4_1_2_subgradient_eq_interiorGradient
        (f := f) (hf := hf) (hdiff := hdiff) hxInterior hxSub
  · -- The conjugate domain is exactly the image of the interior gradient map.
    simpa [D, fStar, grad, C] using
      helperForText_26_4_1_2_subdifferentialEffectiveDomain_eq_interiorGradientImage
        (f := f) (hf := hf) (hf_closed := hf_closed) (hf_smooth := hf_smooth) (hdiff := hdiff)
  · -- Theorem 25.5 gives continuity of the gradient on the entire interior differentiability set.
    simpa [grad, C] using
      helperForText_26_4_1_2_interiorGradient_continuousOn_interior
        (f := f) (hf := hf) (hdiff := hdiff)
  · intro x hx
    have hxInterior :
        x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
      simpa [C] using hx
    -- Theorem 26.4 rewrites the conjugate value at `grad x` into the Fenchel-Young formula.
    simpa [fStar, grad] using
      helperForText_26_4_1_2_fenchelConjugate_eq_dotSub_at_interiorGradient
        (hf := hf) (hdiff := hdiff) hxInterior

-- Proof sketch: combine Theorem 26.1, which identifies essential smoothness with
-- single-valuedness of `∂ f`, with the injectivity criterion encoded by
-- `IsOneToOneMultivaluedMap`; then use the Chapter 26 strict-convexity characterization on
-- `int (dom f)` for closed proper convex functions.
/-- Helper for Corollary 26.3.1: inverse single-valuedness of `∂ f` is equivalent to ordinary
single-valuedness of `∂(f*)`. -/
lemma helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f) :
    IsSingleValuedMultivaluedMap (inverseMultivaluedMap (subdifferentialAt f)) ↔
      IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n f)) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hfConv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hclosed : ClosedConvexFunction f := ⟨hfConv, hf_closed⟩
  constructor
  · intro hInverseSingleValued
    -- Transport conjugate subgradients back to primal subgradients and use uniqueness in the inverse fibers.
    intro xStar g₁ hg₁ g₂ hg₂
    let x₁ : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g₁
    let x₂ : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm g₂
    have hx₁Conj :
        IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x₁ := by
      simpa [x₁, IsEuclideanSubgradientAt] using hg₁
    have hx₂Conj :
        IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x₂ := by
      simpa [x₂, IsEuclideanSubgradientAt] using hg₂
    have hx₁ :
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x₁ := by
      have hx₁Primal :
          IsEuclideanSubgradientAt f x₁ xStar :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x₁ xStar).1 hx₁Conj
      simpa [IsEuclideanSubgradientAt] using hx₁Primal
    have hx₂ :
        dotProductEquiv ℝ (Fin n) xStar ∈ subdifferentialAt f x₂ := by
      have hx₂Primal :
          IsEuclideanSubgradientAt f x₂ xStar :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x₂ xStar).1 hx₂Conj
      simpa [IsEuclideanSubgradientAt] using hx₂Primal
    have hEq : x₁ = x₂ :=
      hInverseSingleValued (dotProductEquiv ℝ (Fin n) xStar)
        (by simpa [inverseMultivaluedMap] using hx₁)
        (by simpa [inverseMultivaluedMap] using hx₂)
    calc
      g₁ = dotProductEquiv ℝ (Fin n) x₁ := by simp [x₁]
      _ = dotProductEquiv ℝ (Fin n) x₂ := by rw [hEq]
      _ = g₂ := by simp [x₂]
  · intro hConjugateSingleValued
    -- Convert primal inverse-fiber membership into conjugate subgradient membership and use uniqueness there.
    intro xDual x₁ hx₁ x₂ hx₂
    let xStar : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm xDual
    have hx₁Conj :
        dotProductEquiv ℝ (Fin n) x₁ ∈ subdifferentialAt (fenchelConjugate n f) xStar := by
      have hx₁Primal :
          IsEuclideanSubgradientAt f x₁ xStar := by
        simpa [xStar, inverseMultivaluedMap, IsEuclideanSubgradientAt] using hx₁
      have hx₁Fenchel :
          IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x₁ :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x₁ xStar).2 hx₁Primal
      simpa [IsEuclideanSubgradientAt] using hx₁Fenchel
    have hx₂Conj :
        dotProductEquiv ℝ (Fin n) x₂ ∈ subdifferentialAt (fenchelConjugate n f) xStar := by
      have hx₂Primal :
          IsEuclideanSubgradientAt f x₂ xStar := by
        simpa [xStar, inverseMultivaluedMap, IsEuclideanSubgradientAt] using hx₂
      have hx₂Fenchel :
          IsEuclideanSubgradientAt (fenchelConjugate n f) xStar x₂ :=
        (euclidean_subgradient_fenchelConjugate_iff
          (f := f) hclosed hproper x₂ xStar).2 hx₂Primal
      simpa [IsEuclideanSubgradientAt] using hx₂Fenchel
    have hEqDual :
        dotProductEquiv ℝ (Fin n) x₁ = dotProductEquiv ℝ (Fin n) x₂ :=
      hConjugateSingleValued xStar hx₁Conj hx₂Conj
    exact (dotProductEquiv ℝ (Fin n)).injective hEqDual

/-- Helper for Corollary 26.3.1: essential smoothness identifies `dom ∂ f` with
`int (dom f)`. -/
lemma helperForCorollary_26_3_1_subdifferentialEffectiveDomain_eq_interior_of_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hf_smooth : IsEssentiallySmooth f) :
    subdifferentialEffectiveDomain f =
      interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
  rcases (subdifferential_singleValued_iff_essentiallySmooth
      (f := f) hf hf_closed).2 hf_smooth with
    ⟨grad, hOnInterior, hOffInterior⟩
  ext x
  constructor
  · intro hx
    by_contra hxNotInterior
    have hEmpty : subdifferentialAt f x = ∅ := hOffInterior x hxNotInterior
    have hNonempty :=
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).1 hx
    exact hNonempty.ne_empty (by simpa [hEmpty])
  · intro hx
    -- On the interior, Theorem 26.1 gives an explicit singleton formula for the subdifferential.
    have hSingleton :
        subdifferentialAt f x = {dotProductEquiv ℝ (Fin n) (grad x)} :=
      hOnInterior x hx
    exact
      (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty f x).2
        (by simpa [hSingleton] using Set.singleton_nonempty (dotProductEquiv ℝ (Fin n) (grad x)))

/-- Helper for Corollary 26.3.1: essential strict convexity already yields strict convexity on
`int (dom f)` by restricting Text 26.2.1 from `ri (dom f)`. -/
lemma helperForCorollary_26_3_1_strictConvexOn_interior_of_essentiallyStrictlyConvex
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf_essStrict : IsEssentiallyStrictlyConvex f) :
    StrictConvexOn ℝ
      (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
      (fun x => (f x).toReal) := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f := hf_essStrict.1
  have hStrictRI :
      StrictConvexOn ℝ
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
        (fun x => (f x).toReal) :=
    essentiallyStrictlyConvex_strictConvexOn_relativeInterior_and_exists_nonconvex_subdifferentialEffectiveDomain.1
      f hf_essStrict
  have hDomConv :
      Convex ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) :=
    effectiveDomain_convex (S := (Set.univ : Set (Fin n → ℝ))) (f := f) hproper.1
  refine ⟨hDomConv.interior, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  -- Interior points are relative-interior points, so the relative-interior strict convexity applies.
  exact hStrictRI.2
    (helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hx)
    (helperForTheorem_23_4_mem_relativeInterior_of_mem_interior
      (C := effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) hy)
    hxy ha hb hab

/-- Helper for Corollary 26.3.1: strict convexity on `int (dom f)` becomes essential strict
convexity once essential smoothness identifies `dom ∂ f` with that interior. -/
lemma helperForCorollary_26_3_1_essentiallyStrictlyConvex_of_strictConvexOn_interior_and_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f)
    (hStrictInterior :
      StrictConvexOn ℝ
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
        (fun x => (f x).toReal))
    (hf_smooth : IsEssentiallySmooth f) :
    IsEssentiallyStrictlyConvex f := by
  refine ⟨helperForTheorem_25_6_properConvexFunctionOn (f := f) hf, ?_⟩
  intro C hCSubset hCConv
  refine ⟨hCConv, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hDomEq :=
    helperForCorollary_26_3_1_subdifferentialEffectiveDomain_eq_interior_of_essentiallySmooth
      (f := f) hf hf_closed hf_smooth
  have hxInterior :
      x ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [hDomEq] using hCSubset hx
  have hyInterior :
      y ∈ interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f) := by
    simpa [hDomEq] using hCSubset hy
  -- Once `C` sits inside `int (dom f)`, the assumed strict convexity on the interior closes the goal.
  exact hStrictInterior.2 hxInterior hyInterior hxy ha hb hab

/-- Corollary 26.3.1: for a closed proper convex function, the subdifferential mapping `∂ f` is
one-to-one if and only if `f` is strictly convex on `int (dom f)` and essentially smooth. -/
theorem subdifferential_oneToOne_iff_strictConvexOn_interior_and_essentiallySmooth
    {n : ℕ} (f : (Fin n → ℝ) → EReal)
    (hf : ProperConvexERealFunction (F := (Fin n → ℝ)) f)
    (hf_closed : LowerSemicontinuous f) :
    IsOneToOneMultivaluedMap (subdifferentialAt f) ↔
      StrictConvexOn ℝ
        (interior (effectiveDomain (Set.univ : Set (Fin n → ℝ)) f))
        (fun x => (f x).toReal) ∧
        IsEssentiallySmooth f := by
  have hproper : ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hproperStar :
      ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f) :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hfStar : ProperConvexERealFunction (F := (Fin n → ℝ)) (fenchelConjugate n f) :=
    helperForLemma_26_2_properConvexERealFunction hproperStar
  have hfStarClosed : LowerSemicontinuous (fenchelConjugate n f) :=
    (fenchelConjugate_closedConvex (n := n) (f := f)).1
  constructor
  · intro hOneToOne
    have hf_smooth : IsEssentiallySmooth f :=
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := f) hf hf_closed).1.1 hOneToOne.1
    have hConjugateSingleValued :
        IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n f)) :=
      (helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
        (f := f) hf hf_closed).1 hOneToOne.2
    have hfStar_smooth : IsEssentiallySmooth (fenchelConjugate n f) :=
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := fenchelConjugate n f) hfStar hfStarClosed).1.1 hConjugateSingleValued
    have hf_essStrict : IsEssentiallyStrictlyConvex f :=
      (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
        (f := f) hf hf_closed).2 hfStar_smooth
    refine ⟨?_, hf_smooth⟩
    -- The forward implication uses Theorem 26.3 to recover essential strict convexity, then restricts it to the interior.
    exact
      helperForCorollary_26_3_1_strictConvexOn_interior_of_essentiallyStrictlyConvex
        (f := f) hf_essStrict
  · rintro ⟨hStrictInterior, hf_smooth⟩
    have hSingleValued :
        IsSingleValuedMultivaluedMap (subdifferentialAt f) :=
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := f) hf hf_closed).1.2 hf_smooth
    have hf_essStrict : IsEssentiallyStrictlyConvex f :=
      helperForCorollary_26_3_1_essentiallyStrictlyConvex_of_strictConvexOn_interior_and_essentiallySmooth
        (f := f) hf hf_closed hStrictInterior hf_smooth
    have hfStar_smooth : IsEssentiallySmooth (fenchelConjugate n f) :=
      (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
        (f := f) hf hf_closed).1 hf_essStrict
    have hConjugateSingleValued :
        IsSingleValuedMultivaluedMap (subdifferentialAt (fenchelConjugate n f)) :=
      (subdifferential_singleValued_iff_essentiallySmooth
        (f := fenchelConjugate n f) hfStar hfStarClosed).1.2 hfStar_smooth
    refine ⟨hSingleValued, ?_⟩
    -- Transport single-valuedness of `∂(f*)` back to injectivity of `∂ f`.
    exact
      (helperForCorollary_26_3_1_inverseSubdifferential_singleValued_iff_conjugateSingleValued
        (f := f) hf hf_closed).2 hConjugateSingleValued

-- Proof sketch: use Theorem 16.4 to identify the conjugate of `f₁ □ f₂` with the pointwise sum
-- `f₁* + f₂*` under the common-relative-interior hypothesis, combine Theorem 26.3 with the
-- essential smoothness of `f₁` to see that `f₁*` is essentially strictly convex, then apply the
-- qualified subdifferential sum rule from Theorem 23.8 to show the sum remains essentially
-- strictly convex, and finally dualize back with Theorem 26.3.
/-- Helper for Corollary 26.3.2: the binary relative-interior hypothesis packages into the `Fin 2`
family witness needed by the finite-family Chapter 23 and Chapter 16 lemmas. -/
lemma helperForCorollary_26_3_2_commonRelativeInterior_twoConjugates
    {n : ℕ} (f₁ f₂ : (Fin n → ℝ) → EReal)
    (hri :
      Set.Nonempty
        (euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₁)) ∩
          euclideanRelativeInterior_fin n
            (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (fenchelConjugate n f₂)))) :
    ∃ z : Fin n → ℝ,
      ∀ i : Fin 2,
        z ∈ euclideanRelativeInterior_fin n
          (effectiveDomain (Set.univ : Set (Fin n → ℝ))
            (Fin.cases (fenchelConjugate n f₁) (fun _ => fenchelConjugate n f₂) i)) := by
  rcases hri with ⟨z, hz₁, hz₂⟩
  refine ⟨z, ?_⟩
  intro i
  -- The finite-family witness is just the two coordinate hypotheses repackaged.
  fin_cases i
  · simpa using hz₁
  · simpa using hz₂

end Section26
end Chap05
