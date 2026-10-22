/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section26_part8

section Chap05
section Section26

attribute [local instance] Classical.propDecidable
open scoped ConvexAnalysis Pointwise

/-- The coordinate-space realization of the Euclidean adjoint of a linear map. -/
noncomputable def coordinateAdjointLinearMap {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
  helperForTheorem_23_9_coordinateAdjointMap A

/-- Helper for Corollary 26.3.3: the coordinate adjoint realizes the usual dot-product adjoint
identity. -/
lemma helperForCorollary_26_3_3_dotProduct_coordinateAdjoint {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (x : Fin n → ℝ) (y : Fin m → ℝ) :
    dotProduct (A x) y = dotProduct x (coordinateAdjointLinearMap A y) := by
  -- Rewrite the coordinate adjoint through the Euclidean lift and apply the Chapter 16 adjoint
  -- identity for the dot product.
  simpa [coordinateAdjointLinearMap, helperForTheorem_23_9_coordinateAdjointMap,
    helperForTheorem_23_9_euclideanLinearLift] using
    (section16_dotProduct_map_eq_dotProduct_adjoint
      (A := helperForTheorem_23_9_euclideanLinearLift A) (x := x) (yStar := y))

/-- Helper for Corollary 26.3.3: surjectivity of `A` forces injectivity of the coordinate adjoint
`A*`. -/
lemma helperForCorollary_26_3_3_coordinateAdjoint_injective_of_surjective {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (hA : Function.Surjective A) :
    Function.Injective (coordinateAdjointLinearMap A) := by
  intro y₁ y₂ hEq
  apply sub_eq_zero.mp
  apply dotProduct_eq_zero
  intro z
  rcases hA z with ⟨x, rfl⟩
  -- Test the difference against an arbitrary point in the range of `A`; surjectivity makes this
  -- enough to force the dual difference to vanish.
  calc
    dotProduct (y₁ - y₂) (A x) = dotProduct (A x) (y₁ - y₂) := by
      rw [dotProduct_comm]
    _ = dotProduct x (coordinateAdjointLinearMap A (y₁ - y₂)) :=
      helperForCorollary_26_3_3_dotProduct_coordinateAdjoint A x (y₁ - y₂)
    _ = 0 := by
      simp [map_sub, hEq]

/-- Helper for Corollary 26.3.3: subgradients of the precomposition `f* ∘ A*` project to
subgradients of `f*` under the relative-interior qualification. -/
lemma helperForCorollary_26_3_3_mem_conjugateSubdiffDomain_of_mem_precompSubdiffDomain
    {n m : ℕ} (f : (Fin n → ℝ) → EReal) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hproper : ProperConvexFunctionOn Set.univ (fenchelConjugate n f))
    (hri : RangeMeetsRelativeInteriorEffectiveDomain A (fenchelConjugate n f))
    {yStar : Fin m → ℝ}
    (hyStar :
      yStar ∈ subdifferentialEffectiveDomain (fun z => fenchelConjugate n f (A z))) :
    A yStar ∈ subdifferentialEffectiveDomain (fenchelConjugate n f) := by
  have hEq :
      subdifferentialAt (fun z => fenchelConjugate n f (A z)) yStar =
        A.dualMap '' subdifferentialAt (fenchelConjugate n f) (A yStar) := by
    -- Theorem 23.9 identifies the precomposition subdifferential exactly under the
    -- relative-interior qualification.
    simpa using
      (subdifferential_precomp_linearMap_contains_dualMapImage_and_eq_under_qualification
        A (fenchelConjugate n f) hproper).2 (Or.inl hri) yStar
  have hyNonempty :
      Set.Nonempty (subdifferentialAt (fun z => fenchelConjugate n f (A z)) yStar) :=
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fun z => fenchelConjugate n f (A z)) yStar).1 hyStar
  rw [hEq] at hyNonempty
  rcases hyNonempty with ⟨xDual, hxDual⟩
  rcases hxDual with ⟨eta, hEta, rfl⟩
  -- Any nonempty image fiber comes from an actual subgradient of `f*` at the image point.
  exact
    (helperForRemark_5_24_1_mem_subdifferentialEffectiveDomain_iff_nonempty
      (fenchelConjugate n f) (A yStar)).2 ⟨eta, hEta⟩

/-- Helper for Corollary 26.3.3: the conjugate precomposition `y* ↦ f*(A* y*)` is essentially
strictly convex under the adjoint-range qualification. -/
lemma helperForCorollary_26_3_3_essentiallyStrictlyConvex_conjugatePrecomp
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
    IsEssentiallyStrictlyConvex (fun yStar => fenchelConjugate n f (coordinateAdjointLinearMap A yStar)) := by
  let fStar : (Fin n → ℝ) → EReal := fenchelConjugate n f
  let B : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ) := coordinateAdjointLinearMap A
  have hproper : ProperConvexFunctionOn Set.univ f :=
    helperForTheorem_25_6_properConvexFunctionOn (f := f) hf
  have hconv : ConvexFunction f := by
    simpa [ConvexFunction] using hproper.1
  have hproperStar : ProperConvexFunctionOn Set.univ fStar :=
    proper_fenchelConjugate_of_proper (n := n) (f := f) hproper
  have hfStar : ProperConvexERealFunction fStar :=
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
      -- Rewriting `(f*)*` back to `f` puts Theorem 26.3 in exactly the form supplied by the
      -- hypothesis `hf_smooth`.
      simpa [fStar, hbiconj] using hf_smooth
    exact
      (essentiallyStrictlyConvex_iff_conjugate_essentiallySmooth
        (f := fStar) hfStar hfStar_closed).2 hf_bismooth
  rcases hri with ⟨y0, hy0⟩
  have hy0' : B y0 ∈
      euclideanRelativeInterior_fin n
        (effectiveDomain (Set.univ : Set (Fin n → ℝ)) fStar) := by
    simpa [fStar, B] using hy0
  have hRange : B y0 ∈ Set.range B := ⟨y0, rfl⟩
  have hRangeRi : RangeMeetsRelativeInteriorEffectiveDomain B fStar := ⟨B y0, hRange, hy0'⟩
  have hDomPoint : B y0 ∈ effectiveDomain Set.univ fStar :=
    helperForTheorem_19_1_mem_of_euclideanRelativeInterior_fin hy0'
  have hRangeDom : ∃ z : Fin n → ℝ, z ∈ Set.range B ∧ z ∈ effectiveDomain Set.univ fStar :=
    ⟨B y0, hRange, hDomPoint⟩
  have hprecompProper : ProperConvexFunctionOn Set.univ (fun yStar => fStar (B yStar)) :=
    helperForTheorem_23_9_precomp_proper_of_range_meets_effectiveDomain
      B fStar hproperStar hRangeDom
  refine ⟨hprecompProper, ?_⟩
  intro C hCSubset hCConv
  have hImageSubset : B '' C ⊆ subdifferentialEffectiveDomain fStar := by
    rintro _ ⟨u, hu, rfl⟩
    exact
      helperForCorollary_26_3_3_mem_conjugateSubdiffDomain_of_mem_precompSubdiffDomain
        f B hproperStar hRangeRi (hCSubset hu)
  have hImageConv : Convex ℝ (B '' C) := hCConv.linear_image B
  have hStrictImage : StrictConvexOn ℝ (B '' C) (fun z => (fStar z).toReal) :=
    hfStar_essStrict.2 hImageSubset hImageConv
  refine ⟨hCConv, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hxImage : B x ∈ B '' C := ⟨x, hx, rfl⟩
  have hyImage : B y ∈ B '' C := ⟨y, hy, rfl⟩
  have hxyImage : B x ≠ B y :=
    (helperForCorollary_26_3_3_coordinateAdjoint_injective_of_surjective A hA).ne hxy
  -- Strict convexity of `f*` on the image domain pulls back along the injective adjoint map.
  have hStrict := hStrictImage.2 hxImage hyImage hxyImage ha hb hab
  simpa [fStar, B, map_add, map_smul] using hStrict

/-- Helper for Corollary 26.3.3: taking the coordinate adjoint twice recovers the original
linear map. -/
lemma helperForCorollary_26_3_3_coordinateAdjoint_involutive {n m : ℕ}
    (A : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) :
    coordinateAdjointLinearMap (coordinateAdjointLinearMap A) = A := by
  apply LinearMap.ext
  intro x
  apply sub_eq_zero.mp
  apply dotProduct_eq_zero
  intro y
  have hleft :=
    helperForCorollary_26_3_3_dotProduct_coordinateAdjoint
      (coordinateAdjointLinearMap A) y x
  -- Compare both sides against every test vector `y`; the double-adjoint relation is then a
  -- direct consequence of the dot-product adjoint identities.
  calc
    dotProduct ((coordinateAdjointLinearMap (coordinateAdjointLinearMap A)) x - A x) y
        = dotProduct y ((coordinateAdjointLinearMap (coordinateAdjointLinearMap A)) x - A x) := by
            rw [dotProduct_comm]
    _ = dotProduct y ((coordinateAdjointLinearMap (coordinateAdjointLinearMap A)) x) -
          dotProduct y (A x) := by
            simp [dotProduct_sub]
    _ = dotProduct ((coordinateAdjointLinearMap A) y) x - dotProduct y (A x) := by
          rw [← hleft]
    _ = dotProduct ((coordinateAdjointLinearMap A) y) x - dotProduct (A x) y := by
          simp [dotProduct_comm]
    _ = dotProduct (A x) y - dotProduct (A x) y := by
          rw [dotProduct_comm,
            (helperForCorollary_26_3_3_dotProduct_coordinateAdjoint A x y).symm]
    _ = 0 := by
          ring

/-- Helper for Corollary 26.3.3: under the relative-interior qualification, the conjugate of the
precomposition `h ∘ A` is the image of `h*` under the coordinate adjoint of `A`. -/
lemma helperForCorollary_26_3_3_fenchelConjugate_coordinateAdjointPrecomp_eq_imageUnderLinearMap
    {n m : ℕ} (h : (Fin n → ℝ) → EReal) (A : (Fin m → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    (hconv : ConvexFunction h)
    (hri : RangeMeetsRelativeInteriorEffectiveDomain A h) :
    fenchelConjugate m (fun y => h (A y)) =
      imageUnderLinearMap (coordinateAdjointLinearMap A) (fenchelConjugate n h) := by
  rcases hri with ⟨z, hzRange, hzri⟩
  rcases hzRange with ⟨y0, rfl⟩
  have hriEuclid :
      ∃ x : EuclideanSpace ℝ (Fin m),
        helperForTheorem_23_9_euclideanLinearLift A x ∈
          euclideanRelativeInterior n
            ((fun z : EuclideanSpace ℝ (Fin n) => (z : Fin n → ℝ)) ⁻¹'
              effectiveDomain Set.univ h) := by
    refine ⟨WithLp.toLp 2 y0, ?_⟩
    have hzri' :
        (EuclideanSpace.equiv (Fin n) ℝ).symm (A y0) ∈
          euclideanRelativeInterior n
            ((EuclideanSpace.equiv (Fin n) ℝ).symm '' effectiveDomain Set.univ h) :=
      (mem_euclideanRelativeInterior_fin_iff
        (n := n) (C := effectiveDomain Set.univ h) (x := A y0)).1 hzri
    -- Rephrase the coordinate witness in the Euclidean-space model required by Section 16.
    simpa [helperForTheorem_23_9_euclideanLinearLift,
      helperForTheorem_23_4_preimage_eq_symmImage] using hzri'
  have hsec :=
    section16_fenchelConjugate_precomp_eq_adjoint_image_of_exists_mem_ri_effectiveDomain
      (A := helperForTheorem_23_9_euclideanLinearLift A) (g := h) hconv hriEuclid
  have hraw :
      (fun xStar : Fin m → ℝ =>
        sInf
          ((fun yStar : EuclideanSpace ℝ (Fin n) => fenchelConjugate n h (yStar : Fin n → ℝ)) ''
            {yStar |
              (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
                WithLp.toLp 2 xStar})) =
        imageUnderLinearMap (coordinateAdjointLinearMap A) (fenchelConjugate n h) := by
    -- The raw Section 16 fiber formula is exactly the coordinate-space `imageUnderLinearMap`.
    simpa [coordinateAdjointLinearMap] using
      helperForTheorem_23_9_rawAdjointImage_eq_imageUnderCoordinateAdjoint A h
  calc
    fenchelConjugate m (fun y => h (A y)) =
        (fun xStar : Fin m → ℝ =>
          sInf
            ((fun yStar : EuclideanSpace ℝ (Fin n) => fenchelConjugate n h (yStar : Fin n → ℝ)) ''
              {yStar |
                (LinearMap.adjoint (helperForTheorem_23_9_euclideanLinearLift A)) yStar =
                  WithLp.toLp 2 xStar})) := hsec.1
    _ = imageUnderLinearMap (coordinateAdjointLinearMap A) (fenchelConjugate n h) := hraw

end Section26
end Chap05
