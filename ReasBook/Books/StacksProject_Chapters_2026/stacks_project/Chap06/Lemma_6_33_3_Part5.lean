module

public import stacks_project.Chap06.Lemma_6_33_3_Part4

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}}

local instance : HasLimits (Type w) := inferInstance
local instance : HasColimits (Type w) := inferInstance
local instance : PreservesLimits (forget (Type w)) := inferInstance
local instance : PreservesFilteredColimits (forget (Type w)) :=
  PreservesColimits.preservesFilteredColimits (forget (Type w))
local instance : (forget (Type w)).ReflectsIsomorphisms := inferInstance

variable {C : Type (w + 1)} [Category.{w} C] (F : C ⥤ Type w) [IsAlgebraicStructure C F]

variable {ι : Type u} {U : ι → Opens X}

local notation "algRestrictToOpen" => algebraicRestrictToOpen
local notation "algRestrictToPairLeft" => algebraicRestrictToPairLeft
local notation "algRestrictToPairRight" => algebraicRestrictToPairRight
local notation "algRestrictToTripleFirst" => algebraicRestrictToTripleFirst
local notation "algRestrictToTripleSecond" => algebraicRestrictToTripleSecond
local notation "algRestrictToTripleThird" => algebraicRestrictToTripleThird
local notation "algRestrictOverlapToTripleLeft" => algebraicRestrictOverlapToTripleLeft
local notation "algRestrictOverlapToTripleCenter" =>
  algebraicRestrictOverlapToTripleCenter
local notation "algRestrictOverlapToTripleOuter" =>
  algebraicRestrictOverlapToTripleOuter

theorem algebraicTripleOverlap_normalized
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    {W : Opens X} {i j k : ι} (hWijk : W ≤ U i ⊓ U j ⊓ U k) :
    (algebraicTripleOverlapHom12 localSheaf overlapIso i j k).hom.app
        (op (subspaceOpenOfLE hWijk)) ≫
      (algebraicTripleOverlapHom23 localSheaf overlapIso i j k).hom.app
        (op (subspaceOpenOfLE hWijk)) =
    (algebraicTripleOverlapHom13 localSheaf overlapIso i j k).hom.app
        (op (subspaceOpenOfLE hWijk)) := by
  exact sheafHomAppCongr (V := subspaceOpenOfLE hWijk) (cocycle i j k)

theorem algebraicSubsetChartIso_trans
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    {W : Opens X} {i j k : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j) (hWk : W ≤ U k) :
    (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom ≫
        (algebraicSubsetChartIso localSheaf overlapIso hWj hWk).hom =
      (algebraicSubsetChartIso localSheaf overlapIso hWi hWk).hom := by
  let hWijk : W ≤ U i ⊓ U j ⊓ U k :=
    subset_triple_overlap_le (U := U) hWi hWj hWk
  let hTripleLeft : U i ⊓ U j ⊓ U k ≤ U i ⊓ U j := inf_le_left
  let hTripleCenter : U i ⊓ U j ⊓ U k ≤ U j ⊓ U k := by
    intro x hx
    exact ⟨hx.1.2, hx.2⟩
  let hTripleOuter : U i ⊓ U j ⊓ U k ≤ U i ⊓ U k := by
    intro x hx
    exact ⟨hx.1.1, hx.2⟩
  let hTripleFirst : U i ⊓ U j ⊓ U k ≤ U i := hTripleLeft.trans inf_le_left
  let hTripleSecond : U i ⊓ U j ⊓ U k ≤ U j := hTripleLeft.trans inf_le_right
  let hTripleThird : U i ⊓ U j ⊓ U k ≤ U k := inf_le_right
  let directFirst :=
    openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleFirst (localSheaf i)
  let directSecond :=
    openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleSecond (localSheaf j)
  let directThird :=
    openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleThird (localSheaf k)
  let left12 :=
    (algebraicTripleOverlapHom12 localSheaf overlapIso i j k).hom.app
      (op (subspaceOpenOfLE hWijk))
  let left23 :=
    (algebraicTripleOverlapHom23 localSheaf overlapIso i j k).hom.app
      (op (subspaceOpenOfLE hWijk))
  let left13 :=
    (algebraicTripleOverlapHom13 localSheaf overlapIso i j k).hom.app
      (op (subspaceOpenOfLE hWijk))
  have h12 :
      directFirst.hom ≫
          (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom ≫
          directSecond.inv =
        left12 := by
    let hWij := subset_overlap_le (U := U) hWi hWj
    let eLeft := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left (localSheaf i)
    let eRight := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right (localSheaf j)
    let ePairLeft :=
      openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleLeft
        (((openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
          C).obj (localSheaf i))
    let ePairRight :=
      openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleLeft
        (((openSubsetIntersectionRightInclusion_isOpenEmbedding (U i) (U j)).sheafPullback
          C).obj (localSheaf j))
    let overlapIsoSections :
        ((algRestrictToPairLeft (U i) (U j)).obj (localSheaf i)).1 ≅
          ((algRestrictToPairRight (U i) (U j)).obj (localSheaf j)).1 :=
      (TopCat.Sheaf.forget C (openSubsetSpace (U i ⊓ U j))).mapIso (overlapIso i j)
    have hleft :
        directFirst.hom ≫ eLeft.inv =
          (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            ePairLeft.hom := by
      simpa [directFirst, eLeft, ePairLeft, hTripleFirst, hTripleLeft, Category.assoc] using
        openSubsetHomOfLEOpenEmbeddingSectionIso_forward_endpoint_compare
          hWijk hTripleLeft inf_le_left (localSheaf i)
    have hmiddle :
        ePairLeft.hom ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
            ePairRight.inv =
          ((((algRestrictOverlapToTripleLeft (U i) (U j) (U k)).map
                (overlapIso i j).hom)).hom.app
              (op (subspaceOpenOfLE hWijk))) := by
      simpa only [ePairLeft, ePairRight, overlapIsoSections] using
        openSubsetHomOfLEOpenEmbeddingSectionIso_map_compare
          hWijk hTripleLeft (overlapIso i j).hom
    have hright :
        eRight.hom ≫ directSecond.inv =
          ePairRight.inv ≫
            (((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
                (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) := by
      simpa [directSecond, eRight, ePairRight, hTripleSecond, hTripleLeft, Category.assoc] using
        (openSubsetHomOfLEOpenEmbeddingSectionIso_inverse_endpoint_compare
          hWijk hTripleLeft inf_le_right (localSheaf j)).symm
    have hstep1 :
        directFirst.hom ≫
            (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom ≫
            directSecond.inv =
          directFirst.hom ≫ eLeft.inv ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
            eRight.hom ≫ directSecond.inv := by
      simpa only [eLeft, eRight, overlapIsoSections, Category.assoc] using
        congrArg (fun t ↦ directFirst.hom ≫ t ≫ directSecond.inv)
          (algebraicSubsetChartIso_hom localSheaf overlapIso hWi hWj)
    have hstep2 :
        directFirst.hom ≫ eLeft.inv ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
            eRight.hom ≫ directSecond.inv =
          (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            ePairLeft.hom ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
            eRight.hom ≫ directSecond.inv := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
              eRight.hom ≫ directSecond.inv)
          hleft
    have hstep3 :
        (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
            (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
          eRight.hom ≫ directSecond.inv =
        (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
            (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
          ePairRight.inv ≫
          (((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
              (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
              ePairLeft.hom ≫
              overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫ t)
          hright
    have hstep4 :
        (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
            (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
          ePairRight.inv ≫
          (((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
              (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) =
        left12 := by
      have hgrouped :
          (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            (ePairLeft.hom ≫
              overlapIsoSections.hom.app (op (subspaceOpenOfLE hWij)) ≫
              ePairRight.inv) ≫
            (((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
                (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) =
          left12 := by
        simpa only [left12, algebraicTripleOverlapHom12, Functor.mapIso_hom,
          TopCat.Sheaf.comp_app] using
          congrArg
            (fun t ↦
              (((algebraicRestrictToTripleFirstViaIJIso (U i) (U j) (U k)).hom.app
                (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫ t ≫
                (((algebraicRestrictToTripleSecondViaIJIso (U i) (U j) (U k)).inv.app
                  (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))))
            hmiddle
      simpa only [Category.assoc] using hgrouped
    exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  have h23 :
      directSecond.hom ≫
          (algebraicSubsetChartIso localSheaf overlapIso hWj hWk).hom ≫
          directThird.inv =
        left23 := by
    let hWjk := subset_overlap_le (U := U) hWj hWk
    let eLeft := openSubsetHomOfLEOpenEmbeddingSectionIso hWjk inf_le_left (localSheaf j)
    let eRight := openSubsetHomOfLEOpenEmbeddingSectionIso hWjk inf_le_right (localSheaf k)
    let ePairLeft :=
      openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleCenter
        (((openSubsetIntersectionLeftInclusion_isOpenEmbedding (U j) (U k)).sheafPullback
          C).obj (localSheaf j))
    let ePairRight :=
      openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleCenter
        (((openSubsetIntersectionRightInclusion_isOpenEmbedding (U j) (U k)).sheafPullback
          C).obj (localSheaf k))
    let overlapIsoSections :
        ((algRestrictToPairLeft (U j) (U k)).obj (localSheaf j)).1 ≅
          ((algRestrictToPairRight (U j) (U k)).obj (localSheaf k)).1 :=
      (TopCat.Sheaf.forget C (openSubsetSpace (U j ⊓ U k))).mapIso (overlapIso j k)
    have hleft :
        directSecond.hom ≫ eLeft.inv =
          (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
              (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            ePairLeft.hom := by
      simpa [directSecond, eLeft, ePairLeft, hTripleSecond, hTripleCenter, Category.assoc] using
        openSubsetHomOfLEOpenEmbeddingSectionIso_forward_endpoint_compare
          hWijk hTripleCenter inf_le_left (localSheaf j)
    have hmiddle :
        ePairLeft.hom ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
            ePairRight.inv =
          ((((algRestrictOverlapToTripleCenter (U i) (U j) (U k)).map
                (overlapIso j k).hom)).hom.app
              (op (subspaceOpenOfLE hWijk))) := by
      simpa only [ePairLeft, ePairRight, overlapIsoSections] using
        openSubsetHomOfLEOpenEmbeddingSectionIso_map_compare
          hWijk hTripleCenter (overlapIso j k).hom
    have hright :
        eRight.hom ≫ directThird.inv =
          ePairRight.inv ≫
            (((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
                (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) := by
      simpa [directThird, eRight, ePairRight, hTripleThird, hTripleCenter, Category.assoc] using
        (openSubsetHomOfLEOpenEmbeddingSectionIso_inverse_endpoint_compare
          hWijk hTripleCenter inf_le_right (localSheaf k)).symm
    have hstep1 :
        directSecond.hom ≫
            (algebraicSubsetChartIso localSheaf overlapIso hWj hWk).hom ≫
            directThird.inv =
          directSecond.hom ≫ eLeft.inv ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
            eRight.hom ≫ directThird.inv := by
      simpa only [eLeft, eRight, overlapIsoSections, Category.assoc] using
        congrArg (fun t ↦ directSecond.hom ≫ t ≫ directThird.inv)
          (algebraicSubsetChartIso_hom localSheaf overlapIso hWj hWk)
    have hstep2 :
        directSecond.hom ≫ eLeft.inv ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
            eRight.hom ≫ directThird.inv =
          (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
              (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            ePairLeft.hom ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
            eRight.hom ≫ directThird.inv := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
              eRight.hom ≫ directThird.inv)
          hleft
    have hstep3 :
        (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
            (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
          eRight.hom ≫ directThird.inv =
        (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
            (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
          ePairRight.inv ≫
          (((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
              (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
              (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
              ePairLeft.hom ≫
              overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫ t)
          hright
    have hstep4 :
        (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
            (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
          ePairRight.inv ≫
          (((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
              (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) =
        left23 := by
      have hgrouped :
          (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
              (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            (ePairLeft.hom ≫
              overlapIsoSections.hom.app (op (subspaceOpenOfLE hWjk)) ≫
              ePairRight.inv) ≫
            (((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
                (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) =
          left23 := by
        simpa only [left23, algebraicTripleOverlapHom23, Functor.mapIso_hom,
          TopCat.Sheaf.comp_app] using
          congrArg
            (fun t ↦
              (((algebraicRestrictToTripleSecondViaJKIso (U i) (U j) (U k)).hom.app
                (localSheaf j)).hom.app (op (subspaceOpenOfLE hWijk))) ≫ t ≫
                (((algebraicRestrictToTripleThirdViaJKIso (U i) (U j) (U k)).inv.app
                  (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))))
            hmiddle
      simpa only [Category.assoc] using hgrouped
    exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  have h13 :
      directFirst.hom ≫
          (algebraicSubsetChartIso localSheaf overlapIso hWi hWk).hom ≫
          directThird.inv =
        left13 := by
    let hWik := subset_overlap_le (U := U) hWi hWk
    let eLeft := openSubsetHomOfLEOpenEmbeddingSectionIso hWik inf_le_left (localSheaf i)
    let eRight := openSubsetHomOfLEOpenEmbeddingSectionIso hWik inf_le_right (localSheaf k)
    let ePairLeft :=
      openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleOuter
        (((openSubsetIntersectionLeftInclusion_isOpenEmbedding (U i) (U k)).sheafPullback
          C).obj (localSheaf i))
    let ePairRight :=
      openSubsetHomOfLEOpenEmbeddingSectionIso hWijk hTripleOuter
        (((openSubsetIntersectionRightInclusion_isOpenEmbedding (U i) (U k)).sheafPullback
          C).obj (localSheaf k))
    let overlapIsoSections :
        ((algRestrictToPairLeft (U i) (U k)).obj (localSheaf i)).1 ≅
          ((algRestrictToPairRight (U i) (U k)).obj (localSheaf k)).1 :=
      (TopCat.Sheaf.forget C (openSubsetSpace (U i ⊓ U k))).mapIso (overlapIso i k)
    have hleft :
        directFirst.hom ≫ eLeft.inv =
          (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            ePairLeft.hom := by
      simpa [directFirst, eLeft, ePairLeft, hTripleFirst, hTripleOuter, Category.assoc] using
        openSubsetHomOfLEOpenEmbeddingSectionIso_forward_endpoint_compare
          hWijk hTripleOuter inf_le_left (localSheaf i)
    have hmiddle :
        ePairLeft.hom ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
            ePairRight.inv =
          ((((algRestrictOverlapToTripleOuter (U i) (U j) (U k)).map
                (overlapIso i k).hom)).hom.app
              (op (subspaceOpenOfLE hWijk))) := by
      simpa only [ePairLeft, ePairRight, overlapIsoSections] using
        openSubsetHomOfLEOpenEmbeddingSectionIso_map_compare
          hWijk hTripleOuter (overlapIso i k).hom
    have hright :
        eRight.hom ≫ directThird.inv =
          ePairRight.inv ≫
            (((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
                (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) := by
      simpa [directThird, eRight, ePairRight, hTripleThird, hTripleOuter, Category.assoc] using
        (openSubsetHomOfLEOpenEmbeddingSectionIso_inverse_endpoint_compare
          hWijk hTripleOuter inf_le_right (localSheaf k)).symm
    have hstep1 :
        directFirst.hom ≫
            (algebraicSubsetChartIso localSheaf overlapIso hWi hWk).hom ≫
            directThird.inv =
          directFirst.hom ≫ eLeft.inv ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
            eRight.hom ≫ directThird.inv := by
      simpa only [eLeft, eRight, overlapIsoSections, Category.assoc] using
        congrArg (fun t ↦ directFirst.hom ≫ t ≫ directThird.inv)
          (algebraicSubsetChartIso_hom localSheaf overlapIso hWi hWk)
    have hstep2 :
        directFirst.hom ≫ eLeft.inv ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
            eRight.hom ≫ directThird.inv =
          (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            ePairLeft.hom ≫
            overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
            eRight.hom ≫ directThird.inv := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            t ≫ overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
              eRight.hom ≫ directThird.inv)
          hleft
    have hstep3 :
        (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
            (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
          eRight.hom ≫ directThird.inv =
        (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
            (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
          ePairRight.inv ≫
          (((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
              (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) := by
      simpa [Category.assoc] using
        congrArg
          (fun t ↦
            (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
              ePairLeft.hom ≫
              overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫ t)
          hright
    have hstep4 :
        (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
            (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
          ePairLeft.hom ≫
          overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
          ePairRight.inv ≫
          (((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
              (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) =
        left13 := by
      have hgrouped :
          (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
              (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫
            (ePairLeft.hom ≫
              overlapIsoSections.hom.app (op (subspaceOpenOfLE hWik)) ≫
              ePairRight.inv) ≫
            (((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
                (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))) =
          left13 := by
        simpa only [left13, algebraicTripleOverlapHom13, Functor.mapIso_hom,
          TopCat.Sheaf.comp_app] using
          congrArg
            (fun t ↦
              (((algebraicRestrictToTripleFirstViaIKIso (U i) (U j) (U k)).hom.app
                (localSheaf i)).hom.app (op (subspaceOpenOfLE hWijk))) ≫ t ≫
                (((algebraicRestrictToTripleThirdViaIKIso (U i) (U j) (U k)).inv.app
                  (localSheaf k)).hom.app (op (subspaceOpenOfLE hWijk))))
            hmiddle
      simpa only [Category.assoc] using hgrouped
    exact hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  have hnorm := algebraicTripleOverlap_normalized localSheaf overlapIso cocycle hWijk
  have hs12 :
      (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom =
        directFirst.inv ≫ left12 ≫ directSecond.hom := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ directFirst.inv ≫ t ≫ directSecond.hom) h12
  have hs23 :
      (algebraicSubsetChartIso localSheaf overlapIso hWj hWk).hom =
        directSecond.inv ≫ left23 ≫ directThird.hom := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ directSecond.inv ≫ t ≫ directThird.hom) h23
  have hs13 :
      (algebraicSubsetChartIso localSheaf overlapIso hWi hWk).hom =
        directFirst.inv ≫ left13 ≫ directThird.hom := by
    simpa [Category.assoc] using
      congrArg (fun t ↦ directFirst.inv ≫ t ≫ directThird.hom) h13
  calc
    (algebraicSubsetChartIso localSheaf overlapIso hWi hWj).hom ≫
        (algebraicSubsetChartIso localSheaf overlapIso hWj hWk).hom
        =
      (directFirst.inv ≫ left12 ≫ directSecond.hom) ≫
        (directSecond.inv ≫ left23 ≫ directThird.hom) := by
          rw [hs12, hs23]
    _ = directFirst.inv ≫ left12 ≫ left23 ≫ directThird.hom := by
          simp [Category.assoc]
    _ = directFirst.inv ≫ left13 ≫ directThird.hom := by
          simpa [left12, left23, left13, Category.assoc] using
            congrArg (fun t ↦ directFirst.inv ≫ t ≫ directThird.hom) hnorm
    _ = (algebraicSubsetChartIso localSheaf overlapIso hWi hWk).hom := by
          rw [hs13]

theorem algebraicSubsetChartIso_self_hom
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    (algebraicSubsetChartIso localSheaf overlapIso hWi hWi).hom = 𝟙 _ := by
  let e := algebraicSubsetChartIso localSheaf overlapIso hWi hWi
  apply (cancel_mono e.hom).1
  simpa [e, Category.assoc] using
    (algebraicSubsetChartIso_trans localSheaf overlapIso cocycle hWi hWi hWi :
      e.hom ≫ e.hom = e.hom)

theorem algebraicOpenCoverBasisPresheafMap_id
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso) :
    ∀ W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ,
      algebraicOpenCoverBasisPresheafMap localSheaf overlapIso (𝟙 W) = 𝟙 _ := by
  intro W
  dsimp [algebraicOpenCoverBasisPresheafMap]
  have hsub :
      subspaceOpenHom (chosen_chart_le W.unop) (chosen_chart_le W.unop)
          (show W.unop.obj ≤ W.unop.obj from le_rfl) = 𝟙 _ := by
    apply Subsingleton.elim
  rw [hsub]
  simpa using
    algebraicSubsetChartIso_self_hom localSheaf overlapIso cocycle (chosen_chart_le W.unop)

theorem algebraicOpenCoverBasisPresheafMap_comp
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso) :
    ∀ {A B D : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ}
      (iAB : A ⟶ B) (iBD : B ⟶ D),
      algebraicOpenCoverBasisPresheafMap localSheaf overlapIso (iAB ≫ iBD) =
        algebraicOpenCoverBasisPresheafMap localSheaf overlapIso iAB ≫
          algebraicOpenCoverBasisPresheafMap localSheaf overlapIso iBD := by
  intro A B D iAB iBD
  let hBA : B.unop.obj ≤ A.unop.obj := iAB.unop.hom.le
  let hDB : D.unop.obj ≤ B.unop.obj := iBD.unop.hom.le
  let hDA : D.unop.obj ≤ A.unop.obj := hDB.trans hBA
  let cA := chosen_chart A.unop
  let cB := chosen_chart B.unop
  let cD := chosen_chart D.unop
  let hAcA : A.unop.obj ≤ U cA := chosen_chart_le A.unop
  let hBcB : B.unop.obj ≤ U cB := chosen_chart_le B.unop
  let hDcD : D.unop.obj ≤ U cD := chosen_chart_le D.unop
  let hBcA : B.unop.obj ≤ U cA := hBA.trans hAcA
  let hDcA : D.unop.obj ≤ U cA := hDA.trans hAcA
  let hDcB : D.unop.obj ≤ U cB := hDB.trans hBcB
  let rAB : subspaceOpenOfLE hBcA ⟶ subspaceOpenOfLE hAcA :=
    subspaceOpenHom hBcA hAcA hBA
  let rBD_A : subspaceOpenOfLE hDcA ⟶ subspaceOpenOfLE hBcA :=
    subspaceOpenHom hDcA hBcA hDB
  let rBD_B : subspaceOpenOfLE hDcB ⟶ subspaceOpenOfLE hBcB :=
    subspaceOpenHom hDcB hBcB hDB
  let rAD : subspaceOpenOfLE hDcA ⟶ subspaceOpenOfLE hAcA :=
    subspaceOpenHom hDcA hAcA hDA
  have hrcomp : rBD_A ≫ rAB = rAD := by
    apply Subsingleton.elim
  have hmapA :
      (localSheaf cA).1.map rAD.op =
        (localSheaf cA).1.map rAB.op ≫ (localSheaf cA).1.map rBD_A.op := by
    calc
      (localSheaf cA).1.map rAD.op = (localSheaf cA).1.map ((rBD_A ≫ rAB).op) := by
        simpa [hrcomp]
      _ = (localSheaf cA).1.map rAB.op ≫ (localSheaf cA).1.map rBD_A.op := by
        simp [Functor.map_comp]
  have hnat :=
    algebraicSubsetChartIso_naturality localSheaf overlapIso (hVW := hDB)
      (hVi := hDcA) (hVj := hDcB) (hWi := hBcA) (hWj := hBcB)
  have htrans :=
    algebraicSubsetChartIso_trans localSheaf overlapIso cocycle hDcA hDcB hDcD
  calc
    algebraicOpenCoverBasisPresheafMap localSheaf overlapIso (iAB ≫ iBD)
        = (localSheaf cA).1.map rAD.op ≫
            (algebraicSubsetChartIso localSheaf overlapIso hDcA hDcD).hom := by
          rfl
    _ = ((localSheaf cA).1.map rAB.op ≫ (localSheaf cA).1.map rBD_A.op) ≫
            (algebraicSubsetChartIso localSheaf overlapIso hDcA hDcD).hom := by
          rw [hmapA]
    _ = (localSheaf cA).1.map rAB.op ≫
          ((localSheaf cA).1.map rBD_A.op ≫
            ((algebraicSubsetChartIso localSheaf overlapIso hDcA hDcB).hom ≫
              (algebraicSubsetChartIso localSheaf overlapIso hDcB hDcD).hom)) := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ (localSheaf cA).1.map rAB.op ≫
              ((localSheaf cA).1.map rBD_A.op ≫ t)) htrans.symm
    _ = (localSheaf cA).1.map rAB.op ≫
          (((algebraicSubsetChartIso localSheaf overlapIso hBcA hBcB).hom ≫
              (localSheaf cB).1.map rBD_B.op) ≫
            (algebraicSubsetChartIso localSheaf overlapIso hDcB hDcD).hom) := by
          simpa only [Category.assoc] using
            congrArg (fun t ↦ (localSheaf cA).1.map rAB.op ≫
              (t ≫ (algebraicSubsetChartIso localSheaf overlapIso hDcB hDcD).hom)) hnat
    _ = algebraicOpenCoverBasisPresheafMap localSheaf overlapIso iAB ≫
          algebraicOpenCoverBasisPresheafMap localSheaf overlapIso iBD := by
          simpa [algebraicOpenCoverBasisPresheafMap, cA, cB, cD, hBcA, hDcB,
            rAB, rBD_B, Category.assoc]

noncomputable def algebraicOpenCoverBasisPresheaf
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso) :
    (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ ⥤ C where
  obj W := algebraicOpenCoverBasisPresheafObj localSheaf W
  map f := algebraicOpenCoverBasisPresheafMap localSheaf overlapIso f
  map_id := algebraicOpenCoverBasisPresheafMap_id localSheaf overlapIso cocycle
  map_comp := algebraicOpenCoverBasisPresheafMap_comp localSheaf overlapIso cocycle

theorem algebraicBasisCoverTransportToFixedChart_compatible
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    {W0 : BasisOpen (coverSubordinateOpens (U := U))}
    (𝒰 : BasisCover (coverSubordinateOpens (U := U)) W0)
    (hInter :
      ∀ i j : 𝒰.ι, ((𝒰.obj i).obj ⊓ (𝒰.obj j).obj) ∈ coverSubordinateOpens (U := U))
    (s : FamilyOfElementsOnObjects
      ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F) 𝒰.obj)
    (hs : s.IsCompatible) :
    TopCat.Presheaf.IsCompatible
      ((algebraicToTypes F (U (chosen_chart W0))).obj (localSheaf (chosen_chart W0))).1
      (fun i ↦ subspaceOpenOfLE ((𝒰.hom i).hom.le.trans (chosen_chart_le W0)))
      (fun i ↦
        F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (chosen_chart_le (𝒰.obj i))
            ((𝒰.hom i).hom.le.trans (chosen_chart_le W0))).hom
          (s i)) := by
  intro i j
  let c0 := chosen_chart W0
  let ci := chosen_chart (𝒰.obj i)
  let cj := chosen_chart (𝒰.obj j)
  let hI0 : (𝒰.obj i).obj ≤ U c0 := (𝒰.hom i).hom.le.trans (chosen_chart_le W0)
  let hJ0 : (𝒰.obj j).obj ≤ U c0 := (𝒰.hom j).hom.le.trans (chosen_chart_le W0)
  let Zij := BasisCover.actualIntersection 𝒰 hInter i j
  let hZ0 : Zij.obj ≤ U c0 :=
    (BasisCover.actualIntersectionLeft 𝒰 hInter i j).hom.le.trans hI0
  let kLeft := BasisCover.actualIntersectionLeft 𝒰 hInter i j
  let kRight := BasisCover.actualIntersectionRight 𝒰 hInter i j
  have hleft_nat :=
    algebraicSubsetChartIso_naturality localSheaf overlapIso
      (hVW := kLeft.hom.le)
      (hVi := kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
      (hVj := hZ0)
      (hWi := chosen_chart_le (𝒰.obj i))
      (hWj := hI0)
  have hright_nat :=
    algebraicSubsetChartIso_naturality localSheaf overlapIso
      (hVW := kRight.hom.le)
      (hVi := kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
      (hVj := hZ0)
      (hWi := chosen_chart_le (𝒰.obj j))
      (hWj := hJ0)
  have hleft_fixed :
      F.map
          ((localSheaf c0).1.map
            ((subspaceOpenOfLE hI0).infLELeft (subspaceOpenOfLE hJ0)).op)
          (F.map
            (algebraicSubsetChartIso localSheaf overlapIso
              (chosen_chart_le (𝒰.obj i)) hI0).hom
            (s i)) =
        F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i))) hZ0).hom
          (F.map
            ((localSheaf ci).1.map
              (subspaceOpenHom
                (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                (chosen_chart_le (𝒰.obj i))
                kLeft.hom.le).op)
            (s i)) := by
    have h := congrArg (fun f ↦ F.map f) hleft_nat
    have h' := congrFun h (s i)
    simpa [algebraicToTypes, c0, ci, hI0, hJ0, hZ0, subspaceOpenOfLE_inf_eq,
      Functor.map_comp, Function.comp_apply] using h'.symm
  have hright_fixed :
      F.map
          ((localSheaf c0).1.map
            ((subspaceOpenOfLE hI0).infLERight (subspaceOpenOfLE hJ0)).op)
          (F.map
            (algebraicSubsetChartIso localSheaf overlapIso
              (chosen_chart_le (𝒰.obj j)) hJ0).hom
            (s j)) =
        F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j))) hZ0).hom
          (F.map
            ((localSheaf cj).1.map
              (subspaceOpenHom
                (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                (chosen_chart_le (𝒰.obj j))
                kRight.hom.le).op)
            (s j)) := by
    have hZ0' : kRight.hom.le.trans hJ0 = hZ0 := by
      apply Subsingleton.elim
    have h := congrArg (fun f ↦ F.map f) hright_nat
    have h' := congrFun h (s j)
    simpa [algebraicToTypes, c0, cj, hI0, hJ0, hZ0, hZ0', subspaceOpenOfLE_inf_eq,
      Functor.map_comp, Function.comp_apply] using h'.symm
  have hs' :=
    (BasisCover.isCompatible_iff_actualIntersections 𝒰 hInter
      ((algebraicOpenCoverBasisPresheaf localSheaf overlapIso cocycle) ⋙ F) s).1 hs i j
  have hs_pair :
      F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
            (chosen_chart_le Zij)).hom
          (F.map
            ((localSheaf ci).1.map
              (subspaceOpenHom
                (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                (chosen_chart_le (𝒰.obj i))
                kLeft.hom.le).op)
            (s i)) =
        F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
            (chosen_chart_le Zij)).hom
          (F.map
            ((localSheaf cj).1.map
              (subspaceOpenHom
                (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                (chosen_chart_le (𝒰.obj j))
                kRight.hom.le).op)
            (s j)) := by
    simpa [Zij, ci, cj, algebraicOpenCoverBasisPresheaf,
      algebraicOpenCoverBasisPresheafMap, Functor.map_comp, Function.comp_apply] using hs'
  have hs_push :=
    congrArg
      (fun x ↦ F.map
        (algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le Zij) hZ0).hom x)
      hs_pair
  have hleft_trans :=
    algebraicSubsetChartIso_trans localSheaf overlapIso cocycle
      (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i))) (chosen_chart_le Zij) hZ0
  have hright_trans :=
    algebraicSubsetChartIso_trans localSheaf overlapIso cocycle
      (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j))) (chosen_chart_le Zij) hZ0
  have hs_middle :
      F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i))) hZ0).hom
          (F.map
            ((localSheaf ci).1.map
              (subspaceOpenHom
                (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                (chosen_chart_le (𝒰.obj i))
                kLeft.hom.le).op)
            (s i)) =
        F.map
          (algebraicSubsetChartIso localSheaf overlapIso
            (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j))) hZ0).hom
          (F.map
            ((localSheaf cj).1.map
              (subspaceOpenHom
                (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                (chosen_chart_le (𝒰.obj j))
                kRight.hom.le).op)
            (s j)) := by
    have hleft_nested :
        F.map
            (algebraicSubsetChartIso localSheaf overlapIso
              (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i))) hZ0).hom
            (F.map
              ((localSheaf ci).1.map
                (subspaceOpenHom
                  (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                  (chosen_chart_le (𝒰.obj i))
                  kLeft.hom.le).op)
              (s i)) =
          F.map
            (algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le Zij) hZ0).hom
            (F.map
              (algebraicSubsetChartIso localSheaf overlapIso
                (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                (chosen_chart_le Zij)).hom
              (F.map
                ((localSheaf ci).1.map
                  (subspaceOpenHom
                    (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
                    (chosen_chart_le (𝒰.obj i))
                    kLeft.hom.le).op)
                (s i))) := by
      have h := congrArg (fun f ↦ F.map f)
        (hleft_trans.symm)
      have h' := congrFun h
        (F.map
          ((localSheaf ci).1.map
            (subspaceOpenHom
              (kLeft.hom.le.trans (chosen_chart_le (𝒰.obj i)))
              (chosen_chart_le (𝒰.obj i))
              kLeft.hom.le).op)
          (s i))
      simpa [Functor.map_comp, Function.comp_apply] using h'
    have hright_nested :
        F.map
            (algebraicSubsetChartIso localSheaf overlapIso (chosen_chart_le Zij) hZ0).hom
            (F.map
              (algebraicSubsetChartIso localSheaf overlapIso
                (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                (chosen_chart_le Zij)).hom
              (F.map
                ((localSheaf cj).1.map
                  (subspaceOpenHom
                    (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                    (chosen_chart_le (𝒰.obj j))
                    kRight.hom.le).op)
                (s j))) =
          F.map
            (algebraicSubsetChartIso localSheaf overlapIso
              (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j))) hZ0).hom
            (F.map
              ((localSheaf cj).1.map
                (subspaceOpenHom
                  (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
                  (chosen_chart_le (𝒰.obj j))
                  kRight.hom.le).op)
              (s j)) := by
      have h := congrArg (fun f ↦ F.map f) hright_trans
      have h' := congrFun h
        (F.map
          ((localSheaf cj).1.map
            (subspaceOpenHom
              (kRight.hom.le.trans (chosen_chart_le (𝒰.obj j)))
              (chosen_chart_le (𝒰.obj j))
              kRight.hom.le).op)
          (s j))
      simpa [Functor.map_comp, Function.comp_apply] using h'
    exact hleft_nested.trans (hs_push.trans hright_nested)
  exact hleft_fixed.trans (hs_middle.trans hright_fixed.symm)


end
