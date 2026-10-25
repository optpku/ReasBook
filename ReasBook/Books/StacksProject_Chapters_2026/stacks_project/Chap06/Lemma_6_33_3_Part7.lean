module

public import stacks_project.Chap06.Lemma_6_33_3_Part6
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

noncomputable def algebraicMemberSpaceBasisRestrictIso
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι) :
    algebraicBasisSiteRestrictFromSheaf
      (algebraicMemberSubordinateOpens_isBasis (U := U) i)
      (((algRestrictToOpen (U i)).obj
        ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend))) ≅
    algebraicBasisSiteRestrictFromSheaf
      (algebraicMemberSubordinateOpens_isBasis (U := U) i)
      (localSheaf i) := by
  let e :
      (algebraicBasisSiteRestrictFromSheaf
        (algebraicMemberSubordinateOpens_isBasis (U := U) i)
        (((algRestrictToOpen (U i)).obj
          ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend)))).presheaf ≅
      (algebraicBasisSiteRestrictFromSheaf
        (algebraicMemberSubordinateOpens_isBasis (U := U) i)
        (localSheaf i)).presheaf :=
    NatIso.ofComponents
      (fun V ↦ algebraicMemberSpaceBasisComponentIso
        F localSheaf overlapIso cocycle hU i V.unop)
      (by
        intro V W f
        exact algebraicMemberSpaceBasisComponent_naturality
          (F := F) localSheaf overlapIso cocycle hU i f)
  exact ObjectProperty.isoMk _ e

noncomputable def algebraicMemberRestrictExtendIso
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι) :
    ((algRestrictToOpen (U i)).obj
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend)) ≅
    localSheaf i := by
  let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
  let G := algebraicBasisSiteRestrictFromSheaf (C := C) hMi (localSheaf i)
  let Fsource :=
    ((algRestrictToOpen (U i)).obj
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend))
  exact
    (algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G Fsource
      (algebraicMemberSpaceBasisRestrictIso
        (F := F) localSheaf overlapIso cocycle hU i)) ≪≫
    (algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G (localSheaf i) (Iso.refl G)).symm

theorem algebraicMemberSpaceBasisRestrictIso_component_eq_of_rep
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
      ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
    (((algebraicMemberSpaceBasisRestrictIso (F := F) localSheaf overlapIso cocycle hU i).hom).hom.app
        (op basisW)) =
      (algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi).hom := by
  classical
  let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
    ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
  simpa [algebraicMemberSpaceBasisRestrictIso, basisW] using
    congrArg Iso.hom
      (algebraicMemberSpaceBasisComponentIso_eq_of_rep
        (F := F) localSheaf overlapIso cocycle hU i hWi)

/-- Helper for Lemma 6.33.3: restricting the inverse dense-subsite counit to a basis open gives
the canonical forward restriction-extension comparison. -/
theorem algebraicBasisSiteCounitInv_app_eq_restrictExtendComponentHom
    {Y : TopCat.{w}} {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    [HasLimitsOfSize.{w, w} C]
    (Fext : TopCat.Sheaf C Y)
    (U₀ : (BasisOpen B)ᵒᵖ) :
    ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hB).inverse.map
          ((algebraicBasisSiteSheafComparisonEquiv (C := C) hB).counitIso.app Fext).inv).hom).app U₀) =
      BasisSiteSheaf.restrictExtendComponentHom
        (algebraicBasisSiteRestrictFromSheaf (C := C) hB Fext) U₀ := by
  letI : ∀ V : (Opens Y)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (basisOpenInclusion B).op) C :=
    algebraicBasisExtension_hasLimitsOfShape (C := C) (X := Y) B
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hB
  let e : BasisSiteSheaf C B hB ≌ TopCat.Sheaf C Y :=
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology Y) C
  simpa [e, algebraicBasisSiteSheafComparisonEquiv, algebraicBasisSiteRestrictFromSheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f ↦ f.hom.app U₀) (e.unit_app_inverse Fext).symm

/-- Helper for Lemma 6.33.3: restricting the dense-subsite counit to a basis open gives the
canonical inverse restriction-extension comparison. -/
theorem algebraicBasisSiteCounitHom_app_eq_restrictExtendComponentInv
    {Y : TopCat.{w}} {B : Set (Opens Y)} (hB : Opens.IsBasis B)
    [HasLimitsOfSize.{w, w} C]
    (Fext : TopCat.Sheaf C Y)
    (U₀ : (BasisOpen B)ᵒᵖ) :
    ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hB).inverse.map
          ((algebraicBasisSiteSheafComparisonEquiv (C := C) hB).counitIso.app Fext).hom).hom).app U₀) =
      BasisSiteSheaf.restrictExtendComponentInv
        (algebraicBasisSiteRestrictFromSheaf (C := C) hB Fext) U₀ := by
  letI : ∀ V : (Opens Y)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow V (basisOpenInclusion B).op) C :=
    algebraicBasisExtension_hasLimitsOfShape (C := C) (X := Y) B
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology Y) :=
    basisOpenInclusion_isCoverDense hB
  let e : BasisSiteSheaf C B hB ≌ TopCat.Sheaf C Y :=
    (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology Y) C
  simpa [e, algebraicBasisSiteSheafComparisonEquiv, algebraicBasisSiteRestrictFromSheaf,
    BasisSiteSheaf.extend] using
    congrArg (fun f ↦ f.hom.app U₀) (e.unitInv_app_inverse Fext).symm

theorem algebraicMemberBasisComparisonInverseMapMapIsoComponent
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
    let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
      ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
    let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
    let Fsource := ((algRestrictToOpen (U i)).obj ℱ)
    let G := algebraicBasisSiteRestrictFromSheaf (C := C) hMi (localSheaf i)
    let sourceExtend :=
      BasisSiteSheaf.restrictExtendIso (algebraicBasisSiteRestrictFromSheaf (C := C) hMi Fsource)
    let targetExtend := BasisSiteSheaf.restrictExtendIso G
    let basisComp :=
      (((algebraicMemberSpaceBasisRestrictIso (F := F) localSheaf overlapIso cocycle hU i).hom).hom.app
        (op basisW))
    (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
          (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
              (algebraicMemberSpaceBasisRestrictIso (F := F) localSheaf overlapIso cocycle hU i)).hom)).hom).app
        (op basisW) =
      ((sourceExtend.inv).app (op basisW)) ≫ basisComp ≫
        ((targetExtend.hom).app (op basisW)) := by
  classical
  let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
  let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
    ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let Fsource := ((algRestrictToOpen (U i)).obj ℱ)
  let G := algebraicBasisSiteRestrictFromSheaf (C := C) hMi (localSheaf i)
  let sourceExtend :=
    BasisSiteSheaf.restrictExtendIso (algebraicBasisSiteRestrictFromSheaf (C := C) hMi Fsource)
  let targetExtend := BasisSiteSheaf.restrictExtendIso G
  let basisComp :=
    (((algebraicMemberSpaceBasisRestrictIso (F := F) localSheaf overlapIso cocycle hU i).hom).hom.app
      (op basisW))
  letI :
      (basisOpenInclusion (algebraicMemberSubordinateOpens (U := U) i)).IsCoverDense
        (Opens.grothendieckTopology (openSubsetSpace (U i))) :=
    basisOpenInclusion_isCoverDense hMi
  let e :
      BasisSiteSheaf C (algebraicMemberSubordinateOpens (U := U) i) hMi ≌
        TopCat.Sheaf C (openSubsetSpace (U i)) :=
    (basisOpenInclusion (algebraicMemberSubordinateOpens (U := U) i)).sheafInducedTopologyEquivOfIsCoverDense
      (Opens.grothendieckTopology (openSubsetSpace (U i))) C
  simpa only [e, algebraicBasisSiteSheafComparisonEquiv, algebraicBasisSiteRestrictFromSheaf,
    BasisSiteSheaf.extend, BasisSiteSheaf.restrictExtendIso, Fsource, G, sourceExtend,
    targetExtend, basisW, basisComp, Category.assoc] using
    congrArg (fun k ↦ k.hom.app (op basisW))
      (CategoryTheory.Equivalence.inv_fun_map
        (algebraicBasisSiteSheafComparisonEquiv (C := C) hMi)
        (algebraicBasisSiteRestrictFromSheaf (C := C) hMi Fsource)
        G
        (algebraicMemberSpaceBasisRestrictIso
          (F := F) localSheaf overlapIso cocycle hU i).hom)

theorem algebraicMemberRestrictExtendIso_hom_eq
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι) :
    let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
    let G := algebraicBasisSiteRestrictFromSheaf (C := C) hMi (localSheaf i)
    let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
    let Fsource := ((algRestrictToOpen (U i)).obj ℱ)
    (algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i).hom =
      (algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G Fsource
        (algebraicMemberSpaceBasisRestrictIso
          (F := F) localSheaf overlapIso cocycle hU i)).hom ≫
        (algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G
          (localSheaf i) (Iso.refl G)).inv := by
  let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
  let G := algebraicBasisSiteRestrictFromSheaf (C := C) hMi (localSheaf i)
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let Fsource := ((algRestrictToOpen (U i)).obj ℱ)
  dsimp [AlgebraicSheafOpenCover.realizationLeftHom,
    AlgebraicSheafOpenCover.realizationRightHom]
  rfl

theorem algebraicMemberRestrictExtendIso_inverseMap_app_eq_basisRestrictComponent
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
    let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
      ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
    (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
          ((algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i).hom)).hom).app
        (op basisW) =
      (((algebraicMemberSpaceBasisRestrictIso (F := F) localSheaf overlapIso cocycle hU i).hom).hom.app
        (op basisW)) := by
  classical
  let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
  let G := algebraicBasisSiteRestrictFromSheaf (C := C) hMi (localSheaf i)
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let Fsource := ((algRestrictToOpen (U i)).obj ℱ)
  let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
    ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
  let sourceExtend :=
    BasisSiteSheaf.restrictExtendIso (algebraicBasisSiteRestrictFromSheaf (C := C) hMi Fsource)
  let targetExtend := BasisSiteSheaf.restrictExtendIso G
  let basisComp :=
    (((algebraicMemberSpaceBasisRestrictIso (F := F) localSheaf overlapIso cocycle hU i).hom).hom.app
      (op basisW))
  have hleft :
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
            ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).counitIso.app Fsource).inv).hom).app
          (op basisW)) =
        ((sourceExtend.hom).app (op basisW)) := by
    simpa [sourceExtend, hMi, Fsource, basisW] using
      algebraicBasisSiteCounitInv_app_eq_restrictExtendComponentHom
        (C := C) hMi Fsource (op basisW)
  have hmid :
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
                (algebraicMemberSpaceBasisRestrictIso
                  (F := F) localSheaf overlapIso cocycle hU i)).hom)).hom).app
            (op basisW)) =
        ((sourceExtend.inv).app (op basisW)) ≫
          basisComp ≫ ((targetExtend.hom).app (op basisW)) := by
    simpa only [hMi, basisW, Fsource, G, sourceExtend, targetExtend, basisComp,
      Category.assoc] using
      algebraicMemberBasisComparisonInverseMapMapIsoComponent
        (F := F) localSheaf overlapIso cocycle hU i hWi
  have hright :
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G (localSheaf i)
                (Iso.refl G)).inv)).hom).app
            (op basisW)) =
        ((targetExtend.inv).app (op basisW)) := by
    have hrefl :
        ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
                (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
                  (Iso.refl G)).inv)).hom).app
              (op basisW)) =
          𝟙 _ := by
      simp
    have hrightCounit :
        ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
                ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).counitIso.app
                  (localSheaf i)).hom).hom).app
              (op basisW)) =
          ((targetExtend.inv).app (op basisW)) := by
      simpa [G, basisW, targetExtend] using
        algebraicBasisSiteCounitHom_app_eq_restrictExtendComponentInv
          (C := C) hMi (localSheaf i) (op basisW)
    change
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
                  (Iso.refl G)).inv ≫
                ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).counitIso.app
                  (localSheaf i)).hom)).hom).app
            (op basisW)) =
        ((targetExtend.inv).app (op basisW))
    rw [Functor.map_comp]
    change (((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
                ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
                  (Iso.refl G)).inv).hom).app
              (op basisW)) ≫
            ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
                  ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).counitIso.app
                    (localSheaf i)).hom).hom).app
                (op basisW))) =
          ((targetExtend.inv).app (op basisW))
    rw [hrefl, hrightCounit]
    simp
  have hsource :
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G Fsource
                (algebraicMemberSpaceBasisRestrictIso
                  (F := F) localSheaf overlapIso cocycle hU i)).hom)).hom).app
            (op basisW)) =
        ((sourceExtend.hom).app (op basisW)) ≫
          ((sourceExtend.inv).app (op basisW)) ≫
          basisComp ≫ ((targetExtend.hom).app (op basisW)) := by
    change
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).counitIso.app Fsource).inv ≫
                ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
                  (algebraicMemberSpaceBasisRestrictIso
                    (F := F) localSheaf overlapIso cocycle hU i)).hom)).hom).app
            (op basisW)) =
        ((sourceExtend.hom).app (op basisW)) ≫
          ((sourceExtend.inv).app (op basisW)) ≫
          basisComp ≫ ((targetExtend.hom).app (op basisW))
    rw [Functor.map_comp]
    change
      ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
            ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).counitIso.app Fsource).inv).hom).app
          (op basisW)) ≫
        ((((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).functor.mapIso
                (algebraicMemberSpaceBasisRestrictIso
                  (F := F) localSheaf overlapIso cocycle hU i)).hom).hom).app
            (op basisW)) =
      ((sourceExtend.hom).app (op basisW)) ≫
        ((sourceExtend.inv).app (op basisW)) ≫
        basisComp ≫ ((targetExtend.hom).app (op basisW))
    rw [hleft, hmid]
    rfl
  have hsplit :
      (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
            ((algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i).hom)).hom).app
          (op basisW) =
        (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G Fsource
                (algebraicMemberSpaceBasisRestrictIso
                  (F := F) localSheaf overlapIso cocycle hU i)).hom)).hom).app
            (op basisW) ≫
          (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G
                (localSheaf i) (Iso.refl G)).inv)).hom).app
            (op basisW) := by
    rw [algebraicMemberRestrictExtendIso_hom_eq]
    rw [Functor.map_comp]
    rfl
  have hsourceCancel :
      ((sourceExtend.hom).app (op basisW)) ≫ ((sourceExtend.inv).app (op basisW)) =
        𝟙 _ := by
    change ((sourceExtend.hom ≫ sourceExtend.inv).app (op basisW)) = 𝟙 _
    simpa using congrArg (fun f ↦ f.app (op basisW)) sourceExtend.hom_inv_id
  have htargetCancel :
      ((targetExtend.hom).app (op basisW)) ≫ ((targetExtend.inv).app (op basisW)) =
        𝟙 _ := by
    change ((targetExtend.hom ≫ targetExtend.inv).app (op basisW)) = 𝟙 _
    simpa using congrArg (fun f ↦ f.app (op basisW)) targetExtend.hom_inv_id
  calc
    (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
          ((algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i).hom)).hom).app
        (op basisW)
      =
        (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G Fsource
                (algebraicMemberSpaceBasisRestrictIso
                  (F := F) localSheaf overlapIso cocycle hU i)).hom)).hom).app
            (op basisW) ≫
          (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
              ((algebraicBasisSiteIsoExtendOfRestrictIso (C := C) hMi G
                (localSheaf i) (Iso.refl G)).inv)).hom).app
            (op basisW) := hsplit
    _ =
        (((sourceExtend.hom).app (op basisW)) ≫
          ((sourceExtend.inv).app (op basisW)) ≫
          basisComp ≫ ((targetExtend.hom).app (op basisW))) ≫
          ((targetExtend.inv).app (op basisW)) := by
            rw [hsource, hright]
            rfl
    _ =
        (((sourceExtend.hom).app (op basisW) ≫
          (sourceExtend.inv).app (op basisW)) ≫ basisComp) ≫
          ((targetExtend.hom).app (op basisW) ≫
            (targetExtend.inv).app (op basisW)) := by
            simp [Category.assoc]
    _ = basisComp := by
      rw [hsourceCancel, htargetCancel]
      rw [Category.id_comp]
      rw [Category.comp_id]

theorem algebraicMemberRestrictExtendIso_component_eq_of_rep
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U)
    (i : ι)
    {W : Opens X}
    (hWi : W ≤ U i) :
    ((algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i).hom).hom.app
        (op (subspaceOpenOfLE hWi)) =
      (algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi).hom := by
  classical
  let hMi := algebraicMemberSubordinateOpens_isBasis (U := U) i
  let basisW : BasisOpen (algebraicMemberSubordinateOpens (U := U) i) :=
    ⟨subspaceOpenOfLE hWi, ⟨W, hWi, rfl⟩⟩
  have hnorm :=
    algebraicMemberRestrictExtendIso_inverseMap_app_eq_basisRestrictComponent
      (F := F) localSheaf overlapIso cocycle hU i hWi
  have hcomp :=
    algebraicMemberSpaceBasisRestrictIso_component_eq_of_rep
      (F := F) localSheaf overlapIso cocycle hU i hWi
  change (((algebraicBasisSiteSheafComparisonEquiv (C := C) hMi).inverse.map
          ((algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i).hom)).hom).app
        (op basisW) =
      (algebraicMemberSpaceBasisComponentIsoOfRep
        F localSheaf overlapIso cocycle hU i hWi).hom
  exact hnorm.trans hcomp

-- Proof sketch: glue the underlying set-valued sheaves by Lemma 6.33.2, then transport the
-- algebraic structure on sections across the equalizer construction.
/-- Lemma 6.33.3 (explicit witness): the extension of the cover-subordinate basis sheaf built from
an algebraic gluing datum realizes that datum, with realization isomorphisms given by
`algebraicMemberRestrictExtendIso`.  This is the reusable form consumed by the module version. -/
theorem algebraicMemberRestrictExtendIso_cocycle
    (F : C ⥤ Type w) [IsAlgebraicStructure C F]
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) (i j : ι) :
    AlgebraicSheafOpenCover.realizationLeftHom localSheaf
        ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend)
        (fun i ↦ algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i) i j ≫
      (overlapIso i j).hom =
    AlgebraicSheafOpenCover.realizationRightHom localSheaf
        ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend)
        (fun i ↦ algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i) i j := by
  classical
  let ℱ := (algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend
  let φ : ∀ i : ι, ((U i).isOpenEmbedding.sheafPullback C).obj ℱ ≅ localSheaf i :=
    fun i ↦ algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i
  show AlgebraicSheafOpenCover.realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
    AlgebraicSheafOpenCover.realizationRightHom localSheaf ℱ φ i j
  apply CategoryTheory.Sheaf.hom_ext
  apply CategoryTheory.NatTrans.ext
  funext V
  obtain ⟨W, hW, hV⟩ :=
    openSubsetOpenRepresentation (U := U i ⊓ U j) V.unop
  have hVop : V = op (subspaceOpenOfLE hW) := by
    apply Opposite.unop_injective
    simpa using hV.symm
  subst hVop
  have hWi : W ≤ U i := hW.trans inf_le_left
  have hWj : W ≤ U j := hW.trans inf_le_right
  have hφi := algebraicMemberRestrictExtendIso_component_eq_of_rep
    (F := F) localSheaf overlapIso cocycle hU i hWi
  have hφj := algebraicMemberRestrictExtendIso_component_eq_of_rep
    (F := F) localSheaf overlapIso cocycle hU j hWj
  let hWij := hW
  let ePair : (((algRestrictToOpen (U i ⊓ U j)).obj ℱ)).1.obj
        (op (subspaceOpenOfLE hWij)) ≅ ℱ.1.obj (op W) :=
    eqToIso (by
      change
        ℱ.1.obj
            (op ((subspaceInclusionFunctor (U i ⊓ U j)).obj
              (subspaceOpenOfLE hWij))) =
          ℱ.1.obj (op W)
      simpa [subspaceOpenOfLEImageEq])
  let eGi := algebraicGlobalMemberSectionIso (U := U) ℱ (i := i) hWi
  let eGj := algebraicGlobalMemberSectionIso (U := U) ℱ (i := j) hWj
  let eLiℱ :=
    openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left
      ((algRestrictToOpen (U i)).obj ℱ)
  let eRjℱ :=
    openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right
      ((algRestrictToOpen (U j)).obj ℱ)
  let eLi := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left (localSheaf i)
  let eRj := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_right (localSheaf j)
  let ambientW : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨i, hWi⟩⟩
  let ambientWRight : BasisOpen (coverSubordinateOpens (U := U)) := ⟨W, ⟨j, hWj⟩⟩
  let coverI :=
    algebraicCoverBasisRestrictExtendComponentIso
      F localSheaf overlapIso cocycle hU ambientW
  let coverJ :=
    algebraicCoverBasisRestrictExtendComponentIso
      F localSheaf overlapIso cocycle hU ambientWRight
  let chartCI := algebraicSubsetChartIso localSheaf overlapIso
    (chosen_chart_le ambientW) hWi
  let chartCJ := algebraicSubsetChartIso localSheaf overlapIso
    (chosen_chart_le ambientW) hWj
  let chartCJRight := algebraicSubsetChartIso localSheaf overlapIso
    (chosen_chart_le ambientWRight) hWj
  let chartIJ := algebraicSubsetChartIso localSheaf overlapIso hWi hWj
  have hleftGlobal :
      (((algebraicGlobalRestrictionToPairViaLeftIso (U i) (U j)).hom.app ℱ).hom.app
          (op (subspaceOpenOfLE hWij))) =
        ePair.hom ≫ eGi.inv ≫ eLiℱ.inv := by
    simp [ePair, eGi, eLiℱ, algebraicGlobalRestrictionToPairViaLeftIso,
      algebraicGlobalRestrictionCompIso, algebraicGlobalMemberSectionIso,
      openSubsetHomOfLEOpenEmbeddingSectionIso,
      Topology.IsOpenEmbedding.sheafPullback, eqToHom_map, Category.assoc]
  have hrightGlobal :
      (((algebraicGlobalRestrictionToPairViaRightIso (U i) (U j)).hom.app ℱ).hom.app
          (op (subspaceOpenOfLE hWij))) =
        ePair.hom ≫ eGj.inv ≫ eRjℱ.inv := by
    simp [ePair, eGj, eRjℱ, algebraicGlobalRestrictionToPairViaRightIso,
      algebraicGlobalRestrictionCompIso, algebraicGlobalMemberSectionIso,
      openSubsetHomOfLEOpenEmbeddingSectionIso,
      Topology.IsOpenEmbedding.sheafPullback, eqToHom_map, Category.assoc]
  have hφiPair :
      ((((algRestrictToPairLeft (U i) (U j)).map (φ i).hom).hom.app
          (op (subspaceOpenOfLE hWij)))) =
        eLiℱ.hom ≫
          (algebraicMemberSpaceBasisComponentIsoOfRep
            F localSheaf overlapIso cocycle hU i hWi).hom ≫
          eLi.inv := by
    have h :=
      (openSubsetHomOfLEOpenEmbeddingSectionIso_map_compare
        (hAB := hWij) (hBD := inf_le_left) (η := (φ i).hom))
    rw [← h, hφi]
  have hφjPair :
      ((((algRestrictToPairRight (U i) (U j)).map (φ j).hom).hom.app
          (op (subspaceOpenOfLE hWij)))) =
        eRjℱ.hom ≫
          (algebraicMemberSpaceBasisComponentIsoOfRep
            F localSheaf overlapIso cocycle hU j hWj).hom ≫
          eRj.inv := by
    have h :=
      (openSubsetHomOfLEOpenEmbeddingSectionIso_map_compare
        (hAB := hWij) (hBD := inf_le_right) (η := (φ j).hom))
    rw [← h, hφj]
  have hchartIJHom :
        chartIJ.hom =
          eLi.inv ≫
            ((overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij))) ≫
            eRj.hom := by
    have hsubset : subset_overlap_le (U := U) hWi hWj = hWij := Subsingleton.elim _ _
    cases hsubset
    simp [chartIJ, eLi, eRj, algebraicSubsetChartIso_hom, TopCat.Sheaf.forget,
      Functor.mapIso_hom, Category.assoc]
  have hchartIJ :
      eLi.inv ≫
          ((overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij))) =
        chartIJ.hom ≫ eRj.inv := by
    rw [hchartIJHom]
    simp [Category.assoc]
  have hchartTrans :
      chartCI.hom ≫ chartIJ.hom = chartCJ.hom := by
    simpa [chartCI, chartIJ, chartCJ, ambientW] using
      algebraicSubsetChartIso_trans localSheaf overlapIso cocycle
        (chosen_chart_le ambientW) hWi hWj
  have hAmbientEq : ambientWRight = ambientW := by
    ext
    rfl
  have hleftNorm :
      ((((algebraicGlobalRestrictionToPairViaLeftIso (U i) (U j)).hom.app ℱ ≫
              (algRestrictToPairLeft (U i) (U j)).map (φ i).hom) ≫
            (overlapIso i j).hom).hom.app
          (op (subspaceOpenOfLE hWij))) =
        ePair.hom ≫ coverI.hom ≫ chartCJ.hom ≫ eRj.inv := by
    simp only [TopCat.Sheaf.comp_app]
    rw [hleftGlobal, hφiPair]
    simp only [Category.assoc]
    calc
      (ePair.hom ≫ eGi.inv ≫ eLiℱ.inv) ≫
            (eLiℱ.hom ≫
              (algebraicMemberSpaceBasisComponentIsoOfRep
                F localSheaf overlapIso cocycle hU i hWi).hom ≫ eLi.inv) ≫
            (overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij))
          =
        ePair.hom ≫ eGi.inv ≫
          (algebraicMemberSpaceBasisComponentIsoOfRep
            F localSheaf overlapIso cocycle hU i hWi).hom ≫
          eLi.inv ≫
          (overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij)) := by
            simp [Category.assoc]
      _ =
        ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫
          eLi.inv ≫
          (overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij)) := by
            simp [algebraicMemberSpaceBasisComponentIsoOfRep, eGi, coverI, chartCI,
              ambientW, Category.assoc]
      _ =
        ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫ chartIJ.hom ≫ eRj.inv := by
            calc
              ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫ eLi.inv ≫
                  (overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij)) =
                ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫
                  (eLi.inv ≫
                    (overlapIso i j).hom.hom.app (op (subspaceOpenOfLE hWij))) := by
                    simp [Category.assoc]
              _ = ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫
                    (chartIJ.hom ≫ eRj.inv) := by
                    rw [hchartIJ]
              _ = ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫ chartIJ.hom ≫ eRj.inv := by
                    simp [Category.assoc]
      _ = ePair.hom ≫ coverI.hom ≫ chartCJ.hom ≫ eRj.inv := by
            calc
              ePair.hom ≫ coverI.hom ≫ chartCI.hom ≫ chartIJ.hom ≫ eRj.inv =
                  (ePair.hom ≫ coverI.hom) ≫ (chartCI.hom ≫ chartIJ.hom) ≫
                    eRj.inv := by
                    simp [Category.assoc]
              _ = (ePair.hom ≫ coverI.hom) ≫ chartCJ.hom ≫ eRj.inv := by
                    exact congrArg
                      (fun t ↦ (ePair.hom ≫ coverI.hom) ≫ t ≫ eRj.inv)
                      hchartTrans
              _ = ePair.hom ≫ coverI.hom ≫ chartCJ.hom ≫ eRj.inv := by
                    simp [Category.assoc]
  have hrightNorm :
      (((algebraicGlobalRestrictionToPairViaRightIso (U i) (U j)).hom.app ℱ ≫
            (algRestrictToPairRight (U i) (U j)).map (φ j).hom).hom.app
          (op (subspaceOpenOfLE hWij))) =
        ePair.hom ≫ coverI.hom ≫ chartCJ.hom ≫ eRj.inv := by
    simp only [TopCat.Sheaf.comp_app]
    rw [hrightGlobal, hφjPair]
    have hrightRaw :
        (ePair.hom ≫ eGj.inv ≫ eRjℱ.inv) ≫
            (eRjℱ.hom ≫
              (algebraicMemberSpaceBasisComponentIsoOfRep
                F localSheaf overlapIso cocycle hU j hWj).hom ≫ eRj.inv) =
          ePair.hom ≫ coverJ.hom ≫ chartCJRight.hom ≫ eRj.inv := by
      simp [algebraicMemberSpaceBasisComponentIsoOfRep, eGj, coverJ, chartCJRight,
        ambientWRight, Category.assoc]
    have hcoverChart :
        coverJ.hom ≫ chartCJRight.hom = coverI.hom ≫ chartCJ.hom := by
      cases hAmbientEq
      rfl
    calc
      (ePair.hom ≫ eGj.inv ≫ eRjℱ.inv) ≫
            (eRjℱ.hom ≫
              (algebraicMemberSpaceBasisComponentIsoOfRep
                F localSheaf overlapIso cocycle hU j hWj).hom ≫ eRj.inv)
          = ePair.hom ≫ coverJ.hom ≫ chartCJRight.hom ≫ eRj.inv := hrightRaw
      _ = ePair.hom ≫ coverI.hom ≫ chartCJ.hom ≫ eRj.inv := by
        calc
          ePair.hom ≫ coverJ.hom ≫ chartCJRight.hom ≫ eRj.inv =
              ePair.hom ≫ (coverJ.hom ≫ chartCJRight.hom) ≫ eRj.inv := by
                simp [Category.assoc]
          _ = ePair.hom ≫ (coverI.hom ≫ chartCJ.hom) ≫ eRj.inv := by
                rw [hcoverChart]
          _ = ePair.hom ≫ coverI.hom ≫ chartCJ.hom ≫ eRj.inv := by
                simp [Category.assoc]
  dsimp [AlgebraicSheafOpenCover.realizationLeftHom,
    AlgebraicSheafOpenCover.realizationRightHom]
  exact hleftNorm.trans hrightNorm.symm

theorem algebraicOpenCoverBasisSheafExtend_realizes
    (F : C ⥤ Type w) [IsAlgebraicStructure C F]
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    AlgebraicSheafOpenCover.Realizes U localSheaf overlapIso
      ((algebraicOpenCoverBasisSheaf (F := F) localSheaf overlapIso cocycle hU).extend) :=
  ⟨fun i ↦ algebraicMemberRestrictExtendIso (F := F) localSheaf overlapIso cocycle hU i,
    fun i j ↦ algebraicMemberRestrictExtendIso_cocycle F localSheaf overlapIso cocycle hU i j⟩

/-- Lemma 6.33.3: an algebraic gluing datum on an open cover is realized by a `C`-valued sheaf on
the ambient space. -/
theorem exists_algebraic_sheaf_of_open_cover_glueing
    (F : C ⥤ Type w) [IsAlgebraicStructure C F]
    (localSheaf : ∀ i : ι, TopCat.Sheaf C (openSubsetSpace (U i)))
    (overlapIso : ∀ i j : ι,
      (algRestrictToPairLeft (U i) (U j)).obj (localSheaf i) ≅
        (algRestrictToPairRight (U i) (U j)).obj (localSheaf j))
    (cocycle : AlgebraicSheafOpenCover.CocycleCondition U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    ∃ ℱ : TopCat.Sheaf C X, AlgebraicSheafOpenCover.Realizes U localSheaf overlapIso ℱ :=
  ⟨_, algebraicOpenCoverBasisSheafExtend_realizes F localSheaf overlapIso cocycle hU⟩

end
