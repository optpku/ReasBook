module

public import stacks_project.Chap06.Lemma_6_30_13
public import stacks_project.Chap06.Lemma_6_33_3_Part8

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

noncomputable def moduleSheafRestrictionOpenPushIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    moduleSheafRestrictionOpenPush 𝒪 h ≅ moduleSheafRestriction 𝒪 h :=
  Adjunction.leftAdjointUniq
    (moduleSheafRestrictionOpenPushAdjunction 𝒪 h)
    (SheafOfModules.pullbackPushforwardAdjunction (restrictedRingSheafToPushforward 𝒪 h))

@[reducible] def addCommGrpSheafHasSheafifyForOpen (V₀ : Opens X) :
    HasSheafify (Opens.grothendieckTopology (openSubsetSpace V₀)) AddCommGrpCat.{w} := by
  let K := Opens.grothendieckTopology (openSubsetSpace V₀)
  letI : ∀ V : Opens (openSubsetSpace V₀), IsCofiltered (K.Cover V) :=
    fun V => CategoryTheory.isCofiltered_of_directed_ge_nonempty (K.Cover V)
  letI : ∀ V : Opens (openSubsetSpace V₀), IsFiltered (K.Cover V)ᵒᵖ :=
    fun V => CategoryTheory.isFiltered_op_of_isCofiltered (K.Cover V)
  letI :
      ∀ V : Opens (openSubsetSpace V₀),
        PreservesColimitsOfShape (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{w}) :=
    fun V =>
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits
        ((K.Cover V)ᵒᵖ) (F := forget AddCommGrpCat.{w})
  exact
    CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
      K AddCommGrpCat.{w}

@[reducible] def addCommGrpSheafHasZeroObjectForOpen (V₀ : Opens X) :
    HasZeroObject
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (openSubsetSpace V₀)) AddCommGrpCat.{w}) := by
  letI :
      HasSheafify (Opens.grothendieckTopology (openSubsetSpace V₀))
        AddCommGrpCat.{w} :=
    addCommGrpSheafHasSheafifyForOpen V₀
  letI :
      Abelian
        (CategoryTheory.Sheaf
          (Opens.grothendieckTopology (openSubsetSpace V₀)) AddCommGrpCat.{w}) :=
    inferInstance
  exact CategoryTheory.Abelian.hasZeroObject

noncomputable def moduleToAddCommGrpRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ W)).obj
        ((moduleSheafRestriction 𝒪 h).obj ℱ) := by
  let hf := openSubsetHomOfLE_isOpenEmbedding h
  letI := hf.functor_isContinuous
  have hOpen :
      (hf.sheafPullback AddCommGrpCat.{w}).obj
          ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) =
        (SheafOfModules.toSheaf (𝒪 |_ W)).obj
          ((moduleSheafRestrictionOpenPush 𝒪 h).obj ℱ) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  exact
    eqToIso hOpen ≪≫
      (SheafOfModules.toSheaf (𝒪 |_ W)).mapIso
        ((moduleSheafRestrictionOpenPushIso 𝒪 h).app ℱ)

noncomputable def moduleToAddCommGrpPairLeftRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairLeft 𝒪 U V).obj ℱ) :=
  moduleToAddCommGrpRestrictionIso 𝒪 (show U ⊓ V ≤ U from inf_le_left) ℱ

noncomputable def moduleToAddCommGrpPairRightRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    ((openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback
      AddCommGrpCat.{w}).obj
        ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).obj
        ((moduleSheafRestrictionToPairRight 𝒪 U V).obj ℱ) :=
  moduleToAddCommGrpRestrictionIso 𝒪 (show U ⊓ V ≤ V from inf_le_right) ℱ

noncomputable def moduleToAddCommGrpTripleFirstRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    (algebraicRestrictToTripleFirst (C := AddCommGrpCat.{w}) U V W).obj
        ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V ⊓ W))).obj
        ((moduleRestrictToTripleFirst 𝒪 U V W).obj ℱ) :=
  moduleToAddCommGrpRestrictionIso 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans
      (show U ⊓ V ≤ U from inf_le_left)) ℱ

noncomputable def moduleToAddCommGrpTripleSecondRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    (algebraicRestrictToTripleSecond (C := AddCommGrpCat.{w}) U V W).obj
        ((SheafOfModules.toSheaf (𝒪 |_ V)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V ⊓ W))).obj
        ((moduleRestrictToTripleSecond 𝒪 U V W).obj ℱ) :=
  moduleToAddCommGrpRestrictionIso 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans
      (show U ⊓ V ≤ V from inf_le_right)) ℱ

noncomputable def moduleToAddCommGrpTripleThirdRestrictionIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ W)) :
    (algebraicRestrictToTripleThird (C := AddCommGrpCat.{w}) U V W).obj
        ((SheafOfModules.toSheaf (𝒪 |_ W)).obj ℱ) ≅
      (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V ⊓ W))).obj
        ((moduleRestrictToTripleThird 𝒪 U V W).obj ℱ) :=
  moduleToAddCommGrpRestrictionIso 𝒪 (show U ⊓ V ⊓ W ≤ W from inf_le_right) ℱ

@[reducible] def addCommGrpSheafHasSheafify (V₀ : Opens X) :
    HasSheafify (Opens.grothendieckTopology (openSubsetSpace V₀)) AddCommGrpCat.{w} := by
  let K := Opens.grothendieckTopology (openSubsetSpace V₀)
  letI : ∀ V : Opens (openSubsetSpace V₀), IsCofiltered (K.Cover V) :=
    fun V => CategoryTheory.isCofiltered_of_directed_ge_nonempty (K.Cover V)
  letI : ∀ V : Opens (openSubsetSpace V₀), IsFiltered (K.Cover V)ᵒᵖ :=
    fun V => CategoryTheory.isFiltered_op_of_isCofiltered (K.Cover V)
  letI :
      ∀ V : Opens (openSubsetSpace V₀),
        PreservesColimitsOfShape (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{w}) :=
    fun V =>
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits
        ((K.Cover V)ᵒᵖ) (F := forget AddCommGrpCat.{w})
  exact
    CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
      K AddCommGrpCat.{w}

@[reducible] def addCommGrpSheafHasZeroObject (V₀ : Opens X) :
    HasZeroObject
      (CategoryTheory.Sheaf
        (Opens.grothendieckTopology (openSubsetSpace V₀)) AddCommGrpCat.{w}) := by
  letI :
      HasSheafify (Opens.grothendieckTopology (openSubsetSpace V₀))
        AddCommGrpCat.{w} :=
    addCommGrpSheafHasSheafify V₀
  letI :
      Abelian
        (CategoryTheory.Sheaf
          (Opens.grothendieckTopology (openSubsetSpace V₀)) AddCommGrpCat.{w}) :=
    inferInstance
  exact CategoryTheory.Abelian.hasZeroObject

variable (𝒪 : TopCat.Sheaf RingCat X)

/-- Helper for Lemma 6.33.3: the restriction of the ambient ring sheaf to the
cover-subordinate basis. -/
noncomputable abbrev moduleCoverBasisRingSheaf
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (hU : IsOpenCover U) :
    BasisSiteSheaf RingCat.{w} (coverSubordinateOpens (U := U))
      (cover_subordinate_opens_isBasis hU) :=
  ((basisOpenInclusion (coverSubordinateOpens (U := U))).sheafPushforwardContinuous RingCat.{w}
    (basisGrothendieckTopology (coverSubordinateOpens (U := U))
      (cover_subordinate_opens_isBasis hU))
    (Opens.grothendieckTopology X)).obj 𝒪

/-- Helper for Lemma 6.33.3: the canonical functor restricting `𝒪`-modules to the
cover-subordinate basis. -/
noncomputable abbrev moduleCoverBasisRestrictionFunctor
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (hU : IsOpenCover U) :
    SheafOfModules.{w} 𝒪 ⥤ SheafOfModules.{w} (moduleCoverBasisRingSheaf (U := U) 𝒪 hU) :=
  SheafOfModules.pushforward (𝟙 (moduleCoverBasisRingSheaf (U := U) 𝒪 hU))

/-- Helper for Lemma 6.33.3: restriction of module sheaves from `X` to the
cover-subordinate basis is an equivalence. -/
theorem moduleCoverBasisRestrictionFunctor_isEquivalence
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (hU : IsOpenCover U) :
    Functor.IsEquivalence (moduleCoverBasisRestrictionFunctor (U := U) 𝒪 hU) := by
  -- This is Lemma 6.30.13 specialized to the basis of opens contained in a member of the cover.
  simpa [moduleCoverBasisRestrictionFunctor, moduleCoverBasisRingSheaf] using
    (restrictSheafOfModulesToBasis_isEquivalence
      (B := coverSubordinateOpens (U := U))
      (hB := cover_subordinate_opens_isBasis hU) 𝒪)

abbrev moduleTripleOverlapHom12
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (moduleRestrictToTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) :=
  ((moduleRestrictToTripleFirstViaIJIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((moduleRestrictOverlapToTripleLeft 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i j)).hom ≫
    ((moduleRestrictToTripleSecondViaIJIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf j))

abbrev moduleTripleOverlapHom23
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleSecond 𝒪 (U i) (U j) (U k)).obj (localSheaf j) ⟶
      (moduleRestrictToTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((moduleRestrictToTripleSecondViaJKIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf j)) ≫
    ((moduleRestrictOverlapToTripleCenter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso j k)).hom ≫
    ((moduleRestrictToTripleThirdViaJKIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

abbrev moduleTripleOverlapHom13
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (i j k : ι) :
    (moduleRestrictToTripleFirst 𝒪 (U i) (U j) (U k)).obj (localSheaf i) ⟶
      (moduleRestrictToTripleThird 𝒪 (U i) (U j) (U k)).obj (localSheaf k) :=
  ((moduleRestrictToTripleFirstViaIKIso 𝒪 (U i) (U j) (U k)).hom.app (localSheaf i)) ≫
    ((moduleRestrictOverlapToTripleOuter 𝒪 (U i) (U j) (U k)).mapIso
      (overlapIso i k)).hom ≫
    ((moduleRestrictToTripleThirdViaIKIso 𝒪 (U i) (U j) (U k)).inv.app (localSheaf k))

/-- The cocycle condition for pairwise overlap isomorphisms in a gluing datum of sheaves of
`𝒪`-modules on an open cover. -/
abbrev moduleToTypes (𝒪 : TopCat.Sheaf RingCat X) (U : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤ TopCat.Sheaf (Type w) (openSubsetSpace U) :=
  letI : PreservesLimits (forget AddCommGrpCat.{w}) := inferInstance
  letI :
      (Opens.grothendieckTopology (openSubsetSpace U)).HasSheafCompose
        (forget AddCommGrpCat.{w}) :=
    CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize
      (Opens.grothendieckTopology (openSubsetSpace U))
  SheafOfModules.toSheaf (𝒪 |_ U) ⋙
    sheafCompose (Opens.grothendieckTopology (openSubsetSpace U)) (forget AddCommGrpCat.{w})

noncomputable def modulePairLeftToTypesIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ U)) :
    ((moduleSheafRestrictionToPairLeft 𝒪 U V ⋙ moduleToTypes 𝒪 (U ⊓ V)).obj ℱ) ≅
      ((moduleToTypes 𝒪 U ⋙
        (openSubsetIntersectionLeftInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  let e :=
    (sheafCompose (Opens.grothendieckTopology (openSubsetSpace (U ⊓ V)))
      (forget AddCommGrpCat.{w})).mapIso
      (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 U V ℱ).symm
  eqToIso rfl ≪≫ e ≪≫ eqToIso rfl

noncomputable def modulePairRightToTypesIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X)
    (ℱ : SheafOfModules (𝒪 |_ V)) :
    ((moduleSheafRestrictionToPairRight 𝒪 U V ⋙ moduleToTypes 𝒪 (U ⊓ V)).obj ℱ) ≅
      ((moduleToTypes 𝒪 V ⋙
        (openSubsetIntersectionRightInclusion_isOpenEmbedding U V).sheafPullback (Type w)).obj
        ℱ) :=
  let e :=
    (sheafCompose (Opens.grothendieckTopology (openSubsetSpace (U ⊓ V)))
      (forget AddCommGrpCat.{w})).mapIso
      (moduleToAddCommGrpPairRightRestrictionIso 𝒪 U V ℱ).symm
  eqToIso rfl ≪≫ e ≪≫ eqToIso rfl

namespace ModuleSheafOpenCover

def CocycleCondition (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j)) :
    Prop :=
  AlgebraicSheafOpenCover.CocycleCondition (C := AddCommGrpCat.{w}) U
    (fun i ↦ (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))
    (fun i j ↦
      moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i) ≪≫
        ((SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).mapIso (overlapIso i j)) ≪≫
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).symm)

variable {𝒪 : TopCat.Sheaf RingCat X} {U : ι → Opens X}

noncomputable def toSheafOpenCoverGlueing
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : CocycleCondition 𝒪 U localSheaf overlapIso)
    (hU : IsOpenCover U) :
    SheafOpenCoverGlueing U := by
  let addLocal :
      ∀ i : ι, TopCat.Sheaf AddCommGrpCat.{w} (openSubsetSpace (U i)) :=
    fun i ↦ (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i)
  let addOverlap : ∀ i j : ι,
      (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).obj
          (addLocal i) ≅
        (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).obj
          (addLocal j) :=
    fun i j ↦
      moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i) ≪≫
        ((SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).mapIso (overlapIso i j)) ≪≫
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).symm
  have addCocycle :
      AlgebraicSheafOpenCover.CocycleCondition (C := AddCommGrpCat.{w})
        U addLocal addOverlap := by
    simpa [CocycleCondition, addLocal, addOverlap] using cocycle
  exact
    AlgebraicSheafOpenCover.toSheafOpenCoverGlueing
      (C := AddCommGrpCat.{w}) (F := forget AddCommGrpCat.{w})
      addLocal addOverlap addCocycle hU

abbrev realizationLeftHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) :=
  ((moduleRestrictionToPairViaLeftIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).mapIso (φ i)).hom

abbrev realizationRightHom
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (ℱ : SheafOfModules 𝒪)
    (φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i)
    (i j : ι) :
    (moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱ ⟶
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j) :=
  ((moduleRestrictionToPairViaRightIso 𝒪 (U i) (U j)).hom.app ℱ) ≫
    ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).mapIso (φ j)).hom

/-- A sheaf of `𝒪`-modules realizes a module gluing datum if its restrictions recover the given
local module sheaves and the induced overlap comparisons agree with the prescribed overlap
isomorphisms in the categories of sheaves of `𝒪`-modules. -/
def Realizes
    (U : ι → Opens X)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (ℱ : SheafOfModules 𝒪) : Prop :=
  ∃ φ : ∀ i : ι, (moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱ ≅ localSheaf i,
    ∀ i j : ι,
      realizationLeftHom localSheaf ℱ φ i j ≫ (overlapIso i j).hom =
        realizationRightHom localSheaf ℱ φ i j

end ModuleSheafOpenCover

/-- Helper for Lemma 6.33.3: the underlying additive sheaves of the local module sheaves. -/
noncomputable abbrev moduleOpenCoverAddLocal
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i)) :
    ∀ i : ι, TopCat.Sheaf AddCommGrpCat.{w} (openSubsetSpace (U i)) :=
  fun i ↦ (SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i)

/-- Helper for Lemma 6.33.3: the additive overlap isomorphisms induced by the module overlap
isomorphisms. -/
noncomputable abbrev moduleOpenCoverAddOverlap
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j)) :
    ∀ i j : ι,
      (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).obj
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf i) ≅
        (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).obj
          (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf j) :=
  fun i j ↦
    moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i) ≪≫
      ((SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).mapIso (overlapIso i j)) ≪≫
      (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).symm

/-- Helper for Lemma 6.33.3: the module cocycle condition viewed as the additive cocycle
condition used by the algebraic gluing construction. -/
noncomputable abbrev moduleOpenCoverAddCocycle
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso) :
    AlgebraicSheafOpenCover.CocycleCondition (C := AddCommGrpCat.{w}) U
      (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
      (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso) := by
  simpa [ModuleSheafOpenCover.CocycleCondition, moduleOpenCoverAddLocal,
    moduleOpenCoverAddOverlap] using cocycle

/-- Helper for Lemma 6.33.3: the ambient ring sheaf restricted to the cover-subordinate basis. -/
noncomputable abbrev moduleOpenCoverBasisRingSheaf
    (hU : IsOpenCover U) :
    BasisSiteSheaf RingCat.{w}
      (coverSubordinateOpens (U := U)) (cover_subordinate_opens_isBasis hU) :=
  ((basisOpenInclusion (coverSubordinateOpens (U := U))).sheafPushforwardContinuous
    RingCat.{w}
    (basisGrothendieckTopology
      (coverSubordinateOpens (U := U)) (cover_subordinate_opens_isBasis hU))
    (Opens.grothendieckTopology X)).obj 𝒪

/-- Helper for Lemma 6.33.3: the additive basis presheaf obtained from the local module sheaves. -/
noncomputable abbrev moduleOpenCoverBasisAddPresheaf
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso) :
    (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ ⥤ AddCommGrpCat.{w} :=
  algebraicOpenCoverBasisPresheaf
    (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
    (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
    (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle)

/-- Helper for Lemma 6.33.3: local and ambient ring sections agree on a subordinate open. -/
noncomputable def moduleOpenCoverRingSectionIsoOfLE
    (𝒪 : TopCat.Sheaf RingCat X) {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    ((𝒪 |_ U i).obj.obj (op (subspaceOpenOfLE hWi))) ≅
      𝒪.obj.obj (op W) := by
  let e :=
    (((TopCat.Sheaf.forget RingCat (openSubsetSpace (U i))).mapIso
      ((openEmbeddingSheafPullbackIsoRing
        (Opens.isOpenEmbedding (U i))).app 𝒪)).app
      (op (subspaceOpenOfLE hWi)))
  exact e ≪≫
    eqToIso (by
      change
        𝒪.obj.obj
            (op (((U i).isOpenEmbedding).functor.obj
              (subspaceOpenOfLE hWi))) =
          𝒪.obj.obj (op W)
      simpa [subspaceOpenOfLEImageEq])

/-- Helper for Lemma 6.33.3: the local-to-ambient ring section comparison commutes with
restriction of subordinate opens. -/
theorem moduleOpenCoverRingSectionIsoOfLE_naturality
    (𝒪 : TopCat.Sheaf RingCat X)
    {W V : Opens X} {i : ι} (hWi : W ≤ U i) (hVi : V ≤ U i)
    (hWV : W ≤ V) :
    (𝒪 |_ U i).obj.map (subspaceOpenHom hWi hVi hWV).op ≫
        (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWi).hom =
      (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hVi).hom ≫
        𝒪.obj.map (homOfLE hWV).op := by
  let α :=
    (TopCat.Sheaf.forget RingCat (openSubsetSpace (U i))).map
      ((openEmbeddingSheafPullbackIsoRing
        (Opens.isOpenEmbedding (U i))).hom.app 𝒪)
  have hfunctor :
      (((Opens.isOpenEmbedding (U i)).sheafPullback RingCat).obj 𝒪).obj.map
            (subspaceOpenHom hWi hVi hWV).op ≫
          eqToHom
            (by
              change
                𝒪.obj.obj
                    (op (((U i).isOpenEmbedding).functor.obj
                      (subspaceOpenOfLE hWi))) =
                  𝒪.obj.obj (op W)
              simpa [subspaceOpenOfLEImageEq]) =
        eqToHom
            (by
              change
                𝒪.obj.obj
                    (op (((U i).isOpenEmbedding).functor.obj
                      (subspaceOpenOfLE hVi))) =
                  𝒪.obj.obj (op V)
              simpa [subspaceOpenOfLEImageEq]) ≫
          𝒪.obj.map (homOfLE hWV).op := by
    let pW :
        𝒪.obj.obj
            (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hWi))) =
          𝒪.obj.obj (op W) := by
      simpa using congrArg (fun V ↦ 𝒪.obj.obj (op V)) (subspaceOpenOfLEImageEq hWi)
    let pV :
        𝒪.obj.obj
            (op ((subspaceInclusionFunctor (U i)).obj (subspaceOpenOfLE hVi))) =
          𝒪.obj.obj (op V) := by
      simpa using congrArg (fun V ↦ 𝒪.obj.obj (op V)) (subspaceOpenOfLEImageEq hVi)
    have hw :
        𝒪.obj.map (eqToHom (subspaceOpenOfLEImageEq hWi).symm).op = eqToHom pW := by
      have hw' :
          𝒪.obj.map (eqToHom (subspaceOpenOfLEImageEq hWi).symm).op =
            eqToHom (congrArg (fun V ↦ 𝒪.obj.obj (op V)) (subspaceOpenOfLEImageEq hWi)) := by
        simpa using
          (CategoryTheory.eqToHom_map 𝒪.obj
            (congrArg Opposite.op (subspaceOpenOfLEImageEq hWi)))
      simpa [pW] using hw'
    have hv :
        𝒪.obj.map (eqToHom (subspaceOpenOfLEImageEq hVi).symm).op = eqToHom pV := by
      have hv' :
          𝒪.obj.map (eqToHom (subspaceOpenOfLEImageEq hVi).symm).op =
            eqToHom (congrArg (fun V ↦ 𝒪.obj.obj (op V)) (subspaceOpenOfLEImageEq hVi)) := by
        simpa using
          (CategoryTheory.eqToHom_map 𝒪.obj
            (congrArg Opposite.op (subspaceOpenOfLEImageEq hVi)))
      simpa [pV] using hv'
    have hmap' := congrArg (fun k ↦ 𝒪.obj.map k.op)
      (subspaceInclusionFunctorMapEqHomOfLE (U := U) i hWi hVi hWV)
    have hmap :
        𝒪.obj.map (((subspaceInclusionFunctor (U i)).map
            (subspaceOpenHom hWi hVi hWV)).op) ≫
          eqToHom pW =
        eqToHom pV ≫ 𝒪.obj.map (homOfLE hWV).op := by
      rw [← hw, ← hv, ← Functor.map_comp, ← Functor.map_comp]
      exact hmap'
    simpa [Topology.IsOpenEmbedding.sheafPullback, pW, pV] using hmap
  simpa [moduleOpenCoverRingSectionIsoOfLE, α, Category.assoc] using
    congrArg (fun t ↦ α.app (op (subspaceOpenOfLE hVi)) ≫ t) hfunctor

/-- Helper for Lemma 6.33.3: the section group on a basis open inherits a module structure from
the chosen local module sheaf. -/
@[reducible] noncomputable def moduleOpenCoverBasisObjModule
    (hU : IsOpenCover U)
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    (overlapIso : ∀ i j : ι,
      (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
        (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
    (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
    (W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ) :
    Module ((moduleOpenCoverBasisRingSheaf (𝒪 := 𝒪) hU).obj.obj W)
      ((moduleOpenCoverBasisAddPresheaf (𝒪 := 𝒪) localSheaf overlapIso cocycle).obj W) := by
  change Module (𝒪.obj.obj (op W.unop.obj))
    ((localSheaf (chosen_chart W.unop)).val.obj
      (op (subspaceOpenOfLE (chosen_chart_le W.unop))))
  exact Module.compHom _ (moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪)
    (chosen_chart_le W.unop)).inv.hom

/-- Helper for Lemma 6.33.3: local restriction maps are semilinear after transporting local ring
sections to ambient ring sections. -/
theorem moduleOpenCoverLocalRestriction_smul
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    {W V : Opens X} {i : ι} (hWi : W ≤ U i) (hVi : V ≤ U i)
    (hWV : W ≤ V)
    (r : 𝒪.obj.obj (op V))
    (m : (localSheaf i).val.obj (op (subspaceOpenOfLE hVi))) :
    ((localSheaf i).val.map (subspaceOpenHom hWi hVi hWV).op)
        (((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hVi).inv.hom r) • m) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWi).inv.hom
          (𝒪.obj.map (homOfLE hWV).op r)) •
        ((localSheaf i).val.map (subspaceOpenHom hWi hVi hWV).op) m := by
  let eV := moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hVi
  let eW := moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWi
  rw [(localSheaf i).val.map_smul]
  congr 1
  have hnat := moduleOpenCoverRingSectionIsoOfLE_naturality
    (𝒪 := 𝒪) hWi hVi hWV
  have happ :=
    congrArg (fun f : ((𝒪 |_ U i).obj.obj (op (subspaceOpenOfLE hVi)) ⟶
        𝒪.obj.obj (op W)) ↦ f (eV.inv.hom r)) hnat
  change
    eW.hom.hom (((𝒪 |_ U i).obj.map
      (subspaceOpenHom hWi hVi hWV).op) (eV.inv.hom r)) =
      (𝒪.obj.map (homOfLE hWV).op) (eV.hom.hom (eV.inv.hom r)) at happ
  have heV : eV.hom.hom (eV.inv.hom r) = r := by
    simpa using CategoryTheory.congr_fun eV.inv_hom_id r
  rw [heV] at happ
  calc
    ((𝒪 |_ U i).obj.map (subspaceOpenHom hWi hVi hWV).op) (eV.inv.hom r)
        =
      eW.inv.hom (eW.hom.hom (((𝒪 |_ U i).obj.map
        (subspaceOpenHom hWi hVi hWV).op) (eV.inv.hom r))) := by
        simp
    _ = eW.inv.hom ((𝒪.obj.map (homOfLE hWV).op) r) := by
      rw [happ]

theorem moduleToAddCommGrpRestrictionIso_hom_smul
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U)
    (ℱ : SheafOfModules (𝒪 |_ U))
    (V : (Opens (openSubsetSpace W))ᵒᵖ)
    (r : (𝒪 |_ W).obj.obj V)
    (m : ((moduleSheafRestrictionOpenPush 𝒪 h).obj ℱ).val.obj V) :
    (show ((moduleSheafRestriction 𝒪 h).obj ℱ).val.obj V from
      ((moduleToAddCommGrpRestrictionIso 𝒪 h ℱ).hom.hom.app V).hom (r • m)) =
      r • (show ((moduleSheafRestriction 𝒪 h).obj ℱ).val.obj V from
        ((moduleToAddCommGrpRestrictionIso 𝒪 h ℱ).hom.hom.app V).hom m) := by
  change (((moduleSheafRestrictionOpenPushIso 𝒪 h).hom.app ℱ).val.app V) (r • m) =
    r • (((moduleSheafRestrictionOpenPushIso 𝒪 h).hom.app ℱ).val.app V) m
  simp

theorem moduleToAddCommGrpRestrictionIso_inv_smul
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U)
    (ℱ : SheafOfModules (𝒪 |_ U))
    (V : (Opens (openSubsetSpace W))ᵒᵖ)
    (r : (𝒪 |_ W).obj.obj V)
    (m : ((moduleSheafRestriction 𝒪 h).obj ℱ).val.obj V) :
    (show ((moduleSheafRestrictionOpenPush 𝒪 h).obj ℱ).val.obj V from
      ((moduleToAddCommGrpRestrictionIso 𝒪 h ℱ).inv.hom.app V).hom (r • m)) =
      r • (show ((moduleSheafRestrictionOpenPush 𝒪 h).obj ℱ).val.obj V from
        ((moduleToAddCommGrpRestrictionIso 𝒪 h ℱ).inv.hom.app V).hom m) := by
  change (((moduleSheafRestrictionOpenPushIso 𝒪 h).inv.app ℱ).val.app V) (r • m) =
    r • (((moduleSheafRestrictionOpenPushIso 𝒪 h).inv.app ℱ).val.app V) m
  simp

/-- Helper for Lemma 6.33.3: the first step in the basis restriction map is semilinear after
transporting scalar sections from the ambient ring sheaf to the chosen local chart. -/
theorem moduleOpenCoverBasisLocalMap_smul
    (localSheaf : ∀ i : ι, SheafOfModules (𝒪 |_ U i))
    {V W : (BasisOpen (coverSubordinateOpens (U := U)))ᵒᵖ} (f : V ⟶ W)
    (r : 𝒪.obj.obj (op V.unop.obj))
    (m : (localSheaf (chosen_chart V.unop)).val.obj
      (op (subspaceOpenOfLE (chosen_chart_le V.unop)))) :
    let hWV : W.unop.obj ≤ V.unop.obj := f.unop.hom.le
    let hWcV : W.unop.obj ≤ U (chosen_chart V.unop) :=
      hWV.trans (chosen_chart_le V.unop)
    ((localSheaf (chosen_chart V.unop)).val.map
        (subspaceOpenHom hWcV (chosen_chart_le V.unop) hWV).op)
      (((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪)
        (chosen_chart_le V.unop)).inv.hom r) • m) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWcV).inv.hom
        (𝒪.obj.map (homOfLE hWV).op r)) •
        ((localSheaf (chosen_chart V.unop)).val.map
          (subspaceOpenHom hWcV (chosen_chart_le V.unop) hWV).op) m := by
  -- This is exactly the local module-presheaf semilinearity for the inclusion `W ⊆ V`,
  -- with scalar sections transported through the ambient/local ring comparison.
  exact moduleOpenCoverLocalRestriction_smul (𝒪 := 𝒪) localSheaf
    (f.unop.hom.le.trans (chosen_chart_le V.unop)) (chosen_chart_le V.unop)
    f.unop.hom.le r m

/-- Helper for Lemma 6.33.3: the ring comparison for the open-push restriction owner on
sections of a represented open. -/
noncomputable def moduleSheafRestrictionOpenPushRingSectionIso
    (𝒪 : TopCat.Sheaf RingCat X) {T W U₀ : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U₀) :
    ((𝒪 |_ W).obj.obj (op (subspaceOpenOfLE hTW))) ≅
      ((𝒪 |_ U₀).obj.obj (op (subspaceOpenOfLE (hTW.trans hWU)))) :=
  (((TopCat.Sheaf.forget RingCat (openSubsetSpace W)).mapIso
      (moduleSheafRestrictionOpenPushRingIso 𝒪 hWU)).app
      (op (subspaceOpenOfLE hTW))) ≪≫
    openSubsetHomOfLEOpenEmbeddingSectionIso hTW hWU (𝒪 |_ U₀)

/-- Helper for Lemma 6.33.3: the hom of the open-push ring section comparison is the
open-push ring isomorphism followed by the represented-open section comparison. -/
theorem moduleSheafRestrictionOpenPushRingSectionIso_hom
    (𝒪 : TopCat.Sheaf RingCat X) {T W U₀ : Opens X}
    (hTW : T ≤ W) (hWU : W ≤ U₀) :
    (moduleSheafRestrictionOpenPushRingSectionIso 𝒪 hTW hWU).hom =
      ((moduleSheafRestrictionOpenPushRingIso 𝒪 hWU).hom.hom.app
        (op (subspaceOpenOfLE hTW))) ≫
        (openSubsetHomOfLEOpenEmbeddingSectionIso hTW hWU (𝒪 |_ U₀)).hom := by
  -- This is just the first projection of the composite section comparison.
  rfl

/-- Helper for Lemma 6.33.3: for nested cover members, the open-push ring comparison can be
followed by the ambient section comparison for the larger open. -/
noncomputable def moduleSheafRestrictionOpenPushRingSectionToAmbientIso
    (𝒪 : TopCat.Sheaf RingCat X) {T : Opens X} {i j : ι}
    (hTj : T ≤ U j) (hji : U j ≤ U i) :
    ((𝒪 |_ U j).obj.obj (op (subspaceOpenOfLE hTj))) ≅ 𝒪.obj.obj (op T) :=
  moduleSheafRestrictionOpenPushRingSectionIso 𝒪 hTj hji ≪≫
    moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) (i := i) (hTj.trans hji)

/-- Helper for Lemma 6.33.3: the ring isomorphism used by open-push module restriction converts
the Part8 restriction unit into the naive open-embedding unit. -/
theorem moduleSheafRestrictionOpenPushRingIso_unit
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U) :
    let hf := openSubsetHomOfLE_isOpenEmbedding h
    letI := hf.functor_isContinuous
    let adjNaive :
        hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h) :=
      hf.isOpenMap.adjunction.sheafPushforwardContinuous
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace U))
    restrictedRingSheafToPushforward 𝒪 h ≫
        (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
          (moduleSheafRestrictionOpenPushRingIso 𝒪 h).hom =
      adjNaive.unit.app (𝒪 |_ U) := by
  let hf := openSubsetHomOfLE_isOpenEmbedding h
  haveI := hf.functor_isContinuous
  let adjNaive :
        hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h) :=
      hf.isOpenMap.adjunction.sheafPushforwardContinuous
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace U))
  let e := restrictedRingSheafPullbackIso 𝒪 h
  let u := openEmbeddingSheafPullbackIsoRing hf
  let adjActual := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)
  have hUnit := Adjunction.unit_leftAdjointUniq_hom_app adjActual adjNaive (𝒪 |_ U)
  have hUnit' :
      adjActual.unit.app (𝒪 |_ U) ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
            (u.hom.app (𝒪 |_ U)) =
        adjNaive.unit.app (𝒪 |_ U) := by
    exact hUnit
  have hCancel :
      e.hom ≫ (e.inv ≫ (u.hom.app (𝒪 |_ U))) = u.hom.app (𝒪 |_ U) := by
    simpa only [Category.assoc] using
      Iso.hom_inv_id_assoc e (u.hom.app (𝒪 |_ U))
  have hMap :
      (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
            (e.inv ≫ (u.hom.app (𝒪 |_ U))) =
        (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
          (u.hom.app (𝒪 |_ U)) := by
    rw [← Functor.map_comp, hCancel]
  have hRight :
      adjActual.unit.app (𝒪 |_ U) ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
            (e.inv ≫ (u.hom.app (𝒪 |_ U))) =
        adjActual.unit.app (𝒪 |_ U) ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
            (u.hom.app (𝒪 |_ U)) := by
    simpa only [Category.assoc] using
      congrArg (fun t ↦ adjActual.unit.app (𝒪 |_ U) ≫ t) hMap
  change (adjActual.unit.app (𝒪 |_ U) ≫
      (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom) ≫
      (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
        (e.inv ≫ (u.hom.app (𝒪 |_ U))) = adjNaive.unit.app (𝒪 |_ U)
  rw [Category.assoc, hRight, hUnit']

/-- Helper for Lemma 6.33.3: on a represented cover-subordinate open, the ambient-to-local
adjunction unit is the inverse of `moduleOpenCoverRingSectionIsoOfLE`. -/
theorem moduleOpenCoverRingSectionIsoOfLE_hom_unit_id
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W : Opens X} {i : ι} (hWi : W ≤ U i) :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W) ≫
          (moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).hom = 𝟙 _ := by
  let hf := (U i).isOpenEmbedding
  haveI := hf.functor_isContinuous
  let adjActual := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion (U i))
  let adjNaive :
      hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetInclusion (U i)) :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology (openSubsetSpace (U i)))
      (Opens.grothendieckTopology X)
  have hUnit := Adjunction.unit_leftAdjointUniq_hom_app adjActual adjNaive 𝒪
  have hUnit' :
      adjActual.unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion (U i))).map
            ((openEmbeddingSheafPullbackIsoRing ((U i).isOpenEmbedding)).hom.app 𝒪) =
        adjNaive.unit.app 𝒪 := by
    exact hUnit
  let A := ((U i).isOpenEmbedding).functor.obj (subspaceOpenOfLE hWi)
  let p : 𝒪.obj.obj (op A) = 𝒪.obj.obj (op W) := by
    change
      𝒪.obj.obj
          (op (((U i).isOpenEmbedding).functor.obj
            (subspaceOpenOfLE hWi))) =
        𝒪.obj.obj (op W)
    simp [subspaceOpenOfLEImageEq]
  have hApp := congrArg (fun η => η.hom.app (op W)) hUnit'
  have hApp' :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W) ≫
        (((TopCat.Sheaf.forget RingCat (openSubsetSpace (U i))).mapIso
          ((openEmbeddingSheafPullbackIsoRing
            ((U i).isOpenEmbedding)).app 𝒪)).app
          (op (subspaceOpenOfLE hWi))).hom =
        (adjNaive.unit.app 𝒪).hom.app (op W) := by
    simpa only [adjActual, Topology.IsOpenEmbedding.sheafPullback, Functor.mapIso_hom] using
      hApp
  change
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W) ≫
        (((TopCat.Sheaf.forget RingCat (openSubsetSpace (U i))).mapIso
          ((openEmbeddingSheafPullbackIsoRing
            ((U i).isOpenEmbedding)).app 𝒪)).app
          (op (subspaceOpenOfLE hWi))).hom) ≫
        (eqToIso p).hom = 𝟙 _
  rw [hApp']
  change (adjNaive.unit.app 𝒪).hom.app (op W) ≫ (eqToIso p).hom = 𝟙 _
  simp [adjNaive, Topology.IsOpenEmbedding.sheafPullback, IsOpenMap.adjunction,
    Adjunction.sheafPushforwardContinuous]
  let hA : A = W := by simp [A, subspaceOpenOfLEImageEq]
  change 𝒪.obj.map (eqToHom hA).op ≫ (eqToIso p).hom = 𝟙 _
  have hmap : 𝒪.obj.map (eqToHom hA).op = (eqToIso p).inv := by
    have h' :
        𝒪.obj.map (eqToHom (congrArg Opposite.op hA.symm)) = eqToHom p.symm := by
      simpa [p] using CategoryTheory.eqToHom_map 𝒪.obj (congrArg Opposite.op hA.symm)
    simpa using h'
  rw [hmap]
  simp

/-- Helper for Lemma 6.33.3: the inverse of the cover-local ring section comparison is the
ambient-to-local adjunction unit on represented opens. -/
theorem moduleOpenCoverRingSectionIsoOfLE_inv_eq_unit
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W : Opens X} {i : ι} (hWi : W ≤ U i) :
    (moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv =
      (show 𝒪.obj.obj (op W) ⟶ (𝒪 |_ U i).obj.obj (op (subspaceOpenOfLE hWi)) from
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W)) := by
  let e := moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi
  let u : 𝒪.obj.obj (op W) ⟶ (𝒪 |_ U i).obj.obj (op (subspaceOpenOfLE hWi)) :=
    show 𝒪.obj.obj (op W) ⟶ (𝒪 |_ U i).obj.obj (op (subspaceOpenOfLE hWi)) from
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W)
  symm
  change u = e.inv
  rw [← Category.comp_id u]
  rw [← e.hom_inv_id]
  change (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W) ≫
      (moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).hom) ≫ e.inv = e.inv
  rw [moduleOpenCoverRingSectionIsoOfLE_hom_unit_id (U := U) (𝒪 := 𝒪) hWi]
  simp

/-- Helper for Lemma 6.33.3: the naive open-embedding adjunction unit on sections is the
restriction map along the represented-open equality. -/
theorem openSubsetHomOfLE_naiveUnit_app_eq_map
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    {W U V : Opens X} (hWU : W ≤ U) (hVW : V ≤ W) (hVU : V ≤ U)
    (hOpen : ((openSubsetHomOfLE_isOpenEmbedding hWU).functor.obj (subspaceOpenOfLE hVW)) =
      subspaceOpenOfLE hVU)
    (x : (𝒪 |_ U).obj.obj (op (subspaceOpenOfLE hVU))) :
      let hf := openSubsetHomOfLE_isOpenEmbedding hWU
      letI := hf.functor_isContinuous
      let adjNaive :
        hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hWU) :=
        hf.isOpenMap.adjunction.sheafPushforwardContinuous
          (Opens.grothendieckTopology (openSubsetSpace W))
          (Opens.grothendieckTopology (openSubsetSpace U))
      ((adjNaive.unit.app (𝒪 |_ U)).hom.app (op (subspaceOpenOfLE hVU))).hom x =
        ((𝒪 |_ U).obj.map (eqToHom hOpen).op).hom x := by
  let hf := openSubsetHomOfLE_isOpenEmbedding hWU
  haveI := hf.functor_isContinuous
  let adjNaive :
      hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hWU) :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))
  change ((adjNaive.unit.app (𝒪 |_ U)).hom.app (op (subspaceOpenOfLE hVU))).hom x =
        ((𝒪 |_ U).obj.map (eqToHom hOpen).op).hom x
  simp [adjNaive, Topology.IsOpenEmbedding.sheafPullback, IsOpenMap.adjunction,
    Adjunction.sheafPushforwardContinuous]
  congr 1

/-- Helper for Lemma 6.33.3: the scalar transported from the left endpoint of an overlap agrees
with the scalar obtained by restricting the ambient section directly to the overlap. -/
theorem moduleOpenCoverLeftEndpoint_scalar
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W : Opens X} {i j : ι}
    (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W)) :
    let hWij := subset_overlap_le (U := U) hWi hWj
    let hPair : U i ⊓ U j ≤ U i := inf_le_left
    let hOpen : ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj
          (subspaceOpenOfLE hWij)) = subspaceOpenOfLE hWi := by
      simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]
    ((𝒪 |_ U i).obj.map (eqToHom hOpen).op).hom
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv.hom r) =
    ((moduleSheafRestrictionOpenPushRingIso 𝒪 hPair).hom.hom.app
      (op (subspaceOpenOfLE hWij))).hom
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r) := by
  let hWij := subset_overlap_le (U := U) hWi hWj
  let hPair : U i ⊓ U j ≤ U i := inf_le_left
  let hOpen : ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj
        (subspaceOpenOfLE hWij)) = subspaceOpenOfLE hWi := by
    simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]
  change ((𝒪 |_ U i).obj.map (eqToHom hOpen).op).hom
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv.hom r) =
    ((moduleSheafRestrictionOpenPushRingIso 𝒪 hPair).hom.hom.app
      (op (subspaceOpenOfLE hWij))).hom
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r)
  rw [moduleOpenCoverRingSectionIsoOfLE_inv_eq_unit (U := U) (𝒪 := 𝒪) hWi]
  rw [moduleOpenCoverRingSectionIsoOfLE_inv_eq_unit
    (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
    (i := PUnit.unit.{u+1}) hWij]
  let hf := openSubsetHomOfLE_isOpenEmbedding hPair
  haveI := hf.functor_isContinuous
  let adjNaive :
      hf.sheafPullback RingCat ⊣ TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hPair) :=
    hf.isOpenMap.adjunction.sheafPushforwardContinuous
      (Opens.grothendieckTopology (openSubsetSpace (U i ⊓ U j)))
      (Opens.grothendieckTopology (openSubsetSpace (U i)))
  let μ := moduleSheafRestrictionOpenPushRingIso 𝒪 hPair
  let x : (𝒪 |_ U i).obj.obj (op (subspaceOpenOfLE hWi)) :=
    (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
      (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W)).hom r
  change ((𝒪 |_ U i).obj.map (eqToHom hOpen).op).hom x =
    ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i ⊓ U j))).unit.app 𝒪).hom.app (op W)).hom r))
  have hNaive := openSubsetHomOfLE_naiveUnit_app_eq_map (𝒪 := 𝒪) hPair hWij hWi hOpen x
  have hPush := moduleSheafRestrictionOpenPushRingIso_unit (𝒪 := 𝒪) hPair
  have hPushApp := congrArg (fun η => η.hom.app (op (subspaceOpenOfLE hWi))) hPush
  have hPush_x := congrArg (fun f => f.hom x) hPushApp
  have hPush_x' :
      ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
        (((restrictedRingSheafToPushforward 𝒪 hPair).hom.app
          (op (subspaceOpenOfLE hWi))).hom x)) =
      ((adjNaive.unit.app (𝒪 |_ U i)).hom.app (op (subspaceOpenOfLE hWi))).hom x := by
    change
      (((restrictedRingSheafToPushforward 𝒪 hPair).hom.app
          (op (subspaceOpenOfLE hWi)) ≫
        (μ.hom.hom.app (op (subspaceOpenOfLE hWij)))).hom x) =
      ((adjNaive.unit.app (𝒪 |_ U i)).hom.app (op (subspaceOpenOfLE hWi))).hom x at hPush_x
    simpa using hPush_x
  have hComp := restrictedRingSheafToOpenComp_eq 𝒪 hPair
  have hCompApp := congrArg (fun η => η.hom.app (op W)) hComp
  have hComp_r := congrArg (fun f => f.hom r) hCompApp
  have hComp_r' :
      (((restrictedRingSheafToPushforward 𝒪 hPair).hom.app
          (op (subspaceOpenOfLE hWi))).hom x) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i ⊓ U j))).unit.app 𝒪).hom.app (op W)).hom r) := by
    change
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
          (openSubsetInclusion (U i))).unit.app 𝒪).hom.app (op W) ≫
        (restrictedRingSheafToPushforward 𝒪 hPair).hom.app (op (subspaceOpenOfLE hWi))).hom r) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (openSubsetInclusion (U i ⊓ U j))).unit.app 𝒪).hom.app (op W)).hom r) at hComp_r
    simpa [x] using hComp_r
  have hNaive' :
      ((adjNaive.unit.app (𝒪 |_ U i)).hom.app (op (subspaceOpenOfLE hWi))).hom x =
        ((𝒪 |_ U i).obj.map (eqToHom hOpen).op).hom x := by
    simpa [adjNaive, hf] using hNaive
  exact hNaive'.symm.trans (hPush_x'.symm.trans (by
    rw [hComp_r']))

/-- Helper for Lemma 6.33.3: the left endpoint transport from a local module sheaf to an overlap
is semilinear for ambient sections. -/
theorem moduleOpenCoverLeftEndpoint_smul
    (𝒪 : TopCat.Sheaf RingCat.{w} X)
    (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
    {W : Opens X} {i j : ι} (hWi : W ≤ U i) (hWj : W ≤ U j)
    (r : 𝒪.obj.obj (op W))
    (m : (localSheaf i).val.obj (op (subspaceOpenOfLE hWi))) :
    let hWij := subset_overlap_le (U := U) hWi hWj
    let eLi := openSubsetHomOfLEOpenEmbeddingSectionIso hWij inf_le_left
      ((SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))
    (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_left).obj (localSheaf i)).val.obj
        (op (subspaceOpenOfLE hWij)) from
      eLi.inv (((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWi).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE (𝒪 := 𝒪) hWij).inv.hom r) •
        (show ((moduleSheafRestrictionOpenPush 𝒪 inf_le_left).obj (localSheaf i)).val.obj
          (op (subspaceOpenOfLE hWij)) from eLi.inv m) := by
  let hWij := subset_overlap_le (U := U) hWi hWj
  let hPair : U i ⊓ U j ≤ U i := inf_le_left
  let hOpen : ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj
        (subspaceOpenOfLE hWij)) = subspaceOpenOfLE hWi := by
    simp [openSubsetHomOfLEFunctorObjEqSubspaceOpenOfLE]
  let μ := moduleSheafRestrictionOpenPushRingIso 𝒪 hPair
  let F := ((SheafOfModules.toSheaf (𝒪 |_ U i)).obj (localSheaf i))
  let eLi := openSubsetHomOfLEOpenEmbeddingSectionIso hWij hPair F
  have heLi : eLi.inv = F.obj.map (eqToHom hOpen).op := by
    have hmap := CategoryTheory.eqToHom_map F.obj (congrArg Opposite.op hOpen.symm)
    simpa [eLi, F, openSubsetHomOfLEOpenEmbeddingSectionIso, hOpen] using hmap.symm
  change (show ((moduleSheafRestrictionOpenPush 𝒪 hPair).obj (localSheaf i)).val.obj
        (op (subspaceOpenOfLE hWij)) from
      eLi.inv (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv.hom r) • m)) =
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r) •
        (show ((moduleSheafRestrictionOpenPush 𝒪 hPair).obj (localSheaf i)).val.obj
          (op (subspaceOpenOfLE hWij)) from eLi.inv m)
  rw [heLi]
  change
    (show (localSheaf i).val.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj (subspaceOpenOfLE hWij))) from
      ((localSheaf i).val.map (eqToHom hOpen).op)
        (((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv.hom r) • m)) =
    (show (𝒪 |_ U i).obj.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj (subspaceOpenOfLE hWij))) from
      ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
        ((moduleOpenCoverRingSectionIsoOfLE
          (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
          (i := PUnit.unit.{u+1}) hWij).inv.hom r))) •
      (show (localSheaf i).val.obj
        (op ((openSubsetHomOfLE_isOpenEmbedding hPair).functor.obj (subspaceOpenOfLE hWij))) from
        ((localSheaf i).val.map (eqToHom hOpen).op) m)
  rw [(localSheaf i).val.map_smul]
  have hscalar := moduleOpenCoverLeftEndpoint_scalar (U := U) (𝒪 := 𝒪) hWi hWj r
  change
    ((𝒪 |_ U i).obj.map (eqToHom hOpen).op).hom
      ((moduleOpenCoverRingSectionIsoOfLE (U := U) (𝒪 := 𝒪) hWi).inv.hom r) =
    ((μ.hom.hom.app (op (subspaceOpenOfLE hWij))).hom
      ((moduleOpenCoverRingSectionIsoOfLE
        (U := fun _ : PUnit.{u+1} => U i ⊓ U j) (𝒪 := 𝒪)
        (i := PUnit.unit.{u+1}) hWij).inv.hom r)) at hscalar
  rw [hscalar]
  rfl

end
