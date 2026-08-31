module

public import stacks_project.Chap06.Lemma_6_33_3_Part7

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf
open TopologicalSpace.Opens

attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory

noncomputable section

universe w u

section

variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}

/-- Restricting the restriction of `𝒪` to `U` further to `W ⊆ U` gives the restriction of `𝒪`
directly to `W`. -/
noncomputable def restrictedRingSheafPullbackIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪) ≅
      (TopCat.Sheaf.pullback RingCat (openSubsetInclusion W)).obj 𝒪 :=
  let e :
      TopCat.Sheaf.pullback RingCat (openSubsetInclusion U) ⋙
          TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h) ≅
        TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h ≫ openSubsetInclusion U) :=
    (TopCat.Sheaf.pullbackComp (openSubsetHomOfLE h) (openSubsetInclusion U) :
      TopCat.Sheaf.pullback RingCat (openSubsetInclusion U) ⋙
          TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h) ≅
        TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h ≫ openSubsetInclusion U))
  e.app 𝒪 ≪≫
    eqToIso (congrArg
      (fun f ↦ (TopCat.Sheaf.pullback RingCat f).obj 𝒪)
      (openSubsetHomOfLE_comp_inclusion h))

/-- The canonical map of restricted ring sheaves attached to an inclusion `W ⊆ U`. -/
noncomputable def restrictedRingSheafToPushforward
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪 ⟶
      ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W))).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion W)).obj 𝒪) :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
      ((TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪)) ≫
    ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).mapIso
      (restrictedRingSheafPullbackIso 𝒪 h)).hom

/-- Restriction of a ring sheaf to an open subset, as a sheaf on the corresponding open
subspace. -/
abbrev ringSheafRestriction (𝒪 : TopCat.Sheaf RingCat X) (U : Opens X) :
    TopCat.Sheaf RingCat (openSubsetSpace U) :=
  (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪

namespace TopCat

set_option quotPrecheck false in
scoped notation:80 𝒪:80 " |_ " U:80 =>
  ringSheafRestriction 𝒪 U

end TopCat

open scoped TopCat

/- Domain-style sampling for the module-valued restriction step:
- primary domain: inverse-image/restriction of sheaves of modules along open inclusions;
- sampled owner declarations: `SheafOfModules.pullback`, `SheafOfModules.pullbackComp`,
  `moduleSheafRestrictionToOpen`, `moduleSheafExtensionByZeroAdjunction`;
- owner abstraction: the core owner is `SheafOfModules.pullback`, while
  `moduleSheafRestrictionToOpen` is the chapter’s canonical open-immersion specialization;
- source/core/bridge triage: the source-facing surface is the restricted ring sheaf notation
  `𝒪 |_ U`; `SheafOfModules.pullback` is core/canonical; and the pairwise overlap restrictions
  below are thin bridge/view specializations for the named inclusions in the open-cover
  geometry. -/

/- Restriction of sheaves of modules along an inclusion `W ⊆ U` of open subsets. -/
/-- Helper for Lemma 6.33.3: unfolding the internal restriction owner exposes the
pullback/pushforward adjunction unit on `openSubsetSpace U` followed by the single codomain
transport to the directly restricted ring sheaf `𝒪 |_ W`. -/
theorem restrictedRingSheafToPushforward_def
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    restrictedRingSheafToPushforward 𝒪 h =
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U)) ≫
        ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).mapIso
          (restrictedRingSheafPullbackIso 𝒪 h)).hom) := by
  -- This is exactly the defining formula of `restrictedRingSheafToPushforward`.
  rfl

/-- Helper for Lemma 6.33.3: changing the ring sheaf along
`restrictedRingSheafPullbackIso 𝒪 h` is an equivalence on module sheaves, hence its pushforward is
a right adjoint. -/
theorem restrictedRingSheafPullbackIso_pushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W)))
      ((restrictedRingSheafPullbackIso 𝒪 h).hom)).IsRightAdjoint := by
  let e := restrictedRingSheafPullbackIso 𝒪 h
  let transportPush :
      SheafOfModules (𝒪 |_ W) ⥤
        SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) :=
    SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W))) e.hom
  let transportInverse :
      SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) ⥤
        SheafOfModules (𝒪 |_ W) :=
    SheafOfModules.pushforward (F := 𝟭 (Opens (openSubsetSpace W))) e.inv
  have transport_push_inverse_id :
      e.inv ≫
          (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
              (Opens.grothendieckTopology (openSubsetSpace W))
              (Opens.grothendieckTopology (openSubsetSpace W))).map e.hom) =
        𝟙 (𝒪 |_ W) := by
    -- On the identity site, pushing forward a morphism of ring sheaves does not change its
    -- sectionwise action, so the composite reduces to `e.inv ≫ e.hom` on `𝒪 |_ W`.
    rw [show
      (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace W))).map e.hom) = e.hom by
      rfl]
    cases e with
    | mk hom inv hom_inv_id inv_hom_id =>
        simpa [ringSheafRestriction] using inv_hom_id
  have transport_inverse_push_id :
      e.hom ≫
          (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
              (Opens.grothendieckTopology (openSubsetSpace W))
              (Opens.grothendieckTopology (openSubsetSpace W))).map e.inv) =
        𝟙 ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) := by
    -- The same sectionwise computation identifies the opposite composite with `e.hom ≫ e.inv`
    -- on the pullback ring sheaf.
    rw [show
      (((𝟭 (Opens (openSubsetSpace W))).sheafPushforwardContinuous RingCat
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace W))).map e.inv) = e.inv by
      rfl]
    cases e with
    | mk hom inv hom_inv_id inv_hom_id =>
        simpa [ringSheafRestriction] using hom_inv_id
  -- Route correction: isolate the codomain transport from the geometric restriction map and
  -- package it as an identity-site equivalence built from `pushforwardComp` and `pushforwardId`.
  let transportUnitIso :
      𝟭 (SheafOfModules (𝒪 |_ W)) ≅
        transportPush ⋙ transportInverse :=
    (SheafOfModules.pushforwardId (𝒪 |_ W)).symm ≪≫
      SheafOfModules.pushforwardCongr transport_push_inverse_id.symm ≪≫
      (SheafOfModules.pushforwardComp
        (F := 𝟭 (Opens (openSubsetSpace W)))
        (G := 𝟭 (Opens (openSubsetSpace W)))
        e.inv e.hom).symm
  let transportCounitIso :
      transportInverse ⋙ transportPush ≅
        𝟭 (SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U))) :=
    SheafOfModules.pushforwardComp
        (F := 𝟭 (Opens (openSubsetSpace W)))
        (G := 𝟭 (Opens (openSubsetSpace W)))
        e.hom e.inv ≪≫
      SheafOfModules.pushforwardCongr transport_inverse_push_id ≪≫
      SheafOfModules.pushforwardId
        ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U))
  let transportEquiv :
      SheafOfModules (𝒪 |_ W) ≌
        SheafOfModules ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).obj (𝒪 |_ U)) :=
    CategoryTheory.Equivalence.mk
      transportPush
      transportInverse
      transportUnitIso
      transportCounitIso
  letI : transportPush.IsEquivalence :=
    transportEquiv.isEquivalence_functor
  -- Any equivalence is in particular a right adjoint.
  infer_instance

/-- Helper for Lemma 6.33.3: the geometric unit factor in the internal restriction owner already
is a right adjoint by the generic module pullback/pushforward adjunction for the explicit
restriction functor `openSubsetRestrictionFunctor h`. -/
theorem moduleSheafRestrictionUnit_pushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward.{w} (F := openSubsetRestrictionFunctor h)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
        (𝒪 |_ U)))).IsRightAdjoint := by
  let K := Opens.grothendieckTopology (openSubsetSpace W)
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U)) K :=
    openSubsetRestrictionFunctor_isContinuous h
  letI : ∀ V : Opens (openSubsetSpace W), IsCofiltered (K.Cover V) :=
    fun V => CategoryTheory.isCofiltered_of_directed_ge_nonempty (K.Cover V)
  letI : ∀ V : Opens (openSubsetSpace W), IsFiltered (K.Cover V)ᵒᵖ :=
    fun V => CategoryTheory.isFiltered_op_of_isCofiltered (K.Cover V)
  letI :
      ∀ V : Opens (openSubsetSpace W),
        PreservesColimitsOfShape (K.Cover V)ᵒᵖ (forget AddCommGrpCat.{w}) :=
    fun V =>
      PreservesFilteredColimitsOfSize.preserves_filtered_colimits
        ((K.Cover V)ᵒᵖ) (F := forget AddCommGrpCat.{w})
  letI : HasWeakSheafify K AddCommGrpCat.{w} := by
    letI : HasSheafify K AddCommGrpCat.{w} :=
      CategoryTheory.instHasSheafifyOfPreservesLimitsForgetOfHasFiniteLimitsOfSmallOppositeCover
        K AddCommGrpCat.{w}
    exact CategoryTheory.instHasWeakSheafifyOfHasSheafify K AddCommGrpCat.{w}
  letI : K.HasSheafCompose (forget AddCommGrpCat.{w}) :=
    CategoryTheory.hasSheafCompose_of_preservesMulticospan K (forget AddCommGrpCat.{w})
  letI : K.PreservesSheafification (forget AddCommGrpCat.{w}) :=
    CategoryTheory.GrothendieckTopology.instPreservesSheafificationForgetOfPreservesLimitsOfHasColimitsOfShapeOfPreservesColimitsOfShapeOppositeCoverOfHasLimitsOfShapeWalkingMulticospanOfReflectsIsomorphisms
      K
  letI : K.WEqualsLocallyBijective AddCommGrpCat.{w} :=
    CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeakSheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget
      K
  letI :
      (PresheafOfModules.pushforward.{w} (F := openSubsetRestrictionFunctor h)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U))).hom).IsRightAdjoint :=
    (PresheafOfModules.pullbackPushforwardAdjunction (F := openSubsetRestrictionFunctor h)
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
        (𝒪 |_ U))).hom).isRightAdjoint
  exact
    (SheafOfModules.PullbackConstruction.adjunction.{w}
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
        (𝒪 |_ U)))).isRightAdjoint

instance moduleSheafRestrictionPushforward_isRightAdjoint
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (SheafOfModules.pushforward.{w} (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint := by
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  letI :
      (SheafOfModules.pushforward.{w} (F := openSubsetRestrictionFunctor h)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U)))).IsRightAdjoint :=
    moduleSheafRestrictionUnit_pushforward_isRightAdjoint 𝒪 h
  letI :
      (SheafOfModules.pushforward.{w} (F := 𝟭 (Opens (openSubsetSpace W)))
        ((restrictedRingSheafPullbackIso 𝒪 h).hom)).IsRightAdjoint :=
    restrictedRingSheafPullbackIso_pushforward_isRightAdjoint 𝒪 h
  let hCompIso :
      (SheafOfModules.pushforward.{w} (F := 𝟭 (Opens (openSubsetSpace W)))
          ((restrictedRingSheafPullbackIso 𝒪 h).hom)) ⋙
        (SheafOfModules.pushforward.{w} (F := openSubsetRestrictionFunctor h)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
            (𝒪 |_ U)))) ≅
      SheafOfModules.pushforward.{w}
        (F := openSubsetRestrictionFunctor h ⋙ 𝟭 (Opens (openSubsetSpace W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
            (𝒪 |_ U))) ≫
          ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map
            ((restrictedRingSheafPullbackIso 𝒪 h).hom)) :=
    -- Freeze the source spelling of `pushforwardComp` before any normalization.
    SheafOfModules.pushforwardComp.{w}
      (F := openSubsetRestrictionFunctor h)
      (G := 𝟭 (Opens (openSubsetSpace W)))
      (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U)))
      ((restrictedRingSheafPullbackIso 𝒪 h).hom)
  have hSourceRightAdjoint :
      ((SheafOfModules.pushforward.{w} (F := 𝟭 (Opens (openSubsetSpace W)))
          ((restrictedRingSheafPullbackIso 𝒪 h).hom)) ⋙
        (SheafOfModules.pushforward.{w} (F := openSubsetRestrictionFunctor h)
          (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
            (𝒪 |_ U))))).IsRightAdjoint := by
    infer_instance
  -- Route correction: split the owner into the geometric unit factor and the codomain transport,
  -- then invoke the generic right-adjoint package for pushforward along a composite.
  change
    (SheafOfModules.pushforward.{w}
      (F := openSubsetRestrictionFunctor h ⋙ 𝟭 (Opens (openSubsetSpace W)))
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)).unit.app
          (𝒪 |_ U))) ≫
        ((openSubsetRestrictionFunctor h).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology (openSubsetSpace U))
          (Opens.grothendieckTopology (openSubsetSpace W))).map
          ((restrictedRingSheafPullbackIso 𝒪 h).hom))).IsRightAdjoint
  exact @Functor.isRightAdjoint_of_iso _ _ _ _ _ _ hCompIso hSourceRightAdjoint

noncomputable abbrev moduleSheafRestriction
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules.{w} (𝒪 |_ U) ⥤
      SheafOfModules.{w} (𝒪 |_ W) :=
  let _ :
      (SheafOfModules.pushforward.{w} (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint :=
    moduleSheafRestrictionPushforward_isRightAdjoint 𝒪 h
  SheafOfModules.pullback.{w} (restrictedRingSheafToPushforward 𝒪 h)

/-- Restriction of `𝒪|_U`-modules to `\mathcal O|_{U \cap V}` along the left inclusion
`U \cap V \subset U`. -/
noncomputable abbrev moduleSheafRestrictionToPairLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  moduleSheafRestriction 𝒪 inf_le_left

/-- Restriction of `𝒪|_V`-modules to `\mathcal O|_{U \cap V}` along the right inclusion
`U \cap V \subset V`. -/
noncomputable abbrev moduleSheafRestrictionToPairRight
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V)) :=
  moduleSheafRestriction 𝒪 inf_le_right

abbrev moduleRestrictToTripleFirst
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ U) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_left)

abbrev moduleRestrictToTripleSecond
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ V) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    ((show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left).trans inf_le_right)

abbrev moduleRestrictToTripleThird
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ W) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 inf_le_right

abbrev moduleRestrictOverlapToTripleLeft
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ V)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 inf_le_left

abbrev moduleRestrictOverlapToTripleCenter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (V ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪 (inf_le_inf inf_le_right le_rfl)

abbrev moduleRestrictOverlapToTripleOuter
    (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    SheafOfModules (𝒪 |_ (U ⊓ W)) ⥤
      SheafOfModules (𝒪 |_ (U ⊓ V ⊓ W)) :=
  moduleSheafRestriction 𝒪
    (inf_le_inf (show U ⊓ V ≤ U from inf_le_left) le_rfl)

/-- Helper for Lemma 6.33.3: composing two internal restriction owners agrees with the direct
restriction owner. -/
theorem restrictedRingSheafToPushforward_comp_eq
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    restrictedRingSheafToPushforward 𝒪 hWU ≫
        ((openSubsetRestrictionFunctor hWU).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology (openSubsetSpace U))
          (Opens.grothendieckTopology (openSubsetSpace W))).map
        (restrictedRingSheafToPushforward 𝒪 hTW) =
      restrictedRingSheafToPushforward 𝒪 (hTW.trans hWU) := by
  let A := (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪
  let eWU := restrictedRingSheafPullbackIso 𝒪 hWU
  let eTW := restrictedRingSheafPullbackIso 𝒪 hTW
  let eTU := restrictedRingSheafPullbackIso 𝒪 (hTW.trans hWU)
  let adjWU := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE hWU)
  let adjTW := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE hTW)
  let adjTU :=
    TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE (hTW.trans hWU))
  let compIso :=
    TopCat.Sheaf.pullbackComp (A := RingCat)
      (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU)
  let hIsoLHS :
      ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE hTW)).obj
        ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE hWU)).obj A)) ⟶
        (TopCat.Sheaf.pullback RingCat (openSubsetInclusion T)).obj 𝒪 :=
    (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE hTW)).map eWU.hom ≫ eTW.hom
  have hIso :
      hIsoLHS = compIso.hom.app A ≫ eTU.hom := by
    dsimp [restrictedRingSheafPullbackIso]
    simpa only [openSubsetHomOfLE_comp_inclusion, openSubsetHomOfLE_comp,
      eqToIso_refl, Iso.trans_hom, Category.id_comp, Category.comp_id,
      Functor.map_comp, Category.assoc, A, eWU, eTW, eTU, compIso, hIsoLHS] using
      sheaf_pullback_comp_assoc_hom_ring
        (openSubsetHomOfLE hTW) (openSubsetHomOfLE hWU)
        (openSubsetInclusion U) 𝒪
  have hLeft :
      restrictedRingSheafToPushforward 𝒪 hWU ≫
          ((openSubsetRestrictionFunctor hWU).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map
            (restrictedRingSheafToPushforward 𝒪 hTW) =
        (adjWU.comp adjTW).unit.app A ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hWU)).map
            ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hTW)).map hIsoLHS) := by
    have hnat :
        eWU.hom ≫ adjTW.unit.app ((TopCat.Sheaf.pullback RingCat
              (openSubsetInclusion W)).obj 𝒪) ≫
            (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hTW)).map eTW.hom =
          adjTW.unit.app ((TopCat.Sheaf.pullback RingCat
              (openSubsetHomOfLE hWU)).obj A) ≫
            (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hTW)).map
              ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE hTW)).map eWU.hom) ≫
            (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hTW)).map eTW.hom := by
      simpa only [adjTW, A, eWU, eTW, Category.assoc] using
        congrArg
          (fun k ↦ k ≫
            (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hTW)).map eTW.hom)
          (adjTW.unit.naturality eWU.hom)
    simpa only [restrictedRingSheafToPushforward, hIsoLHS, eWU, eTW, adjWU, adjTW, A,
      Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] using
      congrArg
        (fun k ↦ adjWU.unit.app A ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hWU)).map k)
        hnat
  have hCompInv :
      (Adjunction.leftAdjointUniq adjTU (adjWU.comp adjTW)).hom.app A =
        compIso.inv.app A := by
    rfl
  have hUnit :
      (adjWU.comp adjTW).unit.app A =
        adjTU.unit.app A ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map
            (compIso.inv.app A) := by
    simpa only [hCompInv, adjTU, adjWU, adjTW, compIso, Category.assoc] using
      (Adjunction.unit_leftAdjointUniq_hom_app adjTU (adjWU.comp adjTW) A).symm
  have hCancel :
      compIso.inv.app A ≫ hIsoLHS = eTU.hom := by
    rw [hIso]
    simpa only [Category.assoc] using
      congrArg (fun t ↦ t ≫ eTU.hom) (Iso.inv_hom_id_app compIso A)
  have hAfterUnit :
      (adjWU.comp adjTW).unit.app A ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hWU)).map
            ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE hTW)).map hIsoLHS) =
        adjTU.unit.app A ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map
            eTU.hom := by
    rw [hUnit]
    change
      (adjTU.unit.app A ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map
            (compIso.inv.app A)) ≫
        (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map
          hIsoLHS =
      adjTU.unit.app A ≫
        (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map eTU.hom
    have hMap :
        (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map
            (compIso.inv.app A) ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map hIsoLHS =
        (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map eTU.hom := by
      simpa only [Functor.map_comp] using
        congrArg
          (fun k ↦
            (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE (hTW.trans hWU))).map k)
          hCancel
    simpa only [Category.assoc] using
      congrArg (fun k ↦ adjTU.unit.app A ≫ k) hMap
  exact hLeft.trans (hAfterUnit.trans (by rfl))

/-- Helper for Lemma 6.33.3: restricting first to `U` and then internally to `W ⊆ U` gives the
same ring-sheaf owner as restricting directly to `W`. -/
theorem restrictedRingSheafToOpenComp_eq
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪) ≫
        (((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
          (Opens.grothendieckTopology X)
          (Opens.grothendieckTopology (openSubsetSpace U))).map
          (restrictedRingSheafToPushforward 𝒪 h)) =
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion W)).unit.app 𝒪) := by
  let A := (TopCat.Sheaf.pullback RingCat (openSubsetInclusion U)).obj 𝒪
  let e := restrictedRingSheafPullbackIso 𝒪 h
  let adjU := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)
  let adjWU := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)
  let adjW := TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion W)
  let compIso :=
    TopCat.Sheaf.pullbackComp (A := RingCat)
      (openSubsetHomOfLE h) (openSubsetInclusion U)
  have hLeft :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪) ≫
          (((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace U))).map
            (restrictedRingSheafToPushforward 𝒪 h)) =
        (adjU.comp adjWU).unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion U)).map
            ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom) := by
    change
      adjU.unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion U)).map
            (adjWU.unit.app A ≫
              (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom) =
        (adjU.unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion U)).map
            (adjWU.unit.app A)) ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion U)).map
            ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom)
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hCompInv :
      (Adjunction.leftAdjointUniq adjW (adjU.comp adjWU)).hom.app 𝒪 =
        compIso.inv.app 𝒪 := by
    rfl
  have hUnit :
      (adjU.comp adjWU).unit.app 𝒪 =
        adjW.unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion W)).map
            (compIso.inv.app 𝒪) := by
    simpa only [hCompInv, adjU, adjWU, adjW, compIso, Category.assoc] using
      (Adjunction.unit_leftAdjointUniq_hom_app adjW (adjU.comp adjWU) 𝒪).symm
  have hCancel :
      compIso.inv.app 𝒪 ≫ e.hom = 𝟙 _ := by
    dsimp [e, restrictedRingSheafPullbackIso]
    simpa only [openSubsetHomOfLE_comp_inclusion, eqToIso_refl, Iso.trans_hom,
      Category.comp_id] using
      Iso.inv_hom_id_app compIso 𝒪
  have hAfterUnit :
      (adjU.comp adjWU).unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion U)).map
            ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom) =
        adjW.unit.app 𝒪 := by
    rw [hUnit]
    change
      (adjW.unit.app 𝒪 ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion W)).map
            (compIso.inv.app 𝒪)) ≫
        (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion W)).map e.hom =
      adjW.unit.app 𝒪
    have hMap :
        (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion W)).map
            (compIso.inv.app 𝒪) ≫
          (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion W)).map e.hom =
        𝟙 _ := by
      simpa only [Functor.map_comp, Functor.map_id] using
        congrArg
          (fun k ↦ (TopCat.Sheaf.pushforward RingCat (openSubsetInclusion W)).map k)
          hCancel
    simpa only [Category.assoc, Category.comp_id] using
      congrArg (fun k ↦ adjW.unit.app 𝒪 ≫ k) hMap
  exact hLeft.trans hAfterUnit

/-- Helper for Lemma 6.33.3: once two module-restriction owners are definitionally identified,
their pullback functors are identified by transport along that equality. -/
noncomputable abbrev moduleSheafPullbackCongrIso
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat} {R : Sheaf K RingCat} [Functor.IsContinuous F J K]
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R}
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(SheafOfModules.pushforward ψ).IsRightAdjoint]
    (hEq : φ = ψ) :
    SheafOfModules.pullback φ ≅ SheafOfModules.pullback ψ := by
  -- This isolates the equality-to-iso transport so later composition isomorphisms can use a
  -- single stable adapter instead of repeating `change` or `convert`.
  cases hEq
  -- Once the owners are literally the same morphism, the two pullback functors coincide.
  exact Iso.refl _

noncomputable def moduleSheafRestrictionCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {T W U : Opens X} (hTW : T ≤ W) (hWU : W ≤ U) :
    moduleSheafRestriction 𝒪 hWU ⋙ moduleSheafRestriction 𝒪 hTW ≅
      moduleSheafRestriction 𝒪 (hTW.trans hWU) := by
  letI :
      (openSubsetRestrictionFunctor hTW).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace T)) :=
    openSubsetRestrictionFunctor_isContinuous hTW
  letI :
      (openSubsetRestrictionFunctor hWU).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous hWU
  letI :
      (openSubsetRestrictionFunctor (hTW.trans hWU)).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace T)) :=
    openSubsetRestrictionFunctor_isContinuous (hTW.trans hWU)
  letI :
      (SheafOfModules.pushforward
        (F := openSubsetRestrictionFunctor hWU ⋙ openSubsetRestrictionFunctor hTW)
        (restrictedRingSheafToPushforward 𝒪 (hTW.trans hWU))).IsRightAdjoint := by
    -- Rewrite the direct owner to the composite restriction functor before reusing the existing
    -- right-adjoint package.
    simpa [openSubsetRestrictionFunctor_comp hTW hWU] using
      (moduleSheafRestrictionPushforward_isRightAdjoint 𝒪 (hTW.trans hWU))
  have hEq :
      restrictedRingSheafToPushforward 𝒪 hWU ≫
          ((openSubsetRestrictionFunctor hWU).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map
            (restrictedRingSheafToPushforward 𝒪 hTW) =
        restrictedRingSheafToPushforward 𝒪 (hTW.trans hWU) := by
    -- Normalize the composite inverse-image functor before comparing the two owners.
    simpa [openSubsetRestrictionFunctor_comp hTW hWU] using
      restrictedRingSheafToPushforward_comp_eq 𝒪 hTW hWU
  -- Once the owners are compared over the same restriction functor, `pullbackComp` gives the
  -- functor comparison.
  exact
    (SheafOfModules.pullbackComp
      (restrictedRingSheafToPushforward 𝒪 hWU)
      (restrictedRingSheafToPushforward 𝒪 hTW)) ≪≫
      moduleSheafPullbackCongrIso
        (F := openSubsetRestrictionFunctor hWU ⋙ openSubsetRestrictionFunctor hTW) hEq

noncomputable def moduleSheafRestrictionToOpenCompIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestriction 𝒪 h ≅
      moduleSheafRestrictionToOpen W 𝒪 := by
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  letI :
      (SheafOfModules.pushforward
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion U)).unit.app 𝒪))).IsRightAdjoint :=
    (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction U 𝒪).isRightAdjoint
  letI :
      (SheafOfModules.pushforward
        (F := Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion W)).unit.app 𝒪))).IsRightAdjoint := by
    -- Normalize the direct owner to the composite restriction functor before reusing the
    -- canonical right-adjoint instance.
    simpa [openSubsetRestrictionFunctor_comp_inclusion h] using
      (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction W 𝒪).isRightAdjoint
  have hEq :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪) ≫
          (((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace U))).map
            (restrictedRingSheafToPushforward 𝒪 h)) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion W)).unit.app 𝒪) := by
    -- The mixed owner becomes the direct owner once the restriction functors are normalized.
    simpa [openSubsetRestrictionFunctor_comp_inclusion h] using
      restrictedRingSheafToOpenComp_eq 𝒪 h
  -- Package the composite pullback, then transport its owner to the direct restriction owner.
  exact
    (SheafOfModules.pullbackComp
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪)
      (restrictedRingSheafToPushforward 𝒪 h)) ≪≫
      moduleSheafPullbackCongrIso
        (F := Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h) hEq

noncomputable def moduleRestrictToTripleFirstViaIJIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleFirst 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 U V ⋙ moduleRestrictOverlapToTripleLeft 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ U from inf_le_left)).symm

noncomputable def moduleRestrictToTripleSecondViaIJIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleSecond 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 U V ⋙ moduleRestrictOverlapToTripleLeft 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ V from inf_le_left)
    (show U ⊓ V ≤ V from inf_le_right)).symm

noncomputable def moduleRestrictToTripleSecondViaJKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleSecond 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 V W ⋙ moduleRestrictOverlapToTripleCenter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ V from inf_le_left)).symm

noncomputable def moduleRestrictToTripleThirdViaJKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleThird 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 V W ⋙ moduleRestrictOverlapToTripleCenter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ V ⊓ W from inf_le_inf inf_le_right le_rfl)
    (show V ⊓ W ≤ W from inf_le_right)).symm

noncomputable def moduleRestrictToTripleFirstViaIKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleFirst 𝒪 U V W ≅
      moduleSheafRestrictionToPairLeft 𝒪 U W ⋙ moduleRestrictOverlapToTripleOuter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ U from inf_le_left)).symm

noncomputable def moduleRestrictToTripleThirdViaIKIso
  (𝒪 : TopCat.Sheaf RingCat X) (U V W : Opens X) :
    moduleRestrictToTripleThird 𝒪 U V W ≅
      moduleSheafRestrictionToPairRight 𝒪 U W ⋙ moduleRestrictOverlapToTripleOuter 𝒪 U V W :=
  (moduleSheafRestrictionCompIso 𝒪
    (show U ⊓ V ⊓ W ≤ U ⊓ W from inf_le_inf
      (show U ⊓ V ≤ U from inf_le_left) le_rfl)
    (show U ⊓ W ≤ W from inf_le_right)).symm

noncomputable def moduleRestrictionToPairViaLeftIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    moduleSheafRestrictionToOpen (U ⊓ V) 𝒪 ≅
      moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestrictionToPairLeft 𝒪 U V :=
  (moduleSheafRestrictionToOpenCompIso 𝒪
    (show U ⊓ V ≤ U from inf_le_left)).symm

noncomputable def moduleRestrictionToPairViaRightIso
    (𝒪 : TopCat.Sheaf RingCat X) (U V : Opens X) :
    moduleSheafRestrictionToOpen (U ⊓ V) 𝒪 ≅
      moduleSheafRestrictionToOpen V 𝒪 ⋙ moduleSheafRestrictionToPairRight 𝒪 U V :=
  (moduleSheafRestrictionToOpenCompIso 𝒪
    (show U ⊓ V ≤ V from inf_le_right)).symm

noncomputable def moduleSheafRestrictionOpenPushRingIso
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    (𝒪 |_ W) ≅
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat).obj (𝒪 |_ U) :=
  (restrictedRingSheafPullbackIso 𝒪 h).symm ≪≫
    (openEmbeddingSheafPullbackIsoRing (openSubsetHomOfLE_isOpenEmbedding h)).app (𝒪 |_ U)

noncomputable def moduleSheafRestrictionOpenPush
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    SheafOfModules (𝒪 |_ U) ⥤ SheafOfModules (𝒪 |_ W) := by
  let hf := openSubsetHomOfLE_isOpenEmbedding h
  letI := hf.functor_isContinuous
  exact SheafOfModules.pushforward.{w} (F := hf.functor)
    (moduleSheafRestrictionOpenPushRingIso 𝒪 h).hom

noncomputable def moduleSheafRestrictionOpenPushAdjunction
    (𝒪 : TopCat.Sheaf RingCat X) {W U : Opens X} (h : W ≤ U) :
    moduleSheafRestrictionOpenPush 𝒪 h ⊣
      SheafOfModules.pushforward.{w} (restrictedRingSheafToPushforward 𝒪 h) := by
  let hf := openSubsetHomOfLE_isOpenEmbedding h
  letI := hf.functor_isContinuous
  letI :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  exact
    SheafOfModules.pushforwardPushforwardAdj
      (adj := hf.isOpenMap.adjunction)
      (moduleSheafRestrictionOpenPushRingIso 𝒪 h).hom
      (restrictedRingSheafToPushforward 𝒪 h)
      (by
        let e := restrictedRingSheafPullbackIso 𝒪 h
        let u := openEmbeddingSheafPullbackIsoRing hf
        let adjActual :=
          TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)
        let adjNaive :
            (openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat ⊣
              TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h) :=
          hf.isOpenMap.adjunction.sheafPushforwardContinuous
            (Opens.grothendieckTopology (openSubsetSpace W))
            (Opens.grothendieckTopology (openSubsetSpace U))
        have hUnit :=
          Adjunction.unit_leftAdjointUniq_hom_app adjActual adjNaive (𝒪 |_ U)
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
        change (adjNaive.unit.app (𝒪 |_ U)).hom =
          (adjActual.unit.app (𝒪 |_ U) ≫
              (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map e.hom ≫
              (TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).map
                (e.inv ≫ (u.hom.app (𝒪 |_ U)))).hom
        rw [← hUnit', hRight])
      (by
        let e := restrictedRingSheafPullbackIso 𝒪 h
        let u := openEmbeddingSheafPullbackIsoRing hf
        let R := 𝒪 |_ U
        let S := 𝒪 |_ W
        let ψ := restrictedRingSheafToPushforward 𝒪 h
        let adjActual :=
          TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetHomOfLE h)
        let adjNaive :
            (openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat ⊣
              TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h) :=
          hf.isOpenMap.adjunction.sheafPushforwardContinuous
            (Opens.grothendieckTopology (openSubsetSpace W))
            (Opens.grothendieckTopology (openSubsetSpace U))
        have hCounitUniq :
            u.hom.app ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).obj S) ≫
                adjNaive.counit.app S =
              adjActual.counit.app S := by
          exact Adjunction.leftAdjointUniq_hom_app_counit adjActual adjNaive S
        have hNat :
            u.hom.app R ≫
                ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat).map ψ =
              (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).map ψ ≫
                u.hom.app ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).obj S) := by
          exact (u.hom.naturality ψ).symm
        have hHomEquiv :
            adjActual.homEquiv R S e.hom = ψ := by
          rfl
        have hAdj :
            (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).map ψ ≫
                adjActual.counit.app S =
              e.hom := by
          change (adjActual.homEquiv R S).symm ψ = e.hom
          rw [← hHomEquiv]
          exact (adjActual.homEquiv R S).left_inv e.hom
        have hSheaf :
            (e.inv ≫ u.hom.app R) ≫
                ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat).map ψ ≫
                adjNaive.counit.app S =
              𝟙 S := by
          calc
            (e.inv ≫ u.hom.app R) ≫
                ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat).map ψ ≫
                adjNaive.counit.app S =
              e.inv ≫
                ((TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).map ψ ≫
                  u.hom.app ((TopCat.Sheaf.pushforward RingCat (openSubsetHomOfLE h)).obj S)) ≫
                adjNaive.counit.app S := by
                simpa only [Category.assoc] using
                  congrArg (fun t ↦ e.inv ≫ t ≫ adjNaive.counit.app S) hNat
            _ =
              e.inv ≫
                (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).map ψ ≫
                adjActual.counit.app S := by
                simpa only [Category.assoc] using
                  congrArg
                    (fun t ↦
                      e.inv ≫
                        (TopCat.Sheaf.pullback RingCat (openSubsetHomOfLE h)).map ψ ≫ t)
                    hCounitUniq
            _ = e.inv ≫ e.hom := by
                simpa only [Category.assoc] using
                  congrArg (fun t ↦ e.inv ≫ t) hAdj
            _ = 𝟙 S := by
                simpa [S] using e.inv_hom_id
        change ((e.inv ≫ u.hom.app R) ≫
              ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat).map ψ ≫
              adjNaive.counit.app S).hom =
            𝟙 (𝒪 |_ W).obj
        change ((e.inv ≫ u.hom.app R) ≫
              ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback RingCat).map ψ ≫
              adjNaive.counit.app S).hom = (𝟙 S : S ⟶ S).hom
        exact congrArg (fun η ↦ η.hom) hSheaf)
