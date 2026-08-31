module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_RealizationAux
public import stacks_project.Chap06.Lemma_6_33_3_Part10_ViaBridge
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf TopologicalSpace.Opens
attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory
noncomputable section
universe w u

section Lib
variable {X : TopCat.{w}}

/-- Naturality of the `SheafOfModules.toSheaf`/restriction comparison iso. -/
theorem moduleToAddCommGrpRestrictionIso_naturality
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U)
    (ℱ 𝒢 : SheafOfModules (𝒪 |_ U)) (f : ℱ ⟶ 𝒢) :
    ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).map
          ((SheafOfModules.toSheaf (𝒪 |_ U)).map f) ≫
        (moduleToAddCommGrpRestrictionIso 𝒪 h 𝒢).hom =
      (moduleToAddCommGrpRestrictionIso 𝒪 h ℱ).hom ≫
        (SheafOfModules.toSheaf (𝒪 |_ W)).map ((moduleSheafRestriction 𝒪 h).map f) := by
  unfold moduleToAddCommGrpRestrictionIso
  simp only [Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom, Category.assoc]
  have hcommute :
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).map
            ((SheafOfModules.toSheaf (𝒪 |_ U)).map f) ≫
          eqToHom (by apply ObjectProperty.FullSubcategory.ext; rfl) =
        (eqToHom (by apply ObjectProperty.FullSubcategory.ext; rfl) :
          ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).obj
              ((SheafOfModules.toSheaf (𝒪 |_ U)).obj ℱ) ⟶
            (SheafOfModules.toSheaf (𝒪 |_ W)).obj ((moduleSheafRestrictionOpenPush 𝒪 h).obj ℱ)) ≫
          (SheafOfModules.toSheaf (𝒪 |_ W)).map ((moduleSheafRestrictionOpenPush 𝒪 h).map f) := by
    apply (TopCat.Sheaf.forget AddCommGrpCat.{w} (openSubsetSpace W)).map_injective
    ext V x
    simp only [Functor.map_comp, TopCat.Sheaf.forget, eqToHom_map]
    rfl
  rw [← Category.assoc, hcommute, Category.assoc]
  congr 1
  have hnat := (moduleSheafRestrictionOpenPushIso 𝒪 h).hom.naturality f
  have := congrArg (SheafOfModules.toSheaf (𝒪 |_ W)).map hnat
  rw [Functor.map_comp, Functor.map_comp] at this
  exact this

theorem moduleToAddCommGrpPairLeftRestrictionIso_naturality
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (U V : Opens X)
    (ℱ 𝒢 : SheafOfModules (𝒪 |_ U)) (f : ℱ ⟶ 𝒢) :
    (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) U V).map
          ((SheafOfModules.toSheaf (𝒪 |_ U)).map f) ≫
        (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 U V 𝒢).hom =
      (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 U V ℱ).hom ≫
        (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).map
          ((moduleSheafRestrictionToPairLeft 𝒪 U V).map f) :=
  moduleToAddCommGrpRestrictionIso_naturality 𝒪 (show U ⊓ V ≤ U from inf_le_left) ℱ 𝒢 f

theorem moduleToAddCommGrpPairRightRestrictionIso_naturality
    (𝒪 : TopCat.Sheaf RingCat.{w} X) (U V : Opens X)
    (ℱ 𝒢 : SheafOfModules (𝒪 |_ V)) (f : ℱ ⟶ 𝒢) :
    (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) U V).map
          ((SheafOfModules.toSheaf (𝒪 |_ V)).map f) ≫
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 U V 𝒢).hom =
      (moduleToAddCommGrpPairRightRestrictionIso 𝒪 U V ℱ).hom ≫
        (SheafOfModules.toSheaf (𝒪 |_ (U ⊓ V))).map
          ((moduleSheafRestrictionToPairRight 𝒪 U V).map f) :=
  moduleToAddCommGrpRestrictionIso_naturality 𝒪 (show U ⊓ V ≤ V from inf_le_right) ℱ 𝒢 f

end Lib

section Construct
variable {X : TopCat.{w}} {ι : Type u} {U : ι → Opens X}
variable (𝒪 : TopCat.Sheaf RingCat.{w} X)
  (localSheaf : ∀ i : ι, SheafOfModules.{w} (𝒪 |_ U i))
  (overlapIso : ∀ i j : ι,
    (moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).obj (localSheaf i) ≅
      (moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).obj (localSheaf j))
  (cocycle : ModuleSheafOpenCover.CocycleCondition 𝒪 U localSheaf overlapIso)
  (hU : IsOpenCover U)
local notation "ℱmod" => moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU

/-- The `toSheaf`-image of the module realization iso factors through the additive realization iso
via the open restriction comparison. -/
theorem toSheaf_moduleRealizationIso_hom (i : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ U i)).map
      (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i).hom =
    (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i) ℱmod).hom ≫
      (moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i).hom := by
  rw [moduleRealizationIso, Iso.trans_hom, Functor.map_comp]
  rw [show (SheafOfModules.toSheaf (𝒪 |_ U i)).map
        (moduleIsoOfBasisLinear
          (moduleRestrictionPushForm 𝒪 localSheaf overlapIso cocycle hU i) (localSheaf i)
          (modulePushFormToLocalValIso 𝒪 localSheaf overlapIso cocycle hU i)
          (algebraicMemberSubordinateOpens_isBasis (U := U) i) _ _).hom =
      (modulePushFormToLocalAddIso 𝒪 localSheaf overlapIso cocycle hU i).hom from by
      apply (TopCat.Sheaf.forget AddCommGrpCat.{w} (openSubsetSpace (U i))).map_injective; rfl]
  rw [modulePushFormToLocalAddIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc]
  rfl

/-- The shared source comparison iso (`Λ`) for the realization bridges. -/
def bSrc (i j : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).obj
        ((moduleSheafRestrictionToOpen (U i ⊓ U j) 𝒪).obj ℱmod) ≅
      (algebraicRestrictToOpen (C := AddCommGrpCat.{w}) (U i ⊓ U j)).obj
        ((SheafOfModules.toSheaf 𝒪).obj ℱmod) :=
  moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod

/-- FACT (1a): the `toSheaf`-image of the module left realization hom equals the additive left
realization hom conjugated by the comparison isos, modulo the comp-iso square `hSq1`. -/
theorem fact1a (i j : ι)
    (hSq1 :
      (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
          ((moduleRestrictionToPairViaLeftIso 𝒪 (U i) (U j)).hom.app ℱmod) =
        (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod).hom ≫
          (algebraicGlobalRestrictionToPairViaLeftIso (C := AddCommGrpCat.{w}) (U i) (U j)).hom.app
            ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≫
          (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).map
            (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i) ℱmod).inv ≫
          (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j)
            ((moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod)).hom) :
    (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
      (ModuleSheafOpenCover.realizationLeftHom localSheaf ℱmod
        (fun i => moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i) i j) =
    (bSrc 𝒪 localSheaf overlapIso cocycle hU i j).hom ≫
      (AlgebraicSheafOpenCover.realizationLeftHom
        (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        ((SheafOfModules.toSheaf 𝒪).obj ℱmod)
        (fun i => moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i) i j) ≫
      (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i)).hom := by
  have hnat := moduleToAddCommGrpPairLeftRestrictionIso_naturality 𝒪 (U i) (U j)
    ((moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod) (localSheaf i)
    (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i).hom
  have hfac2' :
      (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
          ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).map
            (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i).hom) =
        (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j)
            ((moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod)).inv ≫
          (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).map
            ((moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i) ℱmod).hom ≫
              (moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i).hom) ≫
          (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i)).hom := by
    have hfac2 :
        (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
            ((moduleSheafRestrictionToPairLeft 𝒪 (U i) (U j)).map
              (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i).hom) =
          (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j)
              ((moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod)).inv ≫
            (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).map
              ((SheafOfModules.toSheaf (𝒪 |_ U i)).map
                (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i).hom) ≫
            (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i)).hom := by
      rw [hnat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hfac2]
    congr 2
  rw [ModuleSheafOpenCover.realizationLeftHom, Functor.map_comp, hSq1, Functor.mapIso_hom]
  refine Eq.trans (congrArg (fun t =>
      ((moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod).hom ≫
        (algebraicGlobalRestrictionToPairViaLeftIso (C := AddCommGrpCat.{w}) (U i) (U j)).hom.app
          ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≫
        (algebraicRestrictToPairLeft (C := AddCommGrpCat.{w}) (U i) (U j)).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i) ℱmod).inv ≫
        (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j)
          ((moduleSheafRestrictionToOpen (U i) 𝒪).obj ℱmod)).hom) ≫ t) hfac2') ?_
  beta_reduce
  rw [AlgebraicSheafOpenCover.realizationLeftHom, Functor.mapIso_hom, bSrc]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]

/-- FACT (1b): the viaRight mirror of `fact1a`, modulo the comp-iso square `hSq2`. -/
theorem fact1b (i j : ι)
    (hSq2 :
      (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
          ((moduleRestrictionToPairViaRightIso 𝒪 (U i) (U j)).hom.app ℱmod) =
        (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod).hom ≫
          (algebraicGlobalRestrictionToPairViaRightIso (C := AddCommGrpCat.{w}) (U i) (U j)).hom.app
            ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≫
          (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).map
            (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U j) ℱmod).inv ≫
          (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j)
            ((moduleSheafRestrictionToOpen (U j) 𝒪).obj ℱmod)).hom) :
    (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
      (ModuleSheafOpenCover.realizationRightHom localSheaf ℱmod
        (fun i => moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i) i j) =
    (bSrc 𝒪 localSheaf overlapIso cocycle hU i j).hom ≫
      (AlgebraicSheafOpenCover.realizationRightHom
        (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        ((SheafOfModules.toSheaf 𝒪).obj ℱmod)
        (fun i => moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i) i j) ≫
      (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).hom := by
  have hnat := moduleToAddCommGrpPairRightRestrictionIso_naturality 𝒪 (U i) (U j)
    ((moduleSheafRestrictionToOpen (U j) 𝒪).obj ℱmod) (localSheaf j)
    (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU j).hom
  have hfac2' :
      (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
          ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).map
            (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU j).hom) =
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j)
            ((moduleSheafRestrictionToOpen (U j) 𝒪).obj ℱmod)).inv ≫
          (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).map
            ((moduleToAddCommGrpOpenRestrictionIso 𝒪 (U j) ℱmod).hom ≫
              (moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU j).hom) ≫
          (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).hom := by
    have hfac2 :
        (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map
            ((moduleSheafRestrictionToPairRight 𝒪 (U i) (U j)).map
              (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU j).hom) =
          (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j)
              ((moduleSheafRestrictionToOpen (U j) 𝒪).obj ℱmod)).inv ≫
            (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).map
              ((SheafOfModules.toSheaf (𝒪 |_ U j)).map
                (moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU j).hom) ≫
            (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).hom := by
      rw [hnat, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
    rw [hfac2]
    congr 2
  rw [ModuleSheafOpenCover.realizationRightHom, Functor.map_comp, hSq2, Functor.mapIso_hom]
  refine Eq.trans (congrArg (fun t =>
      ((moduleToAddCommGrpOpenRestrictionIso 𝒪 (U i ⊓ U j) ℱmod).hom ≫
        (algebraicGlobalRestrictionToPairViaRightIso (C := AddCommGrpCat.{w}) (U i) (U j)).hom.app
          ((SheafOfModules.toSheaf 𝒪).obj ℱmod) ≫
        (algebraicRestrictToPairRight (C := AddCommGrpCat.{w}) (U i) (U j)).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 (U j) ℱmod).inv ≫
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j)
          ((moduleSheafRestrictionToOpen (U j) 𝒪).obj ℱmod)).hom) ≫ t) hfac2') ?_
  beta_reduce
  rw [AlgebraicSheafOpenCover.realizationRightHom, Functor.mapIso_hom, bSrc]
  set_option backward.isDefEq.respectTransparency false in
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]

/-- The overlap bridge: the `toSheaf`-image of the module overlap iso equals the additive overlap
conjugated by the pair comparison isos (immediate from the definition of `moduleOpenCoverAddOverlap`). -/
theorem bO (i j : ι) :
    (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map (overlapIso i j).hom =
      (moduleToAddCommGrpPairLeftRestrictionIso 𝒪 (U i) (U j) (localSheaf i)).inv ≫
        (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso i j).hom ≫
        (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).hom := by
  simp only [moduleOpenCoverAddOverlap, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The global module sheaf realizes the module gluing datum (Lemma 6.33.3, module case): the
restrictions recover the local module sheaves (`moduleRealizationIso`) and the overlap comparisons
agree with `overlapIso`.  The cocycle clause is checked after the faithful `SheafOfModules.toSheaf`
against the proven additive cocycle (`algebraicMemberRestrictExtendIso_cocycle`), with the
left/right realization homs translated by `fact1a`/`fact1b` and the overlap by `bO`. -/
theorem moduleOpenCoverGlobalModule_realizes :
    ModuleSheafOpenCover.Realizes U localSheaf overlapIso
      (moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU) :=
  ⟨fun i => moduleRealizationIso 𝒪 localSheaf overlapIso cocycle hU i, by
    intro i j
    refine (SheafOfModules.toSheaf (𝒪 |_ (U i ⊓ U j))).map_injective ?_
    -- The additive cocycle, restated in the syntactic form produced by `fact1a`/`fact1b`
    -- (`(toSheaf 𝒪).obj ℱmod` / `moduleRealizationAddIso`); defeq to the `.extend` form.
    have hcoh :
        AlgebraicSheafOpenCover.realizationLeftHom (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            ((SheafOfModules.toSheaf 𝒪).obj
              (moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU))
            (fun i => moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i) i j ≫
          (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso i j).hom =
        AlgebraicSheafOpenCover.realizationRightHom (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
            ((SheafOfModules.toSheaf 𝒪).obj
          (moduleOpenCoverGlobalModule 𝒪 localSheaf overlapIso cocycle hU))
            (fun i => moduleRealizationAddIso 𝒪 localSheaf overlapIso cocycle hU i) i j :=
      algebraicMemberRestrictExtendIso_cocycle (forget AddCommGrpCat.{w})
        (moduleOpenCoverAddLocal (𝒪 := 𝒪) localSheaf)
        (moduleOpenCoverAddOverlap (𝒪 := 𝒪) localSheaf overlapIso)
        (moduleOpenCoverAddCocycle (𝒪 := 𝒪) localSheaf overlapIso cocycle) hU i j
    rw [Functor.map_comp,
      fact1a 𝒪 localSheaf overlapIso cocycle hU i j
        (hSq1 𝒪 localSheaf overlapIso cocycle hU i j),
      bO 𝒪 localSheaf overlapIso i j,
      fact1b 𝒪 localSheaf overlapIso cocycle hU i j
        (hSq2 𝒪 localSheaf overlapIso cocycle hU i j)]
    set_option backward.isDefEq.respectTransparency false in
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    have hc := congrArg
      (· ≫ (moduleToAddCommGrpPairRightRestrictionIso 𝒪 (U i) (U j) (localSheaf j)).hom) hcoh
    simp only [Category.assoc] at hc
    rw [hc]⟩

end Construct
