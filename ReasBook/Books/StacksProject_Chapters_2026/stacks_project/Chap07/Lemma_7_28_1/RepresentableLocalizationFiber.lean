module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_13_5
public import stacks_project.Chap07.Lemma_7_25_2
public import stacks_project.Chap07.SheafSectionFiber
public import stacks_project.Chap07.Lemma_7_28_1.RepresentableLocalizationRawFiber

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Functor.sheafPullbackConstruction
open CategoryTheory.GrothendieckTopology
open CategoryTheory.GrothendieckTopology.Plus
open CategoryTheory.Presheaf
open Opposite

universe u₁ u₂ v₁ v₂ w

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

section

/-- Helper for Lemma 7.28.1: the forgetful functor on the large `Type` universe used for section
fibers is definitionally the identity, so it preserves sheafification tautologically. -/
instance sectionFiberPreservesSheafification_forget_large_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E) :
    L.PreservesSheafification (forget (Type (max u₁ v₁ w))) where
  le P Q f hf := by
    simpa using hf

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-- Helper for Lemma 7.28.1: the concrete `Plus` map is locally injective for
type-valued presheaves in the enlarged universe used here. -/
theorem sectionFiberToPlus_isLocallyInjective_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (L.toPlus P) := by
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) := {
    equalizerSieve_mem := by
      intro X x y h
      rw [toPlus_eq_mk, toPlus_eq_mk, eq_mk_iff_exists] at h
      obtain ⟨W, _h₁, _h₂, eq⟩ := h
      exact L.superset_covering
        (fun Y f hf ↦ congrFun (congrArg Subtype.val eq) ⟨Y, f, hf⟩) W.2 }
  infer_instance

/-- Helper for Lemma 7.28.1: the concrete `Plus` map is locally surjective for
type-valued presheaves in the enlarged universe used here. -/
theorem sectionFiberToPlus_isLocallySurjective_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (L.toPlus P) := by
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) := {
    imageSieve_mem := by
      intro X x
      obtain ⟨S, x, rfl⟩ := exists_rep x
      refine L.superset_covering (fun Y f hf ↦ ⟨x.1 ⟨Y, f, hf⟩, ?_⟩) S.2
      rw [toPlus_eq_mk, res_mk_eq_mk_pullback, eq_mk_iff_exists]
      refine ⟨S.pullback f, homOfLE le_top, 𝟙 _, ?_⟩
      ext ⟨Z, g, hg⟩
      simpa using
        x.2
          { fst.hf := hf
            snd.hf := S.1.downward_closed hf g
            r.g₁ := g
            r.g₂ := 𝟙 Z
            .. } }
  infer_instance

/-- Helper for Lemma 7.28.1: the concrete plus-plus sheafification unit is locally injective for
type-valued presheaves in the enlarged universe used here. -/
theorem sectionFiberConcreteToSheafify_isLocallyInjective_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallyInjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallyInjective L (L.toPlus P) :=
    sectionFiberToPlus_isLocallyInjective_type (L := L) P
  letI : Presheaf.IsLocallyInjective L (L.toPlus (L.plusObj P)) :=
    sectionFiberToPlus_isLocallyInjective_type (L := L) (L.plusObj P)
  -- The concrete sheafification unit is the composite of the two `Plus` maps.
  change Presheaf.IsLocallyInjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.28.1: the concrete plus-plus sheafification unit is locally surjective for
type-valued presheaves in the enlarged universe used here. -/
theorem sectionFiberConcreteToSheafify_isLocallySurjective_type
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E)
    [∀ X : E, Limits.HasColimitsOfShape (L.Cover X)ᵒᵖ (Type w)]
    [∀ P' : Eᵒᵖ ⥤ Type w, ∀ X : E, ∀ S : L.Cover X,
      Limits.HasMultiequalizer (S.index P')]
    [∀ X : E, Limits.PreservesColimitsOfShape (L.Cover X)ᵒᵖ (forget (Type w))]
    (P : Eᵒᵖ ⥤ Type w) :
    Presheaf.IsLocallySurjective L (L.toSheafify P) := by
  letI : Presheaf.IsLocallySurjective L (L.toPlus P) :=
    sectionFiberToPlus_isLocallySurjective_type (L := L) P
  letI : Presheaf.IsLocallySurjective L (L.toPlus (L.plusObj P)) :=
    sectionFiberToPlus_isLocallySurjective_type (L := L) (L.plusObj P)
  -- The concrete sheafification unit is the composite of the two `Plus` maps.
  change Presheaf.IsLocallySurjective L (L.toPlus P ≫ L.plusMap (L.toPlus P))
  rw [GrothendieckTopology.plusMap_toPlus]
  infer_instance

/-- Helper for Lemma 7.28.1: in the enlarged `Type` universe used here, local weak
equivalences are exactly locally bijective morphisms. -/
theorem sectionFiberLargeType_WEqualsLocallyBijective
    {E : Type u₁} [Category.{v₁} E] (L : GrothendieckTopology E)
    [HasWeakSheafify L (Type (max u₁ v₁ w))] :
    L.WEqualsLocallyBijective (Type (max u₁ v₁ w)) := by
  let T := Type (max u₁ v₁ w)
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallyInjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallyInjective L (L.toSheafify (P ⋙ forget T)) :=
      sectionFiberConcreteToSheafify_isLocallyInjective_type
        (L := L) (P := P ⋙ forget T)
    -- Compare the concrete plus-plus unit with the abstract sheafification unit.
    rw [← Presheaf.isLocallyInjective_forget_iff, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  let _ :
      ∀ P : Eᵒᵖ ⥤ T,
        Presheaf.IsLocallySurjective L (toSheafify L P) := by
    intro P
    let _ : Presheaf.IsLocallySurjective L (L.toSheafify (P ⋙ forget T)) :=
      sectionFiberConcreteToSheafify_isLocallySurjective_type
        (L := L) (P := P ⋙ forget T)
    -- Compare the concrete plus-plus unit with the abstract sheafification unit.
    rw [Presheaf.isLocallySurjective_iff_whisker_forget, ← sheafComposeIso_hom_fac,
      ← toSheafify_plusPlusIsoSheafify_hom]
    let _ : IsIso ((plusPlusIsoSheafify L T (P ⋙ forget T)).hom) := by
      infer_instance
    let _ : IsIso ((sheafifyComposeIso L (forget T) P).hom) := by
      infer_instance
    infer_instance
  exact GrothendieckTopology.WEqualsLocallyBijective.mk' (J := L) (A := T)

/-- Helper for Lemma 7.28.1: the sheafification comparison for a continuous functor in an
enlarged type universe. -/
theorem GrothendieckTopology.continuous_pullback_sheafification_comparison_isIso_ulift
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [u.IsContinuous J K]
    (G : Cᵒᵖ ⥤ Type (max w u₁ u₂ v₁ v₂)) :
    IsIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify G))) := by
  let A := Type (max w u₁ u₂ v₁ v₂)
  let f := (u.op.lan).map (J.toSheafify G)
  -- The sheafification unit lies in `J.W`; continuity transports it across the left Kan
  -- extension along `u.op`.
  have hJG : J.W (J.toSheafify G) := by
    refine (J.W.cancel_right_of_respectsIso (J.toSheafify G) (plusPlusIsoSheafify J A G).hom).1 ?_
    simpa [toSheafify_plusPlusIsoSheafify_hom J A G] using
      (J.W_toSheafify G : J.W (CategoryTheory.toSheafify J G))
  have hGeneric : IsIso ((presheafToSheaf K A).map f) := (K.W_iff _).1 <|
    u.W_map_of_adjunction_of_isContinuous J K (u.op.lan)
      (u.op.lanAdjunction A) (J.toSheafify G) hJG
  let e₁ := plusPlusIsoSheafify K A ((u.op.lan).obj G)
  let e₂ := plusPlusIsoSheafify K A ((u.op.lan).obj (J.sheafify G))
  have hConcreteToGeneric :
      K.sheafifyMap f ≫ e₂.hom = e₁.hom ≫ CategoryTheory.sheafifyMap K f := by
    simpa [A, f, GrothendieckTopology.sheafification, CategoryTheory.sheafification] using
      (plusPlusFunctorIsoSheafification K A).hom.naturality f
  have hEq :
      K.sheafifyMap f = e₁.hom ≫ CategoryTheory.sheafifyMap K f ≫ e₂.inv := by
    calc
      K.sheafifyMap f = (K.sheafifyMap f ≫ e₂.hom) ≫ e₂.inv := by
        simp [Category.assoc]
      _ = e₁.hom ≫ CategoryTheory.sheafifyMap K f ≫ e₂.inv := by
        simpa [Category.assoc] using congrArg (fun k ↦ k ≫ e₂.inv) hConcreteToGeneric
  rw [hEq]
  let eGeneric :
      (presheafToSheaf K A).obj ((u.op.lan).obj G) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify G)) :=
    asIso ((presheafToSheaf K A).map f)
  have : IsIso (CategoryTheory.sheafifyMap K f) := by
    have hIsoPresheaf : IsIso ((sheafToPresheaf K A).map eGeneric.hom) := by
      infer_instance
    simpa [A, f, CategoryTheory.sheafifyMap] using hIsoPresheaf
  infer_instance

/-- Helper for Lemma 7.28.1: the sheafified-representable pullback comparison in an enlarged
type universe. -/
noncomputable def GrothendieckTopology.continuous_uliftSheafifiedRepresentable_iso
    (u : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasWeakSheafify J (Type (max w u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max w u₁ u₂ v₁ v₂))]
    [Functor.IsContinuous u J K]
    [∀ P : Cᵒᵖ ⥤ Type (max w u₁ u₂ v₁ v₂), u.op.HasLeftKanExtension P]
    (U : C) :
    GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁ w, u₂, v₂} K (u.obj U) ≅
      (u.sheafPullback (Type (max w u₁ u₂ v₁ v₂)) J K).obj
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max w u₂ v₂, u₁, v₁} J U) :=
  let A := Type (max w u₁ u₂ v₁ v₂)
  let P : Cᵒᵖ ⥤ A := CategoryTheory.uliftYoneda.{max (max w u₁ u₂ v₁ v₂) v₂, v₁, u₁}.obj U
  let e₁ :
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁ w, u₂, v₂} K (u.obj U) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj P) :=
    Functor.mapIso (presheafToSheaf K A)
      ((compULiftYonedaIsoULiftYonedaCompLan.{max w u₁ u₂ v₁ v₂} u).app U)
  let _ : IsIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify P))) :=
    GrothendieckTopology.continuous_pullback_sheafification_comparison_isIso_ulift
      u J K P
  let e₂Presheaf :
      (sheafToPresheaf K A).obj ((presheafToSheaf K A).obj ((u.op.lan).obj P)) ≅
        (sheafToPresheaf K A).obj
          ((presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P))) :=
    (plusPlusIsoSheafify K A ((u.op.lan).obj P)).symm ≪≫
      asIso (K.sheafifyMap ((u.op.lan).map (J.toSheafify P))) ≪≫
        plusPlusIsoSheafify K A ((u.op.lan).obj (J.sheafify P))
  let e₂ :
      (presheafToSheaf K A).obj ((u.op.lan).obj P) ≅
        (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P)) :=
    (fullyFaithfulSheafToPresheaf K A).preimageIso e₂Presheaf
  let e₃ :
      (presheafToSheaf K A).obj ((u.op.lan).obj (J.sheafify P)) ≅
        (sheafPullback u A J K).obj
          (GrothendieckTopology.uliftSheafifiedRepresentable.{max w u₂ v₂, u₁, v₁} J U) :=
    Functor.mapIso (presheafToSheaf K A)
      (Functor.mapIso (u.op.lan) (plusPlusIsoSheafify J A P))
  e₁ ≪≫ e₂ ≪≫ e₃ ≪≫
    (sheafPullbackIso u (Type (max w u₁ u₂ v₁ v₂)) J K).symm.app
      (GrothendieckTopology.uliftSheafifiedRepresentable.{max w u₂ v₂, u₁, v₁} J U)

/-- Helper for Lemma 7.28.1: the identity representable in a localized site is terminal in the
enlarged type universe. -/
noncomputable def localizedIdentityRepresentableIsoTerminal
    (_J : GrothendieckTopology C) (U : C) :
    ((CategoryTheory.uliftYoneda.{max u₁ v₁ w}.obj (Over.mk (𝟙 U))) :
      (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ w)) ≅
        (Functor.const (Over U)ᵒᵖ).obj (PUnit : Type (max u₁ v₁ w)) :=
  let yonedaOver : Over U ⥤ (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ w) :=
    CategoryTheory.uliftYoneda.{max u₁ v₁ w}
  let hRep :
      IsTerminal
        ((yonedaOver.obj (Over.mk (𝟙 U))) :
          (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ w)) :=
    IsTerminal.isTerminalObj yonedaOver (Over.mk (𝟙 U)) Over.mkIdTerminal
  IsTerminal.uniqueUpToIso hRep <|
    Functor.isTerminalConst (Over U)ᵒᵖ Types.isTerminalPUnit

/-- Helper for Lemma 7.28.1: the sheafified representable of the identity arrow is the terminal
sheaf on the localized site in the enlarged universe. -/
noncomputable def localizedIdentitySheafifiedRepresentableIsoTerminal
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify (J.over U) (Type (max u₁ v₁ w))] :
    GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
        (J.over U) (Over.mk (𝟙 U)) ≅
      Sheaf.terminal (J.over U) Types.isTerminalPUnit :=
  Functor.mapIso (presheafToSheaf (J.over U) (Type (max u₁ v₁ w)))
    (localizedIdentityRepresentableIsoTerminal.{u₁, v₁, w} J U) ≪≫
      (sheafificationIso (Sheaf.terminal (J.over U) Types.isTerminalPUnit)).symm

/-- Helper for Lemma 7.28.1: the identity-arrow sheafified representable is terminal on the
localized site in the enlarged universe. -/
noncomputable instance localizedIdentitySheafifiedRepresentableIsTerminal
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify (J.over U) (Type (max u₁ v₁ w))] :
    IsTerminal
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, max u₁ v₁, v₁}
        (J.over U) (Over.mk (𝟙 U))) :=
  IsTerminal.ofIso
    (Sheaf.isTerminalTerminal (J.over U) Types.isTerminalPUnit)
    (localizedIdentitySheafifiedRepresentableIsoTerminal.{u₁, v₁, w} J U).symm

/-- Helper for Lemma 7.28.1: the canonical identity section of an enlarged sheafified
representable. -/
noncomputable def GrothendieckTopology.uliftRepresentableIdentitySection
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))] :
    (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U).obj.obj (op U) :=
  J.uliftSheafifiedRepresentableHomEquiv
    (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U) U
    (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U))

/-- Helper for Lemma 7.28.1: evaluating a morphism out of the enlarged sheafified
representable on the named identity section recovers its sheafified-Yoneda section. -/
theorem GrothendieckTopology.uliftRepresentableIdentitySection_app
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    {ℱ : Sheaf J (Type (max u₁ v₁ w))}
    (α : GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U ⟶ ℱ) :
    α.hom.app (op U)
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) =
      J.uliftSheafifiedRepresentableHomEquiv ℱ U α := by
  -- Apply functoriality of the sheafified-Yoneda equivalence to the identity morphism.
  simpa [GrothendieckTopology.uliftRepresentableIdentitySection] using
    (J.uliftSheafifiedRepresentableHomEquiv_comp
      (α := 𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U))
      (β := α)).symm

/-- Helper for Lemma 7.28.1: restricting the named identity section along an object of the slice
site is the sheafified-Yoneda image of the underlying arrow. -/
theorem GrothendieckTopology.uliftRepresentableIdentitySection_restrict
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (X : Over U) :
    (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U).obj.map X.hom.op
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) =
      J.uliftSheafifiedRepresentableHomEquiv
        (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U) X.left
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{w, u₁, v₁} J).map X.hom ≫
          𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U)) := by
  -- Naturality in the representing object turns restriction of the identity section into the
  -- canonical section represented by the slice arrow.
  simpa [GrothendieckTopology.uliftRepresentableIdentitySection] using
    (J.uliftSheafifiedRepresentableHomEquiv_naturality X.hom
      (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U)
      (𝟙 (GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U))).symm

/-- Helper for Lemma 7.28.1: sheafifying the raw identity section gives the named identity
section of the enlarged sheafified representable. -/
theorem uliftRepresentableIdentitySection_toSheafify
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))] (X : Over U) :
    (CategoryTheory.toSheafify J (uliftRepresentablePresheaf.{u₁, v₁, w} U)).app (op X.left)
        (ULift.up X.hom) =
      (J.uliftSheafifiedRepresentable U).obj.map X.hom.op
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) := by
  -- First identify the sheafification of the identity arrow with the named identity section.
  have hid :
      (CategoryTheory.toSheafify J (uliftRepresentablePresheaf.{u₁, v₁, w} U)).app (op U)
          (ULift.up (𝟙 U)) =
        GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U := by
    let A := Type (max u₁ v₁ w)
    let P : Cᵒᵖ ⥤ A := uliftRepresentablePresheaf.{u₁, v₁, w} U
    have h : CategoryTheory.toSheafify J P =
        ((sheafificationAdjunction J A).homEquiv P ((presheafToSheaf J A).obj P)) (𝟙 _) := by
      exact (Adjunction.homEquiv_id (sheafificationAdjunction J A) P).symm
    have happ := congrFun (NatTrans.congr_app h (op U)) (ULift.up (𝟙 U))
    simpa [GrothendieckTopology.uliftRepresentableIdentitySection,
      GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv,
      GrothendieckTopology.uliftSheafifiedRepresentable,
      uliftRepresentablePresheaf, P, A] using happ
  have hnat := congrFun
    ((CategoryTheory.toSheafify J (uliftRepresentablePresheaf.{u₁, v₁, w} U)).naturality X.hom.op)
    (ULift.up (𝟙 U))
  dsimp at hnat
  rw [← hid]
  simpa [uliftRepresentablePresheaf] using hnat

/-- Helper for Lemma 7.28.1: a raw fibre point maps to a section of the sheafified fibre over the
named identity section. -/
noncomputable def rawFiberToSheafifiedSectionFiber
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (P : Over (uliftRepresentablePresheaf.{u₁, v₁, w} U)) :
    (uliftFiberPresheafOverRepresentable.{u₁, v₁, w} U).obj P ⟶
      sectionFiberPresheaf ((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom)
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) where
  app X s :=
    ⟨(CategoryTheory.toSheafify J P.left).app (op X.unop.left) s.1, by
      change (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app (op X.unop.left)
          ((CategoryTheory.toSheafify J P.left).app (op X.unop.left) s.1) =
        (J.uliftSheafifiedRepresentable U).obj.map X.unop.hom.op
          (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U)
      have hnat := congrFun
        (NatTrans.congr_app (CategoryTheory.toSheafify_naturality (J := J) P.hom)
          (op X.unop.left)) s.1
      dsimp at hnat
      have hnat' : (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
          (op X.unop.left)
          ((CategoryTheory.toSheafify J P.left).app (op X.unop.left) s.1) =
        (CategoryTheory.toSheafify J (uliftRepresentablePresheaf.{u₁, v₁, w} U)).app
          (op X.unop.left) (P.hom.app (op X.unop.left) s.1) := by
        simpa using hnat.symm
      refine hnat'.trans ?_
      have hbase : P.hom.app (op X.unop.left) s.1 = ULift.up X.unop.hom := by
        apply ULift.ext
        exact s.2
      rw [hbase]
      exact uliftRepresentableIdentitySection_toSheafify (J := J) (U := U) X.unop⟩
  naturality X Y f := by
    funext s
    apply Subtype.ext
    have hnat := congrFun ((CategoryTheory.toSheafify J P.left).naturality f.unop.left.op) s.1
    dsimp at hnat
    exact hnat

/-- Helper for Lemma 7.28.1: local injectivity of sheafification restricts to the raw
identity-section fibre comparison. -/
theorem rawFiberToSheafifiedSectionFiber_locallyInjective
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (P : Over (uliftRepresentablePresheaf.{u₁, v₁, w} U))
    [Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P.left)] :
    Presheaf.IsLocallyInjective (J.over U)
      (rawFiberToSheafifiedSectionFiber.{u₁, v₁, w} J U P) := by
  constructor
  intro X x y hxy
  cases X using Opposite.rec
  rename_i X
  have hleft :
      (CategoryTheory.toSheafify J P.left).app (op X.left) x.1 =
        (CategoryTheory.toSheafify J P.left).app (op X.left) y.1 := by
    exact congrArg Subtype.val hxy
  have hbase :
      Presheaf.equalizerSieve (F := P.left) (X := op X.left) x.1 y.1 ∈ J X.left := by
    exact Presheaf.equalizerSieve_mem J (CategoryTheory.toSheafify J P.left) x.1 y.1 hleft
  refine (J.over U).superset_covering ?_
    (J.overEquiv_symm_mem_over X
      (Presheaf.equalizerSieve (F := P.left) (X := op X.left) x.1 y.1) hbase)
  intro Y f hf
  apply Subtype.ext
  simpa [rawFiberToSheafifiedSectionFiber, uliftFiberPresheafOverRepresentable,
    uliftFiberPresheafOverRepresentable_map] using hf

/-- Helper for Lemma 7.28.1: local surjectivity of sheafification restricts to the raw
identity-section fibre comparison. -/
theorem rawFiberToSheafifiedSectionFiber_locallySurjective
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (P : Over (uliftRepresentablePresheaf.{u₁, v₁, w} U))
    [Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P.left)]
    [Presheaf.IsLocallyInjective J
      (CategoryTheory.toSheafify J (uliftRepresentablePresheaf.{u₁, v₁, w} U))] :
    Presheaf.IsLocallySurjective (J.over U)
      (rawFiberToSheafifiedSectionFiber.{u₁, v₁, w} J U P) := by
  constructor
  intro X z
  let ηP := CategoryTheory.toSheafify J P.left
  let ηU := CategoryTheory.toSheafify J (uliftRepresentablePresheaf.{u₁, v₁, w} U)
  let q := rawFiberToSheafifiedSectionFiber.{u₁, v₁, w} J U P
  let S : Sieve X.left := Presheaf.imageSieve ηP z.1
  let Sover : Sieve X := (Sieve.overEquiv X).symm S
  have hS : S ∈ J X.left := Presheaf.imageSieve_mem J ηP z.1
  have hSover : Sover ∈ (J.over U) X :=
    J.overEquiv_symm_mem_over X S hS
  let T : ∀ ⦃Y : Over U⦄ (f : Y ⟶ X), Sover f → Sieve Y := by
    intro Y f hf
    let t := Presheaf.localPreimage ηP z.1 f.left (by simpa [Sover, S] using hf)
    let a : (uliftRepresentablePresheaf.{u₁, v₁, w} U).obj (op Y.left) :=
      P.hom.app (op Y.left) t
    let b : (uliftRepresentablePresheaf.{u₁, v₁, w} U).obj (op Y.left) :=
      ULift.up Y.hom
    exact (Sieve.overEquiv Y).symm (Presheaf.equalizerSieve (F :=
      uliftRepresentablePresheaf.{u₁, v₁, w} U) a b)
  refine (J.over U).superset_covering ?_ ((J.over U).transitive hSover (Sieve.bind Sover.1 T) ?_)
  · rintro Z h ⟨Y, f, g, hg, hf, rfl⟩
    let hgbase : S g.left := by simpa [Sover, S] using hg
    let t := Presheaf.localPreimage ηP z.1 g.left hgbase
    let t' : P.left.obj (op Z.left) := P.left.map f.left.op t
    have hfiber : (P.hom.app (op Z.left) t').down = Z.hom := by
      let a : (uliftRepresentablePresheaf.{u₁, v₁, w} U).obj (op Y.left) :=
        P.hom.app (op Y.left) t
      let b : (uliftRepresentablePresheaf.{u₁, v₁, w} U).obj (op Y.left) :=
        ULift.up Y.hom
      have heqbase :
          Presheaf.equalizerSieve (F := uliftRepresentablePresheaf.{u₁, v₁, w} U)
            (X := op Y.left) a b f.left := by
        simpa [T, Sover, S, hgbase, t] using hf
      have hnat := congrFun (P.hom.naturality f.left.op) t
      dsimp at hnat
      have hdown : (P.hom.app (op Z.left) t').down = f.left ≫ a.down := by
        simpa [t', a, uliftRepresentablePresheaf] using congrArg ULift.down hnat
      have heqdown : f.left ≫ a.down = f.left ≫ b.down := by
        have hmap :
            ((uliftRepresentablePresheaf.{u₁, v₁, w} U).map f.left.op a).down =
              ((uliftRepresentablePresheaf.{u₁, v₁, w} U).map f.left.op b).down :=
          congrArg ULift.down heqbase
        simpa [uliftRepresentablePresheaf] using hmap
      exact hdown.trans <| heqdown.trans <| by
        simpa [b] using Over.w f
    refine ⟨⟨t', hfiber⟩, ?_⟩
    apply Subtype.ext
    have hlocal := Presheaf.app_localPreimage ηP z.1 g.left hgbase
    have hnat := congrFun (ηP.naturality f.left.op) t
    dsimp at hnat
    calc
      ((rawFiberToSheafifiedSectionFiber.{u₁, v₁, w} J U P).app (op Z) ⟨t', hfiber⟩).1 =
          ηP.app (op Z.left) (P.left.map f.left.op t) := by
            rfl
      _ = ((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map f.left.op
            (ηP.app (op Y.left) t) := by
            exact hnat
      _ = ((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map f.left.op
            (((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map g.left.op z.1) := by
            exact congrArg
              (fun s ↦ ((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map
                f.left.op s) hlocal
      _ = ((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map
            ((f.left ≫ g.left).op) z.1 := by
            simpa [FunctorToTypes.map_comp_apply, op_comp] using
              ((FunctorToTypes.map_comp_apply
                ((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj
                g.left.op f.left.op z.1).symm)
  · intro Y f hf
    let hfbase : S f.left := by simpa [Sover, S] using hf
    let t := Presheaf.localPreimage ηP z.1 f.left hfbase
    let a : (uliftRepresentablePresheaf.{u₁, v₁, w} U).obj (op Y.left) :=
      P.hom.app (op Y.left) t
    let b : (uliftRepresentablePresheaf.{u₁, v₁, w} U).obj (op Y.left) :=
      ULift.up Y.hom
    have hEq : ηU.app (op Y.left) a = ηU.app (op Y.left) b := by
      have hlocal := Presheaf.app_localPreimage ηP z.1 f.left hfbase
      have hnat := congrFun
        (NatTrans.congr_app (CategoryTheory.toSheafify_naturality (J := J) P.hom)
          (op Y.left)) t
      dsimp at hnat
      have hz :
          (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
              (op X.left) z.1 =
            (J.uliftSheafifiedRepresentable U).obj.map X.hom.op
              (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) := z.2
      have hleft :
          ηU.app (op Y.left) a =
            (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
              (op Y.left) (((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map
                f.left.op z.1) := by
        calc
          ηU.app (op Y.left) a =
              (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
                (op Y.left) (ηP.app (op Y.left) t) := by
                simpa [ηU, a, ηP] using hnat
          _ = (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
                (op Y.left) (((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map
                  f.left.op z.1) := by
                exact congrArg
                  (fun s ↦ (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
                    (op Y.left) s) hlocal
      have hright :
          (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
              (op Y.left) (((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map
                f.left.op z.1) =
            (J.uliftSheafifiedRepresentable U).obj.map Y.hom.op
              (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) := by
        have hnatπ := congrFun
          ((((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).naturality f.left.op)
          z.1
        dsimp at hnatπ
        have hπ :
            (((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
                (op Y.left) (((presheafToSheaf J (Type (max u₁ v₁ w))).obj P.left).obj.map
                  f.left.op z.1) =
              (J.uliftSheafifiedRepresentable U).obj.map f.left.op
                ((((presheafToSheaf J (Type (max u₁ v₁ w))).map P.hom).hom).app
                  (op X.left) z.1) := hnatπ
        have htarget :
            (J.uliftSheafifiedRepresentable U).obj.map f.left.op
                ((J.uliftSheafifiedRepresentable U).obj.map X.hom.op
                  (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U)) =
              (J.uliftSheafifiedRepresentable U).obj.map Y.hom.op
                (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) := by
          have hcomp : X.hom.op ≫ f.left.op = Y.hom.op := by
            simpa only [op_comp] using congrArg Quiver.Hom.op (Over.w f)
          rw [← hcomp]
          exact (FunctorToTypes.map_comp_apply
            (J.uliftSheafifiedRepresentable U).obj X.hom.op f.left.op
            (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U)).symm
        exact hπ.trans <| (congrArg
          (fun s ↦ (J.uliftSheafifiedRepresentable U).obj.map f.left.op s) hz).trans htarget
      exact hleft.trans <| hright.trans
        (uliftRepresentableIdentitySection_toSheafify (J := J) (U := U) Y).symm
    apply (J.over U).superset_covering
      (Sieve.le_pullback_bind Sover.1 T f hf)
    exact J.overEquiv_symm_mem_over Y
      (Presheaf.equalizerSieve (F := uliftRepresentablePresheaf.{u₁, v₁, w} U) a b)
      (Presheaf.equalizerSieve_mem J ηU a b hEq)

/-- Helper for Lemma 7.28.1: composing a sheaf morphism with an isomorphism on the source
identifies the corresponding section-fibre presheaves. -/
noncomputable def sectionFiberPresheafIsoOfCompSource
    {J : GrothendieckTopology C}
    {E E' B : Sheaf J (Type (max u₁ v₁ w))}
    (e : E ≅ E') (π' : E' ⟶ B) {U : C}
    (b : B.obj.obj (op U)) :
    sectionFiberPresheaf (e.hom ≫ π') b ≅ sectionFiberPresheaf π' b := by
  refine NatIso.ofComponents (fun X ↦ ?_) ?_
  · refine
      { hom := fun s ↦ ⟨e.hom.hom.app (op X.unop.left) s.1, s.2⟩
        inv := fun t ↦ ⟨e.inv.hom.app (op X.unop.left) t.1, ?_⟩
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · have hcancel :
          e.hom.hom.app (op X.unop.left) (e.inv.hom.app (op X.unop.left) t.1) = t.1 := by
        have h := congrArg (fun α ↦ α.hom.app (op X.unop.left) t.1) e.inv_hom_id
        exact h
      exact (congrArg (fun s ↦ π'.hom.app (op X.unop.left) s) hcancel).trans t.2
    · funext s
      apply Subtype.ext
      have h := congrArg (fun α ↦ α.hom.app (op X.unop.left) s.1) e.hom_inv_id
      exact h
    · funext t
      apply Subtype.ext
      have h := congrArg (fun α ↦ α.hom.app (op X.unop.left) t.1) e.inv_hom_id
      exact h
  · intro X Y f
    ext s
    apply Subtype.ext
    -- Naturality of the source isomorphism gives compatibility with slice restrictions.
    simpa [sectionFiberPresheaf, sectionFiberSubfunctor] using
      congrFun (e.hom.hom.naturality f.unop.left.op) s.1

/-- Helper for Lemma 7.28.1: the sheafified raw identity-section fibre of the localization
object is the original slice-site sheaf. -/
noncomputable def sheafifiedRawLocalizationSectionFiberIso
    (J : GrothendieckTopology C) (U : C)
    [HasWeakSheafify (J.over U) (Type (max u₁ v₁ w))]
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (𝒢 : Sheaf (J.over U) (Type (max u₁ v₁ w))) :
    sectionFiberPresheaf
        ((presheafToSheaf J (Type (max u₁ v₁ w))).map
          (uliftLocalizationOverRepresentable (U := U) 𝒢.obj).hom)
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) ≅
      𝒢.obj := by
  let A := Type (max u₁ v₁ w)
  let P := uliftLocalizationOverRepresentable (U := U) 𝒢.obj
  let q := rawFiberToSheafifiedSectionFiber.{u₁, v₁, w} J U P
  have hqIso : IsIso ((presheafToSheaf (J.over U) A).map q) := by
    let _ : J.WEqualsLocallyBijective A :=
      sectionFiberLargeType_WEqualsLocallyBijective (L := J)
    let _ : (J.over U).WEqualsLocallyBijective A :=
      sectionFiberLargeType_WEqualsLocallyBijective (L := J.over U)
    let _ : Presheaf.IsLocallyInjective (J.over U) q :=
      rawFiberToSheafifiedSectionFiber_locallyInjective (J := J) (U := U) P
    let _ : Presheaf.IsLocallySurjective (J.over U) q :=
      rawFiberToSheafifiedSectionFiber_locallySurjective (J := J) (U := U) P
    exact ((J.over U).W_iff q).1 <|
      GrothendieckTopology.W_of_isLocallyBijective (J := J.over U) (f := q)
  let qIso := asIso ((presheafToSheaf (J.over U) A).map q)
  let sectionSheaf :=
    sectionFiberSheaf
      ((presheafToSheaf J A).map
        (uliftLocalizationOverRepresentable (U := U) 𝒢.obj).hom)
      (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U)
  let rawIso := uliftLocalizationOverRepresentable_fiberIso (U := U) 𝒢.obj
  -- Sheafify the raw fibre comparison, then use that both the section fibre and `𝒢` are sheaves.
  exact (sheafToPresheaf (J.over U) A).mapIso
    (sheafificationIso sectionSheaf ≪≫ qIso.symm ≪≫
      Functor.mapIso (presheafToSheaf (J.over U) A) rawIso ≪≫
        ((sheafificationNatIso (J.over U) A).app 𝒢).symm)

/-- Helper for Lemma 7.28.1: the enlarged representable-localization structure morphism
`j_{U!} 𝒢 ⟶ h_U^#`. -/
noncomputable def GrothendieckTopology.uliftRepresentableLocalizationHom
    (J : GrothendieckTopology C) (U : C)
    [∀ F : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ w), (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type (max u₁ v₁ w))]
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (𝒢 : Sheaf (J.over U) (Type (max u₁ v₁ w))) :
    ((Over.forget U).sheafPullback (Type (max u₁ v₁ w)) (J.over U) J).obj 𝒢 ⟶
      GrothendieckTopology.uliftSheafifiedRepresentable.{w, u₁, v₁} J U :=
  let A := Type (max u₁ v₁ w)
  let L := (Over.forget U).sheafPullback A (J.over U) J
  let F := presheafToSheaf J A
  let e𝒢 := (sheafificationNatIso (J.over U) A).app 𝒢
  let eleft : L.obj 𝒢 ≅ F.obj ((Over.forget U).op.lan.obj 𝒢.obj) :=
    Functor.mapIso L e𝒢 ≪≫
      localization_lowerShriek_associatedSheafIso J U 𝒢.obj
  eleft.hom ≫ F.map (uliftLocalizationOverRepresentable (U := U) 𝒢.obj).hom

/-- Helper for Lemma 7.28.1: the presheaf-level identity-section fibre of the enlarged
localization morphism is the original localized presheaf. -/
noncomputable def GrothendieckTopology.uliftRepresentableLocalizationHom_sectionFiberPresheafIso
    (J : GrothendieckTopology C) (U : C)
    [∀ F : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ w), (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type (max u₁ v₁ w))]
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (𝒢 : Sheaf (J.over U) (Type (max u₁ v₁ w))) :
    sectionFiberPresheaf
        (GrothendieckTopology.uliftRepresentableLocalizationHom.{u₁, v₁, w} J U 𝒢)
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) ≅
      𝒢.obj :=
  let A := Type (max u₁ v₁ w)
  let L := (Over.forget U).sheafPullback A (J.over U) J
  let F := presheafToSheaf J A
  let e𝒢 := (sheafificationNatIso (J.over U) A).app 𝒢
  let eleft : L.obj 𝒢 ≅ F.obj ((Over.forget U).op.lan.obj 𝒢.obj) :=
    Functor.mapIso L e𝒢 ≪≫
      localization_lowerShriek_associatedSheafIso J U 𝒢.obj
  sectionFiberPresheafIsoOfCompSource eleft
    (F.map (uliftLocalizationOverRepresentable (U := U) 𝒢.obj).hom)
    (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) ≪≫
      sheafifiedRawLocalizationSectionFiberIso.{u₁, v₁, w} J U 𝒢

/-- Helper for Lemma 7.28.1: the identity-section fibre of the enlarged localization morphism is
the original localized sheaf. -/
noncomputable def GrothendieckTopology.uliftRepresentableLocalizationHom_sectionFiberSheafIso
    (J : GrothendieckTopology C) (U : C)
    [∀ F : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁ w), (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type (max u₁ v₁ w))]
    [HasWeakSheafify J (Type (max u₁ v₁ w))]
    (𝒢 : Sheaf (J.over U) (Type (max u₁ v₁ w))) :
    sectionFiberSheaf
        (GrothendieckTopology.uliftRepresentableLocalizationHom.{u₁, v₁, w} J U 𝒢)
        (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, w} J U) ≅
      𝒢 :=
  -- The sheaf-level bridge is formal once the underlying presheaf fibre computation is available.
  (fullyFaithfulSheafToPresheaf (J.over U) (Type (max u₁ v₁ w))).preimageIso
    (GrothendieckTopology.uliftRepresentableLocalizationHom_sectionFiberPresheafIso.{u₁, v₁, w}
      J U 𝒢)

/-- Helper for Lemma 7.28.1: after precomposing with `Over.post u`, the section-fibre bridge
identifies the enlarged localization fibre with the target slice sheaf. -/
noncomputable def overPost_uliftRepresentableLocalization_sectionFiberIso
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    (ℋ : Sheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))) :
    (Over.post u).op ⋙
        sectionFiberPresheaf
          (GrothendieckTopology.uliftRepresentableLocalizationHom.{u₁, v₁, max u₂ v₂}
            JC (u.obj V) ℋ)
          (GrothendieckTopology.uliftRepresentableIdentitySection.{u₁, v₁, max u₂ v₂}
            JC (u.obj V)) ≅
      (Over.post u).op ⋙ ℋ.obj :=
  Functor.isoWhiskerLeft (Over.post u).op
    ((sheafToPresheaf (JC.over (u.obj V)) (Type (max u₁ u₂ v₁ v₂))).mapIso
      (GrothendieckTopology.uliftRepresentableLocalizationHom_sectionFiberSheafIso.{u₁, v₁, max u₂ v₂}
        JC (u.obj V) ℋ))

/-- Helper for Lemma 7.28.1: taking the section fibre of a pushed-forward morphism is the same
as precomposing the original section-fibre presheaf with the induced slice functor. -/
noncomputable def sectionFiberPresheaf_sheafPushforwardContinuous_iso
    (u : D ⥤ C) [u.IsContinuous JD JC] (V : D)
    {E B : Sheaf JC (Type w)} (π : E ⟶ B)
    (b : B.obj.obj (op (u.obj V))) :
    sectionFiberPresheaf
        ((u.sheafPushforwardContinuous (Type w) JD JC).map π) b ≅
      (Over.post u).op ⋙ sectionFiberPresheaf π b :=
  Iso.refl _

end

end CategoryTheory
