module

public import stacks_project.Chap06.Lemma_6_33_3_Part10_RealizationAux

@[expose] public section

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
open CategoryTheory CategoryTheory.Limits Opposite TopCat TopologicalSpace Topology
open CategoryTheory.Presheaf TopologicalSpace.Opens
attribute [local instance] CategoryTheory.Types.instFunLike CategoryTheory.Types.instConcreteCategory
noncomputable section
universe w u

namespace Part10CompBridge

-- ============ PROVEN HELPER 1: module pullbackComp.inv = leftAdjointUniq.hom ============
namespace ModRouteHelpers
open SheafOfModules
variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  [(pushforward.{w} φ).IsRightAdjoint]
  {D' : Type u} [Category.{w} D'] {K' : GrothendieckTopology D'}
  {G : D ⥤ D'} {R' : CategoryTheory.Sheaf K' RingCat.{w}}
  [Functor.IsContinuous G K K'] [Functor.IsContinuous (F ⋙ G) J K']
  (ψ : R ⟶ (G.sheafPushforwardContinuous RingCat.{w} K K').obj R')
  [(pushforward.{w} ψ).IsRightAdjoint]

theorem pullbackComp_inv_eq_leftAdjointUniq :
    (pullbackComp.{w} φ ψ).inv =
      (Adjunction.leftAdjointUniq
        (pullbackPushforwardAdjunction.{w} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map ψ))
        ((pullbackPushforwardAdjunction.{w} φ).comp (pullbackPushforwardAdjunction.{w} ψ))).hom := by
  set adjComp := (pullbackPushforwardAdjunction.{w} φ).comp (pullbackPushforwardAdjunction.{w} ψ) with hAC
  set adjDirect := pullbackPushforwardAdjunction.{w} (F := F ⋙ G)
          (φ ≫ (F.sheafPushforwardContinuous RingCat.{w} J K).map ψ) with hAD
  have key : CategoryTheory.conjugateEquiv adjComp adjDirect (pullbackComp.{w} φ ψ).inv = 𝟙 _ := by
    rw [hAC, hAD, SheafOfModules.conjugateEquiv_pullbackComp_inv]; rfl
  have h2 : (pullbackComp.{w} φ ψ).inv =
      (CategoryTheory.conjugateEquiv adjComp adjDirect).symm (𝟙 _) := by
    rw [← key]; exact ((CategoryTheory.conjugateEquiv adjComp adjDirect).symm_apply_apply _).symm
  rw [h2, Adjunction.leftAdjointUniq]
  simp only [Iso.symm_hom, conjugateIsoEquiv_symm_apply_inv, Iso.refl_inv]
  rfl

omit [(pushforward.{w} φ).IsRightAdjoint] in
theorem toSheaf_unit_leftAdjointUniq
    {L1 L2 : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R}
    (adj1 : L1 ⊣ SheafOfModules.pushforward φ) (adj2 : L2 ⊣ SheafOfModules.pushforward φ)
    (M : SheafOfModules.{w} S) :
    (SheafOfModules.toSheaf S).map (adj1.unit.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        ((SheafOfModules.toSheaf R).map ((Adjunction.leftAdjointUniq adj1 adj2).hom.app M)) =
      (SheafOfModules.toSheaf S).map (adj2.unit.app M) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj1 adj2 M
  have h2 := congrArg (SheafOfModules.toSheaf S).map h
  rw [Functor.map_comp] at h2
  exact h2

end ModRouteHelpers

section StrictComm
open SheafOfModules
def toSheafPushforwardIso {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [Functor.IsContinuous F J K]
    (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R) :
    SheafOfModules.pushforward φ ⋙ SheafOfModules.toSheaf S ≅
      SheafOfModules.toSheaf R ⋙ F.sheafPushforwardContinuous AddCommGrpCat.{w} J K :=
  NatIso.ofComponents
    (fun M => eqToIso (by apply ObjectProperty.FullSubcategory.ext; rfl))
    (fun {M N} f => by
      apply (sheafToPresheaf J AddCommGrpCat.{w}).map_injective
      simp only [Functor.comp_map, Functor.map_comp]
      rfl)
end StrictComm

section CongrIso
open SheafOfModules
theorem moduleSheafPullbackCongrIso_inv_val_app
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat} {R : Sheaf K RingCat} [Functor.IsContinuous F J K]
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat J K).obj R}
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(SheafOfModules.pushforward ψ).IsRightAdjoint]
    (hEq : φ = ψ) (M : SheafOfModules S) (V : Dᵒᵖ) :
    ((moduleSheafPullbackCongrIso hEq).inv.app M).val.app V =
      eqToHom (by cases hEq; rfl) := by
  cases hEq
  rfl
end CongrIso

-- template general lemmas (copied verbatim from OpenEmbeddingAux, renamed)
section TemplateLemmas

theorem leftAdjointUniq_comp_second_app'
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ : C₀ ⥤ C₁} {F₁₂ F₁₂' : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₁₂' : F₁₂' ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂')).hom.app X =
      (Adjunction.leftAdjointUniq adj₁₂ adj₁₂').hom.app (F₀₁.obj X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂'.obj (F₀₁.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁.comp adj₁₂')).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁ ⋙ F₁₂').obj X))
        ((adj₁₂.leftAdjointUniq adj₁₂').hom.app (F₀₁.obj X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁.comp adj₁₂') X]
  have h := Adjunction.unit_leftAdjointUniq_hom_app adj₁₂ adj₁₂' (F₀₁.obj X)
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp, Category.assoc] using
    congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h.symm

theorem leftAdjointUniq_comp_first_app'
    {C₀ C₁ C₂ : Type*} [Category C₀] [Category C₁] [Category C₂]
    {F₀₁ F₀₁' : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂}
    {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁}
    (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₀₁' : F₀₁' ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁)
    (X : C₀) :
    (Adjunction.leftAdjointUniq (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂)).hom.app X =
      F₁₂.map ((Adjunction.leftAdjointUniq adj₀₁ adj₀₁').hom.app X) := by
  apply ((adj₀₁.comp adj₁₂).homEquiv X (F₁₂.obj (F₀₁'.obj X))).injective
  change
    ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (((adj₀₁.comp adj₁₂).leftAdjointUniq (adj₀₁'.comp adj₁₂)).hom.app X) =
      ((adj₀₁.comp adj₁₂).homEquiv X ((F₀₁' ⋙ F₁₂).obj X))
        (F₁₂.map ((adj₀₁.leftAdjointUniq adj₀₁').hom.app X))
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app
    (adj₀₁.comp adj₁₂) (adj₀₁'.comp adj₁₂) X]
  let α := (adj₀₁.leftAdjointUniq adj₀₁').hom.app X
  have h₁ : adj₀₁.unit.app X ≫ G₁₀.map α = adj₀₁'.unit.app X := by
    simpa [α] using Adjunction.unit_leftAdjointUniq_hom_app adj₀₁ adj₀₁' X
  have h₂ :
      α ≫ adj₁₂.unit.app (F₀₁'.obj X) =
        adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α) := by
    simpa [α] using adj₁₂.unit.naturality α
  have hcalc :
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) =
        adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
          G₁₀.map (G₂₁.map (F₁₂.map α)) := by
    calc
      adj₀₁'.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))
          =
        (adj₀₁.unit.app X ≫ G₁₀.map α) ≫
          G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X)) := by
            simpa [Category.assoc] using
              congrArg (fun k ↦ k ≫ G₁₀.map (adj₁₂.unit.app (F₀₁'.obj X))) h₁.symm
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map (α ≫ adj₁₂.unit.app (F₀₁'.obj X)) := by
            simp [Functor.map_comp, Category.assoc]
      _ =
        adj₀₁.unit.app X ≫
          G₁₀.map
            (adj₁₂.unit.app (F₀₁.obj X) ≫ G₂₁.map (F₁₂.map α)) := by
            simpa using congrArg (fun k ↦ adj₀₁.unit.app X ≫ G₁₀.map k) h₂
      _ =
      adj₀₁.unit.app X ≫ G₁₀.map (adj₁₂.unit.app (F₀₁.obj X)) ≫
        G₁₀.map (G₂₁.map (F₁₂.map α)) := by
          simp [Functor.map_comp]
  simpa [Adjunction.homEquiv, Adjunction.comp_unit_app, Functor.map_comp,
    Category.assoc, α] using hcalc

end TemplateLemmas

-- ===== proven linchpin: clean uniqueness =====
theorem eq_leftAdjointUniq_hom_app
    {C D : Type*} [Category C] [Category D]
    {LA1 LA2 : C ⥤ D} {Gadd : D ⥤ C}
    (A1 : LA1 ⊣ Gadd) (A2 : LA2 ⊣ Gadd) (N : C)
    (k : LA1.obj N ⟶ LA2.obj N)
    (hk : A1.unit.app N ≫ Gadd.map k = A2.unit.app N) :
    k = (Adjunction.leftAdjointUniq A1 A2).hom.app N := by
  apply (A1.homEquiv N (LA2.obj N)).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app A1 A2 N]
  rw [Adjunction.homEquiv_unit]
  exact hk

-- ===== proven: toSheaf of module congrIso.inv is eqToHom =====
open SheafOfModules in
theorem toSheaf_map_congrIso_inv
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [Functor.IsContinuous F J K]
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R}
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(SheafOfModules.pushforward ψ).IsRightAdjoint]
    (hEq : φ = ψ) (M : SheafOfModules.{w} S) :
    (SheafOfModules.toSheaf R).map ((moduleSheafPullbackCongrIso hEq).inv.app M) =
      eqToHom (by cases hEq; rfl) := by
  cases hEq
  rw [eqToHom_refl]
  apply (sheafToPresheaf K AddCommGrpCat.{w}).map_injective
  apply NatTrans.ext
  funext V
  rfl

open SheafOfModules in
theorem toSheaf_map_congrIso_hom
    {C : Type*} [Category C] {D : Type*} [Category D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
    {S : Sheaf J RingCat.{w}} {R : Sheaf K RingCat.{w}} [Functor.IsContinuous F J K]
    {φ ψ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R}
    [(SheafOfModules.pushforward φ).IsRightAdjoint]
    [(SheafOfModules.pushforward ψ).IsRightAdjoint]
    (hEq : φ = ψ) (M : SheafOfModules.{w} S) :
    (SheafOfModules.toSheaf R).map ((moduleSheafPullbackCongrIso hEq).hom.app M) =
      eqToHom (by cases hEq; rfl) := by
  cases hEq
  rw [eqToHom_refl]
  apply (sheafToPresheaf K AddCommGrpCat.{w}).map_injective
  apply NatTrans.ext
  funext V
  rfl
section
variable {X : TopCat.{w}}

theorem A_inv_eq (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U)
    [hWcont : W.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology X)]
    [hUcont : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)]
    [hPLcont : (openSubsetHomOfLE_isOpenEmbedding h).functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology (openSubsetSpace U))]
    (G : TopCat.Sheaf AddCommGrpCat.{w} X) :
    (algebraicGlobalRestrictionCompIso (C := AddCommGrpCat.{w}) h).inv.app G =
      (Adjunction.leftAdjointUniq
        (W.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
          (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology X))
        ((U.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
            (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)).comp
          ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
            (Opens.grothendieckTopology (openSubsetSpace W))
            (Opens.grothendieckTopology (openSubsetSpace U))))).hom.app G := by
  -- set up adjunctions mirroring template hcomp
  let adjU := U.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{w})
    (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)
  let adjPL := (openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{w})
    (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology (openSubsetSpace U))
  let adjW := W.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{w})
    (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology X)
  let adjComp := adjU.comp adjPL
  -- rewrite inv as hom of swapped leftAdjointUniq, then prove hom-version.
  -- Goal: compIso.inv.app G = (leftAdjointUniq adjW adjComp).hom.app G.
  -- Prove the .hom version first: compIso.hom.app G = (leftAdjointUniq adjComp adjW).hom.app G.
  have hcomp :
      (algebraicGlobalRestrictionCompIso (C := AddCommGrpCat.{w}) h).hom.app G =
        (Adjunction.leftAdjointUniq adjComp adjW).hom.app G := by
    apply (adjComp.homEquiv G _).injective
    have hR : adjComp.homEquiv G _ ((Adjunction.leftAdjointUniq adjComp adjW).hom.app G) =
        adjW.unit.app G := Adjunction.homEquiv_leftAdjointUniq_hom_app adjComp adjW G
    refine Eq.trans ?_ hR.symm
    rw [Adjunction.homEquiv_unit]
    apply CategoryTheory.Sheaf.hom_ext
    refine NatTrans.ext (funext fun V => ?_)
    simp only [algebraicGlobalRestrictionCompIso, adjComp, adjU, adjPL, adjW,
      Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
      Topology.IsOpenEmbedding.sheafPullback,
      Functor.sheafPushforwardContinuousComp', Functor.sheafPushforwardContinuousComp,
      Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousNatTrans,
      Iso.trans_hom, Iso.refl_hom, NatTrans.id_app, NatTrans.comp_app,
      ObjectProperty.ι_map, ObjectProperty.FullSubcategory.comp_hom,
      Adjunction.sheafPushforwardContinuous_unit_app_hom_app,
      Functor.sheafPushforwardContinuous_map_hom_app,
      Functor.sheafPushforwardContinuousNatTrans_app_hom,
      Functor.sheafPushforwardContinuous_obj_obj_map,
      id_eq, Iso.trans_hom, Iso.refl_hom, Category.id_comp, Category.comp_id,
      Category.assoc, NatTrans.comp_app, NatTrans.id_app,
      ObjectProperty.FullSubcategory.id_hom,
      Functor.whiskerRight_app, NatTrans.op_app,
      Functor.sheafPushforwardContinuous_obj_obj_obj,
      NatIso.ofComponents_inv_app, eqToIso.inv]
    simp only [ObjectProperty.ι_obj]
    erw [← Functor.map_comp, ← Functor.map_comp]
    congr 1
  -- Derive the .inv version pointwise: equal `.hom.app G` ⟹ equal `Iso.app G` ⟹ equal `.inv.app G`.
  have happ :
      (algebraicGlobalRestrictionCompIso (C := AddCommGrpCat.{w}) h).app G =
        (Adjunction.leftAdjointUniq adjComp adjW).app G :=
    Iso.ext hcomp
  have hinv :
      (algebraicGlobalRestrictionCompIso (C := AddCommGrpCat.{w}) h).inv.app G =
        (Adjunction.leftAdjointUniq adjComp adjW).inv.app G := by
    have h2 := congrArg Iso.inv happ
    simpa using h2
  rw [hinv, Adjunction.leftAdjointUniq_inv_app]
  rfl
end

-- ===== generic iso conjugation cancellation =====
theorem iso_conj_cancel {Cat : Type*} [Category Cat] {Q X P Y : Cat}
    (e1 : Q ≅ X) (e2 : P ≅ Y) (k : X ⟶ Y) :
    k = e1.inv ≫ (e1.hom ≫ k ≫ e2.inv) ≫ e2.hom := by
  rw [Category.assoc (e1.hom) (k ≫ e2.inv) e2.hom]
  rw [Category.assoc k e2.inv e2.hom, Iso.inv_hom_id, Category.comp_id]
  rw [Iso.inv_hom_id_assoc]

-- ===== standalone unit-equation lemma =====
set_option backward.isDefEq.respectTransparency false in
theorem huniteq_lemma
  {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)
  {L1 L2 : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R}
  (adj1 : L1 ⊣ SheafOfModules.pushforward φ) (adj2 : L2 ⊣ SheafOfModules.pushforward φ)
  {A1 A2 : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
  (e1 : SheafOfModules.toSheaf S ⋙ A1 ≅ L1 ⋙ SheafOfModules.toSheaf R)
  (e2 : SheafOfModules.toSheaf S ⋙ A2 ≅ L2 ⋙ SheafOfModules.toSheaf R)
  (M : SheafOfModules.{w} S)
  (hluniq :
    (SheafOfModules.toSheaf S).map (adj1.unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map ((SheafOfModules.toSheaf R).map ((adj1.leftAdjointUniq adj2).hom.app M)) =
      (SheafOfModules.toSheaf S).map (adj2.unit.app M)) :
  ((SheafOfModules.toSheaf S).map (adj1.unit.app M) ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e1.inv.app M)) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
        (e1.hom.app M ≫ (SheafOfModules.toSheaf R).map ((adj1.leftAdjointUniq adj2).hom.app M) ≫ e2.inv.app M) =
    (SheafOfModules.toSheaf S).map (adj2.unit.app M) ≫ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e2.inv.app M) := by
  have hc : (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e1.inv.app M) ≫
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e1.hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, e1.inv_hom_id_app M, CategoryTheory.Functor.map_id]
  rw [Functor.map_comp, Functor.map_comp]
  simp only [Category.assoc, reassoc_of% hc]
  rw [← Category.assoc, hluniq]

-- ===== bridging keystone (module → additive leftAdjointUniq) =====
section Keystone
open SheafOfModules
variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)

theorem toSheaf_map_leftAdjointUniq_hom_app
    {L1 L2 : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R}
    (adj1 : L1 ⊣ SheafOfModules.pushforward φ) (adj2 : L2 ⊣ SheafOfModules.pushforward φ)
    {A1 A2 : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
    (Adj1 : A1 ⊣ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K))
    (Adj2 : A2 ⊣ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K))
    (e1 : SheafOfModules.toSheaf S ⋙ A1 ≅ L1 ⋙ SheafOfModules.toSheaf R)
    (e2 : SheafOfModules.toSheaf S ⋙ A2 ≅ L2 ⋙ SheafOfModules.toSheaf R)
    (hu1 : ∀ M, Adj1.unit.app ((SheafOfModules.toSheaf S).obj M) =
      (SheafOfModules.toSheaf S).map (adj1.unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map ((e1.inv.app M)) )
    (hu2 : ∀ M, Adj2.unit.app ((SheafOfModules.toSheaf S).obj M) =
      (SheafOfModules.toSheaf S).map (adj2.unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map ((e2.inv.app M)) )
    (M : SheafOfModules.{w} S) :
    (SheafOfModules.toSheaf R).map ((Adjunction.leftAdjointUniq adj1 adj2).hom.app M) =
      e1.inv.app M ≫ (Adjunction.leftAdjointUniq Adj1 Adj2).hom.app ((SheafOfModules.toSheaf S).obj M) ≫ e2.hom.app M := by
  have hluniq := ModRouteHelpers.toSheaf_unit_leftAdjointUniq φ adj1 adj2 M
  have huniteq0 := huniteq_lemma φ adj1 adj2 e1 e2 M hluniq
  have huniteq :
      Adj1.unit.app ((SheafOfModules.toSheaf S).obj M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map
          (e1.hom.app M ≫
            (SheafOfModules.toSheaf R).map ((Adjunction.leftAdjointUniq adj1 adj2).hom.app M) ≫
              e2.inv.app M) =
        Adj2.unit.app ((SheafOfModules.toSheaf S).obj M) := by
    rw [hu1 M, hu2 M]; exact huniteq0
  have hkey := eq_leftAdjointUniq_hom_app Adj1 Adj2 ((SheafOfModules.toSheaf S).obj M)
    (e1.hom.app M ≫
      (SheafOfModules.toSheaf R).map ((Adjunction.leftAdjointUniq adj1 adj2).hom.app M) ≫
        e2.inv.app M) huniteq
  rw [← hkey]
  exact iso_conj_cancel (e1.app M) (e2.app M)
    ((SheafOfModules.toSheaf R).map ((Adjunction.leftAdjointUniq adj1 adj2).hom.app M))
end Keystone

-- ===== generic unit-compat via mates =====
section UnitCompat
open SheafOfModules CategoryTheory
variable {C : Type u} [Category.{w} C] {D : Type u} [Category.{w} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : CategoryTheory.Sheaf J RingCat.{w}} {R : CategoryTheory.Sheaf K RingCat.{w}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{w} J K).obj R)

set_option backward.isDefEq.respectTransparency false in
/-- Beck–Chevalley unit compatibility (matching the keystone's concrete functors).  Given the
module-side adjunction `adjM : LM ⊣ pushforward φ`, the additive-side adjunction
`Adj : A ⊣ F.sheafPushforwardContinuous`, the bridge iso `e : toSheaf S ⋙ A ≅ LM ⋙ toSheaf R`,
and the mate equation `mateEquiv adjM Adj e.hom = (toSheafPushforwardIso φ).hom`, the additive unit
factors through the module unit and `e.inv`.  Note `(toSheafPushforwardIso φ).hom.app M = 𝟙` so the
codomain of the right factor `G.map (e.inv.app M)` matches by definition. -/
theorem unit_compat_of_mate
    {LM : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R}
    (adjM : LM ⊣ SheafOfModules.pushforward φ)
    {A : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
    (Adj : A ⊣ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K))
    (e : SheafOfModules.toSheaf S ⋙ A ≅ LM ⋙ SheafOfModules.toSheaf R)
    (hmate :
      CategoryTheory.mateEquiv adjM Adj e.hom = (toSheafPushforwardIso φ).hom)
    (M : SheafOfModules.{w} S) :
    Adj.unit.app ((SheafOfModules.toSheaf S).obj M) =
      (SheafOfModules.toSheaf S).map (adjM.unit.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.inv.app M) := by
  have hum := CategoryTheory.unit_mateEquiv adjM Adj e.hom M
  rw [hmate] at hum
  have hc : ∀ (N : SheafOfModules.{w} R), (toSheafPushforwardIso φ).hom.app N = 𝟙 _ := by
    intro N
    apply (sheafToPresheaf J AddCommGrpCat.{w}).map_injective
    apply NatTrans.ext
    funext V
    rfl
  rw [hc] at hum
  replace hum := (Category.comp_id _).symm.trans hum
  -- hum : TS.map (adjM.unit.app M) = Adj.unit.app (TS.obj M) ≫ G.map (e.hom.app M)
  have hcancel :
      (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.hom.app M) ≫
        (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.inv.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, e.hom_inv_id_app M, CategoryTheory.Functor.map_id]
  have hRHS :
      (SheafOfModules.toSheaf S).map (adjM.unit.app M) ≫
          (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.inv.app M) =
        Adj.unit.app ((SheafOfModules.toSheaf S).obj M) := by
    rw [hum]
    simp only [Functor.id_obj]
    refine (Category.assoc (Adj.unit.app ((SheafOfModules.toSheaf S).obj M))
      ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.hom.app M))
      ((F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.inv.app M))).trans ?_
    exact (congrArg (Adj.unit.app ((SheafOfModules.toSheaf S).obj M) ≫ ·) hcancel).trans
      (Category.comp_id _)
  exact hRHS.symm

set_option backward.isDefEq.respectTransparency false in
/-- Reduce the Beck–Chevalley mate equation `mateEquiv adjM Adj e.hom = (toSheafPushforwardIso φ).hom`
to the (componentwise) *unit identity* `(toSheaf S).map (adjM.unit.app N) =
Adj.unit.app _ ≫ (F.sheafPushforwardContinuous).map (e.hom.app N)`.  The mate is the unique 2-cell
characterized by this identity (`unit_mateEquiv`/`unit_mateEquiv_symm`); since the unit-side map
`f ↦ Adj.unit.app _ ≫ R₂.map f` is the (injective) adjunction hom-equivalence, the unit identity pins
the mate down. -/
theorem mateEquiv_eq_of_unit
    {LM : SheafOfModules.{w} S ⥤ SheafOfModules.{w} R}
    (adjM : LM ⊣ SheafOfModules.pushforward φ)
    {A : Sheaf J AddCommGrpCat.{w} ⥤ Sheaf K AddCommGrpCat.{w}}
    (Adj : A ⊣ (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K))
    (e : SheafOfModules.toSheaf S ⋙ A ≅ LM ⋙ SheafOfModules.toSheaf R)
    (hu : ∀ (N : SheafOfModules.{w} S),
        (SheafOfModules.toSheaf S).map (adjM.unit.app N) =
          Adj.unit.app ((SheafOfModules.toSheaf S).obj N) ≫
            (F.sheafPushforwardContinuous AddCommGrpCat.{w} J K).map (e.hom.app N)) :
    CategoryTheory.mateEquiv adjM Adj e.hom = (toSheafPushforwardIso φ).hom := by
  have hc : ∀ (N : SheafOfModules.{w} R), (toSheafPushforwardIso φ).hom.app N = 𝟙 _ := by
    intro N
    apply (sheafToPresheaf J AddCommGrpCat.{w}).map_injective
    apply NatTrans.ext
    funext V
    rfl
  refine (CategoryTheory.mateEquiv adjM Adj).eq_symm_apply.mp ?_
  apply NatTrans.ext
  funext N
  -- goal: e.hom.app N = ((mateEquiv adjM Adj).symm (toSheafPushforwardIso φ).hom).app N
  apply (Adj.homEquiv ((SheafOfModules.toSheaf S).obj N) _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  -- LHS = Adj.unit ≫ R₂.map (e.hom.app N);  RHS = Adj.unit ≫ R₂.map (symm.app N)
  rw [← hu N]
  have hkey := CategoryTheory.unit_mateEquiv_symm adjM Adj (toSheafPushforwardIso φ).hom N
  simp only [hc, Category.comp_id] at hkey
  exact hkey

end UnitCompat

-- ============================================================================
-- MAIN THEOREM
-- ============================================================================
section Main
open SheafOfModules ModRouteHelpers
variable {X : TopCat.{w}}

/-- The natural W-bridge `e1` (PROVEN). -/
def e1Bridge (𝒪 : TopCat.Sheaf RingCat.{w} X) (W : Opens X) :
    SheafOfModules.toSheaf 𝒪 ⋙ (W.isOpenEmbedding.sheafPullback AddCommGrpCat.{w}) ≅
      moduleSheafRestrictionToOpen W 𝒪 ⋙ SheafOfModules.toSheaf (𝒪 |_ W) :=
  NatIso.ofComponents
    (fun ℱ => (moduleToAddCommGrpOpenRestrictionIso 𝒪 W ℱ).symm)
    (by
      intro M N f
      have hnat0 :
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 W M).hom ≫
              (W.isOpenEmbedding.sheafPullback AddCommGrpCat.{w}).map ((SheafOfModules.toSheaf 𝒪).map f) =
            (SheafOfModules.toSheaf (𝒪 |_ W)).map ((moduleSheafRestrictionToOpen W 𝒪).map f) ≫
              (moduleToAddCommGrpOpenRestrictionIso 𝒪 W N).hom := by
        dsimp only [moduleToAddCommGrpOpenRestrictionIso]
        simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom, Category.assoc]
        conv_rhs => rw [← Category.assoc, ← Functor.map_comp]
        erw [(moduleSheafRestrictionToOpen_compare_open_embedding_pushforward W 𝒪).symm.hom.naturality f]
        rw [Functor.map_comp, Category.assoc]
        congr 1
      simp only [Iso.symm_hom, Functor.comp_map]
      rw [Iso.comp_inv_eq, Category.assoc]
      exact (Iso.eq_inv_comp _).2 hnat0)

/-- Section formula for the inverse of `e1Bridge 𝒪 W ≪≫ (isoWhiskerRight κ toSheaf).symm`, the
`e1` of the keystone:  `e1.inv.app ℱ = toSheaf.map (κ.hom.app ℱ) ≫ (openIso 𝒪 W ℱ).hom`. -/
theorem e1_inv_app_eq (𝒪 : TopCat.Sheaf RingCat.{w} X) (W : Opens X)
    {G : SheafOfModules.{w} 𝒪 ⥤ SheafOfModules.{w} (𝒪 |_ W)}
    (κ : G ≅ moduleSheafRestrictionToOpen W 𝒪) (ℱ : SheafOfModules.{w} 𝒪) :
    (e1Bridge 𝒪 W ≪≫
        (Functor.isoWhiskerRight κ (SheafOfModules.toSheaf (𝒪 |_ W))).symm).inv.app ℱ =
      (SheafOfModules.toSheaf (𝒪 |_ W)).map (κ.hom.app ℱ) ≫
        (moduleToAddCommGrpOpenRestrictionIso 𝒪 W ℱ).hom := by
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app]
  rfl

/-- Section formula for the *forward* of `e1Bridge 𝒪 W ≪≫ (isoWhiskerRight κ toSheaf).symm`, the
`e1` of the keystone:  `e1.hom.app ℱ = (openIso 𝒪 W ℱ).inv ≫ toSheaf.map (κ.inv.app ℱ)`. -/
theorem e1_hom_app_eq (𝒪 : TopCat.Sheaf RingCat.{w} X) (W : Opens X)
    {G : SheafOfModules.{w} 𝒪 ⥤ SheafOfModules.{w} (𝒪 |_ W)}
    (κ : G ≅ moduleSheafRestrictionToOpen W 𝒪) (ℱ : SheafOfModules.{w} 𝒪) :
    (e1Bridge 𝒪 W ≪≫
        (Functor.isoWhiskerRight κ (SheafOfModules.toSheaf (𝒪 |_ W))).symm).hom.app ℱ =
      (moduleToAddCommGrpOpenRestrictionIso 𝒪 W ℱ).inv ≫
        (SheafOfModules.toSheaf (𝒪 |_ W)).map (κ.inv.app ℱ) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerRight_inv,
    Functor.whiskerRight_app]
  rfl

-- The pure `W`-side Beck–Chevalley unit identity: the `toSheaf`-image of the module
-- pullback–pushforward unit (for the `W`-inclusion unit `φ_W`) equals the additive open-map unit,
-- post-composed with `(moduleToAddCommGrpOpenRestrictionIso).inv`.
set_option backward.isDefEq.respectTransparency false in
theorem unitCompatW (𝒪 : TopCat.Sheaf RingCat.{w} X) (W : Opens X)
    [hWcont : W.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology X)]
    [hφwRA : (SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
          (openSubsetInclusion W)).unit.app 𝒪)).IsRightAdjoint]
    (N : SheafOfModules.{w} 𝒪) :
    (SheafOfModules.toSheaf 𝒪).map
        ((SheafOfModules.pullbackPushforwardAdjunction
            ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
              (openSubsetInclusion W)).unit.app 𝒪)).unit.app N) =
      (W.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
          (E := AddCommGrpCat.{w})
          (Opens.grothendieckTopology (openSubsetSpace W))
          (Opens.grothendieckTopology X)).unit.app ((SheafOfModules.toSheaf 𝒪).obj N) ≫
        ((Opens.map (openSubsetInclusion W)).sheafPushforwardContinuous AddCommGrpCat.{w}
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace W))).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 W N).inv := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous W.isOpenEmbedding
  set φW := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
          (openSubsetInclusion W)).unit.app 𝒪) with hφW
  set adjA := open_embedding_module_pushforward_adjunction W 𝒪 with hadjA
  set adjB := moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction W 𝒪 with hadjB
  set compareIso := moduleSheafRestrictionToOpen_compare_open_embedding_pushforward W 𝒪 with hcmp
  have hOpen :
      (SheafOfModules.toSheaf (𝒪 |_ W)).obj
          ((SheafOfModules.pushforward.{w} (F := W.isOpenEmbedding.functor)
            (((W.isOpenEmbedding.sheafPullbackIso RingCat.{w}).app 𝒪).hom)).obj N) =
        (W.isOpenEmbedding.sheafPullback AddCommGrpCat.{w}).obj
          ((SheafOfModules.toSheaf 𝒪).obj N) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  have hstep1 :
      (SheafOfModules.toSheaf 𝒪).map
        ((SheafOfModules.pullbackPushforwardAdjunction φW).unit.app N) =
      (SheafOfModules.toSheaf 𝒪).map (adjB.unit.app N) := rfl
  rw [hstep1]
  have hstar :
      (SheafOfModules.toSheaf 𝒪).map (adjA.unit.app N) =
        (W.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
            (E := AddCommGrpCat.{w})
            (Opens.grothendieckTopology (openSubsetSpace W))
            (Opens.grothendieckTopology X)).unit.app ((SheafOfModules.toSheaf 𝒪).obj N) ≫
          ((Opens.map (openSubsetInclusion W)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology X)
              (Opens.grothendieckTopology (openSubsetSpace W))).map (eqToHom hOpen.symm) := by
    apply (TopCat.Sheaf.forget AddCommGrpCat.{w} X).map_injective
    ext V x
    rfl
  have hluniq := ModRouteHelpers.toSheaf_unit_leftAdjointUniq φW adjA adjB N
  have hinv :
      (moduleToAddCommGrpOpenRestrictionIso 𝒪 W N).inv =
        eqToHom hOpen.symm ≫
          (SheafOfModules.toSheaf (𝒪 |_ W)).map (compareIso.hom.app N) := by
    dsimp only [moduleToAddCommGrpOpenRestrictionIso, hcmp]
    simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, eqToIso.inv]
    rfl
  rw [hinv, Functor.map_comp, ← Category.assoc, ← hstar]
  exact hluniq.symm

-- Transport of `unitCompatW` along the `moduleSheafPullbackCongrIso`-equality `hEq : φd = φ_W`
-- (both over the same functor `Opens.map (openSubsetInclusion W)`).  After `subst`-ing `hEq`, `φd`
-- collapses to the `W`-inclusion unit and the `congrI`-transport collapses to the identity.
set_option backward.isDefEq.respectTransparency false in
theorem unitCompatDirect (𝒪 : TopCat.Sheaf RingCat.{w} X) (W : Opens X)
    [hWcont : W.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology X)]
    (φd : 𝒪 ⟶ ((Opens.map (openSubsetInclusion W)).sheafPushforwardContinuous RingCat.{w}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology (openSubsetSpace W))).obj
        ((TopCat.Sheaf.pullback RingCat.{w} (openSubsetInclusion W)).obj 𝒪))
    [hφdRA : (SheafOfModules.pushforward φd).IsRightAdjoint]
    [hφwRA : (SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
          (openSubsetInclusion W)).unit.app 𝒪)).IsRightAdjoint]
    (hEq : φd =
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w} (openSubsetInclusion W)).unit.app 𝒪)
    (N : SheafOfModules.{w} 𝒪) :
    (SheafOfModules.toSheaf 𝒪).map
        ((SheafOfModules.pullbackPushforwardAdjunction φd).unit.app N) =
      (W.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
          (E := AddCommGrpCat.{w})
          (Opens.grothendieckTopology (openSubsetSpace W))
          (Opens.grothendieckTopology X)).unit.app ((SheafOfModules.toSheaf 𝒪).obj N) ≫
        ((Opens.map (openSubsetInclusion W)).sheafPushforwardContinuous AddCommGrpCat.{w}
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace W))).map
          ((moduleToAddCommGrpOpenRestrictionIso 𝒪 W N).inv ≫
            (SheafOfModules.toSheaf
              ((TopCat.Sheaf.pullback RingCat.{w} (openSubsetInclusion W)).obj 𝒪)).map
              ((moduleSheafPullbackCongrIso (φ := φd)
                (ψ := (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{w}
                  (openSubsetInclusion W)).unit.app 𝒪)
                hEq).inv.app N)) := by
  subst hEq
  rw [toSheaf_map_congrIso_inv]
  rw [show (eqToHom (by rfl) :
      (SheafOfModules.toSheaf
        ((TopCat.Sheaf.pullback RingCat.{w} (openSubsetInclusion W)).obj 𝒪)).obj
          ((SheafOfModules.pullback _).obj N) ⟶
        (SheafOfModules.toSheaf
          ((TopCat.Sheaf.pullback RingCat.{w} (openSubsetInclusion W)).obj 𝒪)).obj
          ((SheafOfModules.pullback _).obj N)) = 𝟙 _ from rfl,
    Category.comp_id]
  exact unitCompatW 𝒪 W N

/-- Naturality of the restriction-bridge iso (inlined copy of `moduleToAddCommGrpRestrictionIso_naturality`). -/
theorem moduleToAddCommGrpRestrictionIso_naturality'
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

/-- The natural restriction-bridge `e2Restr` (PROVEN via `moduleToAddCommGrpRestrictionIso_naturality'`). -/
def e2RestrBridge (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U) :
    letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
    SheafOfModules.toSheaf (𝒪 |_ U) ⋙
        ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}) ≅
      moduleSheafRestriction 𝒪 h ⋙ SheafOfModules.toSheaf (𝒪 |_ W) :=
  letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  NatIso.ofComponents
    (fun ℱ => moduleToAddCommGrpRestrictionIso 𝒪 h ℱ)
    (by
      intro M N f
      exact moduleToAddCommGrpRestrictionIso_naturality' 𝒪 h M N f)

/-- The composite restriction bridge `e2` (PROVEN), conjugating the additive
`sheafPullback U ⋙ sheafPullback(homOfLE h)` to `toSheaf ∘ (moduleSheafRestrictionToOpen U ⋙ moduleSheafRestriction h)`. -/
def e2Bridge (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U) :
    letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
    SheafOfModules.toSheaf 𝒪 ⋙
        ((U.isOpenEmbedding.sheafPullback AddCommGrpCat.{w}) ⋙
          ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w})) ≅
      (moduleSheafRestrictionToOpen U 𝒪 ⋙ moduleSheafRestriction 𝒪 h) ⋙
        SheafOfModules.toSheaf (𝒪 |_ W) :=
  letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (e1Bridge 𝒪 U) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (moduleSheafRestrictionToOpen U 𝒪) (e2RestrBridge 𝒪 h) ≪≫
    (Functor.associator _ _ _).symm

theorem e2Bridge_hom_app
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U) (ℱ : SheafOfModules.{w} 𝒪) :
    letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
    (e2Bridge 𝒪 h).hom.app ℱ =
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 U ℱ).inv ≫
        (moduleToAddCommGrpRestrictionIso 𝒪 h
          ((moduleSheafRestrictionToOpen U 𝒪).obj ℱ)).hom := by
  letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  dsimp only [e2Bridge]
  simp only [Iso.trans_hom, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [show (e1Bridge 𝒪 U).hom.app ℱ = (moduleToAddCommGrpOpenRestrictionIso 𝒪 U ℱ).inv from rfl]
  rfl

-- The pure restriction-leg (`homOfLE h`) Beck–Chevalley unit identity:  `toSheaf`-image of the
-- module pullback–pushforward unit (for `ψ = restrictedRingSheafToPushforward 𝒪 h`) equals the
-- additive `homOfLE`-open-map unit, post-composed with `(moduleToAddCommGrpRestrictionIso).hom`.
set_option backward.isDefEq.respectTransparency false in
theorem unitCompatRestr (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U)
    [hPL2cont : (openSubsetHomOfLE_isOpenEmbedding h).functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))]
    [hψRA : (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint]
    (N : SheafOfModules.{w} (𝒪 |_ U)) :
    (SheafOfModules.toSheaf (𝒪 |_ U)).map
        ((SheafOfModules.pullbackPushforwardAdjunction
            (restrictedRingSheafToPushforward 𝒪 h)).unit.app N) =
      ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
          (E := AddCommGrpCat.{w})
          (Opens.grothendieckTopology (openSubsetSpace W))
          (Opens.grothendieckTopology (openSubsetSpace U))).unit.app
            ((SheafOfModules.toSheaf (𝒪 |_ U)).obj N) ≫
        ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map
          (moduleToAddCommGrpRestrictionIso 𝒪 h N).hom := by
  letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  set ψ := restrictedRingSheafToPushforward 𝒪 h with hψ
  set adjA := moduleSheafRestrictionOpenPushAdjunction 𝒪 h with hadjA
  set adjB := SheafOfModules.pullbackPushforwardAdjunction (restrictedRingSheafToPushforward 𝒪 h)
    with hadjB
  set compareIso := moduleSheafRestrictionOpenPushIso 𝒪 h with hcmp
  have hOpen :
      ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).obj
          ((SheafOfModules.toSheaf (𝒪 |_ U)).obj N) =
        (SheafOfModules.toSheaf (𝒪 |_ W)).obj
          ((moduleSheafRestrictionOpenPush 𝒪 h).obj N) := by
    apply ObjectProperty.FullSubcategory.ext
    rfl
  have hstep1 :
      (SheafOfModules.toSheaf (𝒪 |_ U)).map
        ((SheafOfModules.pullbackPushforwardAdjunction ψ).unit.app N) =
      (SheafOfModules.toSheaf (𝒪 |_ U)).map (adjB.unit.app N) := rfl
  rw [hstep1]
  have hstar :
      (SheafOfModules.toSheaf (𝒪 |_ U)).map (adjA.unit.app N) =
        ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
            (E := AddCommGrpCat.{w})
            (Opens.grothendieckTopology (openSubsetSpace W))
            (Opens.grothendieckTopology (openSubsetSpace U))).unit.app
              ((SheafOfModules.toSheaf (𝒪 |_ U)).obj N) ≫
          ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U))
              (Opens.grothendieckTopology (openSubsetSpace W))).map (eqToHom hOpen) := by
    apply (TopCat.Sheaf.forget AddCommGrpCat.{w} (openSubsetSpace U)).map_injective
    ext V x
    rfl
  have hluniq := ModRouteHelpers.toSheaf_unit_leftAdjointUniq ψ adjA adjB N
  have hhom :
      (moduleToAddCommGrpRestrictionIso 𝒪 h N).hom =
        eqToHom hOpen ≫
          (SheafOfModules.toSheaf (𝒪 |_ W)).map (compareIso.hom.app N) := by
    dsimp only [moduleToAddCommGrpRestrictionIso, hcmp]
    simp only [Iso.trans_hom, Functor.mapIso_hom, eqToIso.hom]
    rfl
  rw [hhom, Functor.map_comp, ← Category.assoc, ← hstar]
  exact hluniq.symm

theorem e2Bridge_inv_app
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U) (ℱ : SheafOfModules.{w} 𝒪) :
    letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
    (e2Bridge 𝒪 h).inv.app ℱ =
      (moduleToAddCommGrpRestrictionIso 𝒪 h
          ((moduleSheafRestrictionToOpen U 𝒪).obj ℱ)).inv ≫
        ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 U ℱ).hom := by
  letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  dsimp only [e2Bridge]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.id_comp, Category.comp_id,
    Category.assoc]
  rw [show (e1Bridge 𝒪 U).inv.app ℱ = (moduleToAddCommGrpOpenRestrictionIso 𝒪 U ℱ).hom from rfl]
  rfl

-- The composite additive pushforward `G_PL ⋙ G_U` equals the single `W`-pushforward `G_W`
-- (the open inclusions compose definitionally: `openSubsetHomOfLE h ≫ inclusion U = inclusion W`).
set_option backward.isDefEq.respectTransparency false in
theorem GW_eq_comp (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U)
    [hUcont : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)]
    [hPL2cont : (openSubsetHomOfLE_isOpenEmbedding h).functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))] :
    ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W))) ⋙
      ((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous AddCommGrpCat.{w}
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (openSubsetSpace U))) =
      (Opens.map (openSubsetInclusion W)).sheafPushforwardContinuous AddCommGrpCat.{w}
        (Opens.grothendieckTopology X)
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
  rfl

-- Composite Beck–Chevalley unit identity (hu2), stated with the *single* additive right adjoint
-- `G_W` (which equals `G_PL ⋙ G_U` by `GW_eq_comp`).  Proved by expanding both `.comp` units via
-- `comp_unit_app` and gluing the U-leg (`unitCompatW 𝒪 U`) with the restriction-leg (`unitCompatRestr`).
set_option maxRecDepth 4000 in
set_option backward.isDefEq.respectTransparency false in
theorem unit_compat_comp_concrete
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U)
    [hUcont : U.isOpenEmbedding.functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)]
    [hPL2cont : (openSubsetHomOfLE_isOpenEmbedding h).functor.IsContinuous
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))]
    [hφRA : (SheafOfModules.pushforward
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
          (openSubsetInclusion U)).unit.app 𝒪)).IsRightAdjoint]
    [hψRA : (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint]
    (M : SheafOfModules.{w} 𝒪) :
    ((U.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
          (E := AddCommGrpCat.{w})
          (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)).comp
        ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
          (E := AddCommGrpCat.{w})
          (Opens.grothendieckTopology (openSubsetSpace W))
          (Opens.grothendieckTopology (openSubsetSpace U)))).unit.app
          ((SheafOfModules.toSheaf 𝒪).obj M) =
      (SheafOfModules.toSheaf 𝒪).map
          (((SheafOfModules.pullbackPushforwardAdjunction
                ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
                  (openSubsetInclusion U)).unit.app 𝒪)).comp
              (SheafOfModules.pullbackPushforwardAdjunction
                (restrictedRingSheafToPushforward 𝒪 h))).unit.app M) ≫
        (((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U))
              (Opens.grothendieckTopology (openSubsetSpace W))) ⋙
          ((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology X)
              (Opens.grothendieckTopology (openSubsetSpace U)))).map
          ((e2Bridge 𝒪 h).inv.app M) := by
  letI := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  rw [Functor.map_comp, unitCompatW 𝒪 U M, e2Bridge_inv_app 𝒪 h M,
    Functor.comp_map, Functor.map_comp, Functor.map_comp]
  -- the relevant module morphism, and the open-restriction object
  set N := (moduleSheafRestrictionToOpen U 𝒪).obj M with hN
  set gmod := (SheafOfModules.pullbackPushforwardAdjunction
      (restrictedRingSheafToPushforward 𝒪 h)).unit.app
      ((SheafOfModules.pullback
          ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪)).obj M)
    with hgmod
  have hgmod_N : gmod = (SheafOfModules.pullbackPushforwardAdjunction
      (restrictedRingSheafToPushforward 𝒪 h)).unit.app N := rfl
  -- strict commutation: `toSheaf 𝒪 ∘ (push φU) = G_U ∘ toSheaf(𝒪|U)` on the relevant morphism
  have hstrict :
      (SheafOfModules.toSheaf 𝒪).map ((SheafOfModules.pushforward
          ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪)).map gmod) =
        ((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous AddCommGrpCat.{w}
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace U))).map
          ((SheafOfModules.toSheaf (𝒪 |_ U)).map gmod) := by
    apply (TopCat.Sheaf.forget AddCommGrpCat.{w} X).map_injective
    ext V x
    rfl
  rw [hstrict]
  -- iso leaf abbreviations
  set oiI := (moduleToAddCommGrpOpenRestrictionIso 𝒪 U M).inv with hoiI
  set oiH := (moduleToAddCommGrpOpenRestrictionIso 𝒪 U M).hom with hoiH
  set riI := (moduleToAddCommGrpRestrictionIso 𝒪 h N).inv with hriI
  set riH := (moduleToAddCommGrpRestrictionIso 𝒪 h N).hom with hriH
  -- the inner equation (after cancelling the leading `adjU.unit` and pulling `G_U.map` out)
  have hinner :
      ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
            (E := AddCommGrpCat.{w})
            (Opens.grothendieckTopology (openSubsetSpace W))
            (Opens.grothendieckTopology (openSubsetSpace U))).unit.app
          ((U.isOpenEmbedding.functor.sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)).obj
            ((SheafOfModules.toSheaf 𝒪).obj M)) =
        oiI ≫ (SheafOfModules.toSheaf (𝒪 |_ U)).map gmod ≫
          ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U))
              (Opens.grothendieckTopology (openSubsetSpace W))).map riI ≫
          ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U))
              (Opens.grothendieckTopology (openSubsetSpace W))).map
            (((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).map oiH) := by
    rw [hgmod_N, unitCompatRestr 𝒪 h N, ← hriH]
    -- TSR.map gmod = adjPL.unit.app (TSR N) ≫ G_PL.map riH
    -- cancellations
    have hcancel1 :
        ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
            (Opens.grothendieckTopology (openSubsetSpace U))
            (Opens.grothendieckTopology (openSubsetSpace W))).map riH ≫
          ((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U))
              (Opens.grothendieckTopology (openSubsetSpace W))).map riI = 𝟙 _ := by
      rw [← Functor.map_comp, hriH, hriI,
        (moduleToAddCommGrpRestrictionIso 𝒪 h N).hom_inv_id, CategoryTheory.Functor.map_id]
    -- naturality of the `(homOfLE h)` open-map unit on `oiI : A_U(TSS M) ⟶ TSR N`
    have hnat := ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
        (E := AddCommGrpCat.{w})
        (Opens.grothendieckTopology (openSubsetSpace W))
        (Opens.grothendieckTopology (openSubsetSpace U))).unit.naturality oiI
    -- assemble: cancel `riH ≫ riI`, apply naturality, cancel `oiI ≫ oiH`
    simp only [Functor.comp_map, Category.assoc] at hnat ⊢
    rw [reassoc_of% hnat]
    simp only [Category.assoc, reassoc_of% hcancel1, Topology.IsOpenEmbedding.sheafPullback]
    rw [hoiI, hoiH]
    simp only [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.comp_id]
  rw [hinner]
  simp only [Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
theorem comp_bridge_coherence
    (𝒪 : TopCat.Sheaf RingCat.{w} X) {W U : Opens X} (h : W ≤ U) (ℱ : SheafOfModules.{w} 𝒪) :
    (SheafOfModules.toSheaf (𝒪 |_ W)).map
        ((moduleSheafRestrictionToOpenCompIso 𝒪 h).inv.app ℱ) =
      (moduleToAddCommGrpOpenRestrictionIso 𝒪 W ℱ).hom ≫
        (algebraicGlobalRestrictionCompIso (C := AddCommGrpCat.{w}) h).inv.app
          ((SheafOfModules.toSheaf 𝒪).obj ℱ) ≫
        ((openSubsetHomOfLE_isOpenEmbedding h).sheafPullback AddCommGrpCat.{w}).map
          (moduleToAddCommGrpOpenRestrictionIso 𝒪 U ℱ).inv ≫
        (moduleToAddCommGrpRestrictionIso 𝒪 h
          ((moduleSheafRestrictionToOpen U 𝒪).obj ℱ)).hom := by
  letI hPLcont :
      (openSubsetRestrictionFunctor h).IsContinuous
        (Opens.grothendieckTopology (openSubsetSpace U))
        (Opens.grothendieckTopology (openSubsetSpace W)) :=
    openSubsetRestrictionFunctor_isContinuous h
  letI hφRA :
      (SheafOfModules.pushforward
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion U)).unit.app 𝒪))).IsRightAdjoint :=
    (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction U 𝒪).isRightAdjoint
  letI hψRA :
      (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h)).IsRightAdjoint :=
    moduleSheafRestrictionPushforward_isRightAdjoint 𝒪 h
  letI hcompRA :
      (SheafOfModules.pushforward
        (F := Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h)
        (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion W)).unit.app 𝒪))).IsRightAdjoint := by
    simpa [openSubsetRestrictionFunctor_comp_inclusion h] using
      (moduleSheafRestrictionToOpen_pullbackPushforwardAdjunction W 𝒪).isRightAdjoint
  -- composite pushforward right-adjoint (to feed the direct pushforward of unitU ≫ map ψ)
  letI hcomp1 :
      (SheafOfModules.pushforward (restrictedRingSheafToPushforward 𝒪 h) ⋙
        SheafOfModules.pushforward
          ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
            (openSubsetInclusion U)).unit.app 𝒪)).IsRightAdjoint :=
    ((SheafOfModules.pullbackPushforwardAdjunction
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
          (openSubsetInclusion U)).unit.app 𝒪)).comp
      (SheafOfModules.pullbackPushforwardAdjunction (restrictedRingSheafToPushforward 𝒪 h))).isRightAdjoint
  letI hdirectRA :
      (SheafOfModules.pushforward
        (F := Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h)
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪 ≫
          ((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
                (Opens.grothendieckTopology X) (Opens.grothendieckTopology (openSubsetSpace U))).map
            (restrictedRingSheafToPushforward 𝒪 h))).IsRightAdjoint :=
    Functor.isRightAdjoint_of_iso
      (SheafOfModules.pushforwardComp
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪)
        (restrictedRingSheafToPushforward 𝒪 h))
  unfold moduleSheafRestrictionToOpenCompIso
  rw [Iso.trans_inv, NatTrans.comp_app, Functor.map_comp]
  erw [toSheaf_map_congrIso_inv]
  rw [ModRouteHelpers.pullbackComp_inv_eq_leftAdjointUniq]
  -- additive adjunctions (matching A_inv_eq)
  letI hWcont := W.isOpenEmbedding.functor_isContinuous
  letI hUcont := U.isOpenEmbedding.functor_isContinuous
  letI hPL2cont := (openSubsetHomOfLE_isOpenEmbedding h).functor_isContinuous
  set Adj1 := W.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
    (E := AddCommGrpCat.{w})
    (Opens.grothendieckTopology (openSubsetSpace W)) (Opens.grothendieckTopology X) with hAdj1
  set Adj2 := (U.isOpenEmbedding.isOpenMap.adjunction.sheafPushforwardContinuous
      (E := AddCommGrpCat.{w})
      (Opens.grothendieckTopology (openSubsetSpace U)) (Opens.grothendieckTopology X)).comp
    ((openSubsetHomOfLE_isOpenEmbedding h).isOpenMap.adjunction.sheafPushforwardContinuous
      (E := AddCommGrpCat.{w})
      (Opens.grothendieckTopology (openSubsetSpace W))
      (Opens.grothendieckTopology (openSubsetSpace U))) with hAdj2
  -- the congr iso identifying the direct pullback with restriction-to-open W
  have hEq :
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪) ≫
          (((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
            (Opens.grothendieckTopology X)
            (Opens.grothendieckTopology (openSubsetSpace U))).map
            (restrictedRingSheafToPushforward 𝒪 h)) =
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion W)).unit.app 𝒪) := by
    simpa [openSubsetRestrictionFunctor_comp_inclusion h] using
      restrictedRingSheafToOpenComp_eq 𝒪 h
  set congrI := @moduleSheafPullbackCongrIso _ _ _ _ _ _
    (Opens.map (openSubsetInclusion U) ⋙ openSubsetRestrictionFunctor h)
    _ _ _ _ _ hdirectRA hcompRA hEq with hcongrI
  -- e1 bridge for L1 = pullback(unitU ≫ map ψ)
  set e1 :=
    e1Bridge 𝒪 W ≪≫ (Functor.isoWhiskerRight congrI (SheafOfModules.toSheaf (𝒪 |_ W))).symm with he1
  rw [toSheaf_map_leftAdjointUniq_hom_app
    (Adj1 := Adj1) (Adj2 := Adj2) (e1 := e1) (e2 := e2Bridge 𝒪 h)
    (hu1 := ?hu1) (hu2 := ?hu2)]
  rotate_left
  · intro M
    refine unit_compat_of_mate _ (SheafOfModules.pullbackPushforwardAdjunction _)
      Adj1 e1 ?_ M
    refine mateEquiv_eq_of_unit _ _ Adj1 e1 ?_
    intro N
    rw [he1, e1_hom_app_eq 𝒪 W congrI N, hcongrI]
    exact unitCompatDirect 𝒪 W
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat (openSubsetInclusion U)).unit.app 𝒪 ≫
        ((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous RingCat
              (Opens.grothendieckTopology X) (Opens.grothendieckTopology (openSubsetSpace U))).map
          (restrictedRingSheafToPushforward 𝒪 h)) hEq N
  · intro M
    have hcc := unit_compat_comp_concrete 𝒪 h M
    have hmapeq :
        (((Opens.map (openSubsetHomOfLE h)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology (openSubsetSpace U))
              (Opens.grothendieckTopology (openSubsetSpace W))) ⋙
          ((Opens.map (openSubsetInclusion U)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology X)
              (Opens.grothendieckTopology (openSubsetSpace U)))).map
            ((e2Bridge 𝒪 h).inv.app M) =
          ((Opens.map (openSubsetInclusion W)).sheafPushforwardContinuous AddCommGrpCat.{w}
              (Opens.grothendieckTopology X)
              (Opens.grothendieckTopology (openSubsetSpace W))).map
            ((e2Bridge 𝒪 h).inv.app M) := by
      rw [Functor.congr_hom (GW_eq_comp 𝒪 h) ((e2Bridge 𝒪 h).inv.app M)]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rw [hmapeq] at hcc
    exact hcc
  · rw [← A_inv_eq 𝒪 h, e2Bridge_hom_app 𝒪 h ℱ, he1, e1_inv_app_eq 𝒪 W congrI ℱ,
      hcongrI, toSheaf_map_congrIso_hom]
    rw [Category.assoc (eqToHom _), eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end Main
end Part10CompBridge
end
