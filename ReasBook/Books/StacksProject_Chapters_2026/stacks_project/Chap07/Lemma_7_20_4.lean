module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_20_3

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open Opposite

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable (G : C ⥤ D)
variable (J : GrothendieckTopology C) (K : GrothendieckTopology D)

/- Domain-style sampling for Lemma 7.20.4:
- primary domain: sheafification and cocontinuous pushforward/pullback on sites;
- sampled owner API:
  `GrothendieckTopology.sheafifyMap`,
  `GrothendieckTopology.toSheafify`,
  `Adjunction.leftAdjointUniq`,
  `Functor.ranAdjunction`,
  `Functor.sheafPullbackCocontinuousAdjunction`,
  `sheafificationAdjunction`,
  `presheafToSheaf`;
- source/core/bridge triage:
  `source-facing`: the canonical comparison map `(u^p ℱ)^# ⟶ (u^p (ℱ^#))^#`;
  `core/canonical`: the natural isomorphism between the two left adjoints from presheaves on `D`
  to sheaves on `C`, namely
  `((Functor.whiskeringLeft _ _ _).obj G.op) ⋙ presheafToSheaf J _` and
  `presheafToSheaf K _ ⋙ G.sheafPullbackCocontinuous _ J K`, obtained from
  `Adjunction.leftAdjointUniq` applied to `(G.op.ranAdjunction _).comp
  (sheafificationAdjunction J _)` and
  `(sheafificationAdjunction K _).comp (G.sheafPullbackCocontinuousAdjunction J K)`;
  `bridge/view`: the textbook comparison is the component morphism
  `J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))` of that owner-level natural isomorphism.

Primitive data are the cocontinuous functor `G`, the two sheafification adjunctions, and the
right Kan extension hypotheses. The comparison map is derived API from the owner functors
`presheafToSheaf` and `sheafificationAdjunction`; the public statement should therefore use the
canonical owner natural isomorphism first, with `J.sheafifyMap` and `K.toSheafify` retained as
the source-facing bridge surface for the component formula.
-/

-- Proof sketch: the main owner is the left-adjoint-uniqueness isomorphism comparing sheafify
-- after presheaf pullback with cocontinuous pullback after sheafify. The textbook morphism
-- `J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))` is the component of that owner isomorphism
-- at `F`; the source-facing `IsIso` statement is then a direct consequence.
/-- Lemma 7.20.4, owner level: the two canonical left adjoints from presheaves on `D` to sheaves
on `C` are naturally isomorphic. -/
noncomputable def pullbackCocontinuousSheafificationCompatibility
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F'] :
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op) ⋙
        presheafToSheaf J (Type (max u₁ u₂ v₁ v₂)) ≅
      presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
        G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K :=
  Adjunction.leftAdjointUniq
    ((G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))).comp
      (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))))
    ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).comp
      (G.sheafPullbackCocontinuousAdjunction J K))

/-- Helper for Lemma 7.20.4: the target of the owner-level compatibility component is the
explicit `J`-sheafification of the pulled-back `K`-sheafification, via the tautological sheaf iso.
-/
noncomputable def pullbackCocontinuousSheafificationCompatibility_targetIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    (presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
      G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F ≅
      (presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).obj
        (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
          (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj)) := by
  refine CategoryTheory.ObjectProperty.isoMk
    (P := Presheaf.IsSheaf J (A := Type (max u₁ u₂ v₁ v₂)))
    (X := _) (Y := _) (Iso.refl _)

/-- Helper for Lemma 7.20.4: the tautological target-side sheaf isomorphism is the identity on
underlying presheaves. -/
lemma pullbackCocontinuousSheafificationCompatibility_targetIso_hom_hom_eq_id
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    (pullbackCocontinuousSheafificationCompatibility_targetIso
      (G := G) (J := J) (K := K) F).hom.hom = 𝟙 _ := by
  rfl

/-- Helper for Lemma 7.20.4: the inverse of the tautological target-side sheaf isomorphism is
also the identity on underlying presheaves. -/
lemma pullbackCocontinuousSheafificationCompatibility_targetIso_inv_hom_hom_eq_id
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    (pullbackCocontinuousSheafificationCompatibility_targetIso
      (G := G) (J := J) (K := K) F).inv.hom = 𝟙 _ := by
  rfl

/-- Helper for Lemma 7.20.4: the left side of the restricted cocontinuous pullback adjunction is
the explicit composite `sheafToPresheaf ⋙ whiskeringLeft ⋙ presheafToSheaf`, written in the exact
`restrictFullyFaithful` shape. -/
def sheafPullbackCocontinuous_restrict_commLeft
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F'] :
    sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op ⋙
      presheafToSheaf J (Type (max u₁ u₂ v₁ v₂)) ≅
    G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K ⋙
      𝟭 (Sheaf J (Type (max u₁ u₂ v₁ v₂))) :=
  Iso.refl _

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 7.20.4: the restricted cocontinuous pullback adjunction unit is the ambient
composite-adjunction unit followed by the canonical comparison identifying the right adjoints. -/
lemma sheafPullbackCocontinuousAdjunction_unit_app_hom
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Sheaf K (Type (max u₁ u₂ v₁ v₂))) :
    ((G.sheafPullbackCocontinuousAdjunction J K).unit.app F).hom =
      (((G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))).comp
          (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂)))).unit.app F.obj) ≫
        (G.sheafPushforwardCocontinuousCompSheafToPresheafIso
          (Type (max u₁ u₂ v₁ v₂)) J K).symm.hom.app
    ((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F) := by
  -- Normalize the restricted adjunction unit to the ambient composite-adjunction unit.
  apply ((((G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))).comp
    (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂)))).map_restrictFullyFaithful_unit_app
    (fullyFaithfulSheafToPresheaf K (Type (max u₁ u₂ v₁ v₂)))
    (Functor.FullyFaithful.id _)
    (sheafPullbackCocontinuous_restrict_commLeft (G := G) (J := J) (K := K))
    (G.sheafPushforwardCocontinuousCompSheafToPresheafIso
      (Type (max u₁ u₂ v₁ v₂)) J K).symm) F).trans
  -- The remaining terms are identity whiskerings coming from the restricted-left-adjoint side.
  dsimp [Functor.sheafPullbackCocontinuous]
  erw [Functor.map_id]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Helper for Lemma 7.20.4: applying the `ran`-adjunction hom-equivalence to the whiskered
`K`-sheafification unit recovers the restricted cocontinuous pullback unit. -/
lemma sheafPullbackCocontinuousAdjunction_unit_homEquiv_image
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    ((G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))).homEquiv F
        (((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj
          ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F)).obj))
      (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
          (Type (max u₁ u₂ v₁ v₂))).obj G.op).map
          ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F) ≫
        (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))).unit.app
    (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
              (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
            (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj))) =
      (sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F ≫
        ((G.sheafPullbackCocontinuousAdjunction J K).unit.app
          ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F)).hom := by
  -- First isolate the underlying sheafified `K`-sheafification as a sheaf object.
  let adj₁ := G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))
  let adj₂ := sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))
  let adj₃ := sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))
  let adj₄ := G.sheafPullbackCocontinuousAdjunction J K
  let X := (presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F
  -- The restricted adjunction hom-equivalence at the identity component is exactly the ambient
  -- `ran`-adjunction hom-equivalence applied to the `J`-sheafification unit.
  have hcore0 :
      ((adj₄.homEquiv X
          ((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj X)
          (𝟙 _)).hom) =
        (adj₁.homEquiv X.obj
          ((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj X).obj)
          (adj₂.unit.app
            (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
              (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj X.obj)) := by
    exact ((sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂))).congr_map
      (((adj₁.comp adj₂).restrictFullyFaithful_homEquiv_apply
        (fullyFaithfulSheafToPresheaf K (Type (max u₁ u₂ v₁ v₂)))
        (Functor.FullyFaithful.id _)
        (sheafPullbackCocontinuous_restrict_commLeft (G := G) (J := J) (K := K))
        (G.sheafPushforwardCocontinuousCompSheafToPresheafIso
          (Type (max u₁ u₂ v₁ v₂)) J K).symm
        (𝟙 _)))).trans (by
          -- The ambient composite adjunction sends the identity to its unit.
          dsimp [sheafPullbackCocontinuous_restrict_commLeft,
            Functor.sheafPullbackCocontinuous]
          simpa [Adjunction.comp_unit_app] using
            (Adjunction.homEquiv_unit (adj := adj₁)
              (f := adj₂.unit.app
                (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
                  (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj X.obj))).symm)
  have hcore :
      (adj₁.homEquiv X.obj
        ((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj X).obj)
        (adj₂.unit.app
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
            (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj X.obj)) =
      (sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂))).map (adj₄.unit.app X) := by
    -- Reinterpret the restricted unit as the hom-equivalence image of the identity.
    simpa [Adjunction.homEquiv_id] using hcore0.symm
  -- Finally pull the outer `K`-unit through the `ran`-adjunction by naturality on the left.
  change (adj₁.homEquiv F
      ((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj X).obj)
      (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
          (Type (max u₁ u₂ v₁ v₂))).obj G.op).map
          (adj₃.unit.app F) ≫
        adj₂.unit.app
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
            (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj X.obj)) =
    adj₃.unit.app F ≫
      (sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂))).map (adj₄.unit.app X)
  rw [Adjunction.homEquiv_naturality_left]
  -- This is now exactly the specialized identity computed above.
  change adj₃.unit.app F ≫
      (adj₁.homEquiv X.obj
        ((G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj X).obj)
        (adj₂.unit.app
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
            (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj X.obj)) =
    adj₃.unit.app F ≫
      (sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂))).map (adj₄.unit.app X)
  rw [hcore]

/-- Helper for Lemma 7.20.4: the owner-level compatibility isomorphism sends the canonical
sheafification map on the pulled-back presheaf to the pulled-back `K`-sheafification map. -/
lemma toSheafify_pullbackCocontinuousSheafificationCompatibility
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))).unit.app
        (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F) ≫
        (sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
          ((pullbackCocontinuousSheafificationCompatibility G J K).hom.app F) ≫
        (pullbackCocontinuousSheafificationCompatibility_targetIso
          (G := G) (J := J) (K := K) F).hom.hom =
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
        (Type (max u₁ u₂ v₁ v₂))).obj G.op).map
          ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F) ≫
    (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))).unit.app
          (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
            (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
              (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj)) := by
  -- Route correction: normalize the owner-level `leftAdjointUniq` equation through `adj₁.homEquiv`
  -- and then replace the restricted unit by the explicit formula proved above.
  let adj₁ := G.op.ranAdjunction (Type (max u₁ u₂ v₁ v₂))
  let adj₂ := sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))
  let adj₃ := sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))
  let adj₄ := G.sheafPullbackCocontinuousAdjunction J K
  rw [pullbackCocontinuousSheafificationCompatibility_targetIso_hom_hom_eq_id]
  change adj₂.unit.app (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
      (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F) ≫
      (sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
        (((adj₁.comp adj₂).leftAdjointUniq (adj₃.comp adj₄)).hom.app F) =
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).map
      (adj₃.unit.app F) ≫
      adj₂.unit.app (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
        (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
        (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj))
  let lhs :
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F ⟶
        (sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).obj
          ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
              G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F) :=
    adj₂.unit.app (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
        (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F) ≫
      (sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
        (((adj₁.comp adj₂).leftAdjointUniq (adj₃.comp adj₄)).hom.app F)
  let rhs :
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F ⟶
        (sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).obj
          ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
              G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F) :=
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).map
        (adj₃.unit.app F) ≫
      adj₂.unit.app (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
          (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
          (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj))
  apply (adj₁.homEquiv _ _).injective
  change (adj₁.homEquiv _ _ lhs) = (adj₁.homEquiv _ _ rhs)
  have eq :
      (adj₁.unit.app F ≫
          G.op.ran.map
            (adj₂.unit.app (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
                (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F))) ≫
        G.op.ran.map
          ((sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
            (((adj₁.comp adj₂).leftAdjointUniq (adj₃.comp adj₄)).hom.app F)) =
        adj₃.unit.app F ≫
          (sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂))).map
            (adj₄.unit.app ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F)) := by
    simpa [Adjunction.comp_unit_app, Functor.comp_map, Category.assoc] using
      (adj₁.comp adj₂).unit_leftAdjointUniq_hom_app (adj₃.comp adj₄) F
  have hEq :
      (adj₁.homEquiv _ _ lhs) =
        adj₃.unit.app F ≫
          (sheafToPresheaf K (Type (max u₁ u₂ v₁ v₂))).map
            (adj₄.unit.app ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F)) := by
    rw [Adjunction.homEquiv_unit]
    simpa [lhs, Functor.map_comp, Category.assoc] using eq
  rw [hEq]
  -- The remaining term is exactly the specialized `homEquiv` image of the restricted unit.
  simpa [rhs] using
    (sheafPullbackCocontinuousAdjunction_unit_homEquiv_image
      (G := G) (J := J) (K := K) F).symm

/-- Helper for Lemma 7.20.4: the codomain of the owner comparison component is definitionally the
`J`-sheafification of the pulled-back `K`-sheafification. -/
lemma whiskeringLeft_presheafToSheaf_codomain_adapter
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
        G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F).obj =
      ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).obj
        (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
          (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj))).obj := by
  rfl

/-- Helper for Lemma 7.20.4: the component of the owner-level compatibility isomorphism is the
explicit sheafification map induced by the canonical map into `K`-sheafification. -/
lemma pullbackCocontinuousSheafificationCompatibility_hom_app_hom
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    ((pullbackCocontinuousSheafificationCompatibility G J K).hom.app F).hom ≫
        (pullbackCocontinuousSheafificationCompatibility_targetIso
          (G := G) (J := J) (K := K) F).hom.hom =
      ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map
        (whiskerLeft G.op
          ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F))).hom := by
  let η : ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
      (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F ⟶
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
        (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
        (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj) :=
    whiskerLeft G.op ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F)
  have hleft :
      ((pullbackCocontinuousSheafificationCompatibility G J K).hom.app F).hom ≫
          (pullbackCocontinuousSheafificationCompatibility_targetIso
            (G := G) (J := J) (K := K) F).hom.hom =
        sheafifyLift J
          (η ≫
            (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))).unit.app
              (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
                (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
                  (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj)))
          ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
            G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F).property := by
    -- The owner comparison is the unique lift of the pulled-back `K`-unit.
    apply sheafifyLift_unique J
    simpa [η, Category.assoc] using
      toSheafify_pullbackCocontinuousSheafificationCompatibility
        (G := G) (J := J) (K := K) F
  have hright :
      ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom =
        sheafifyLift J
          (η ≫
            (sheafificationAdjunction J (Type (max u₁ u₂ v₁ v₂))).unit.app
              (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
                (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
                  (((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂))).obj F).obj)))
          ((presheafToSheaf K (Type (max u₁ u₂ v₁ v₂)) ⋙
            G.sheafPullbackCocontinuous (Type (max u₁ u₂ v₁ v₂)) J K).obj F).property := by
    -- The abstract sheafification map satisfies the same universal property by naturality.
    apply sheafifyLift_unique J
    simpa [η] using
      (toSheafify_naturality J η).symm
  exact hleft.trans hright.symm

/-- Helper for Lemma 7.20.4: whiskering the `plusPlusIsoSheafify` comparison identifies the
abstract `K`-sheafification unit with the concrete weak-sheafify map. -/
lemma whiskerLeft_toSheafify_plusPlusIsoSheafify_hom
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    whiskerLeft G.op (K.toSheafify F) ≫
      whiskerLeft G.op ((plusPlusIsoSheafify K (Type (max u₁ u₂ v₁ v₂)) F).hom) =
        whiskerLeft G.op
          ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F) := by
  -- Whiskering preserves the comparison between the concrete weak sheafification unit and the
  -- abstract sheafification adjunction unit.
  rw [← whiskerLeft_comp]
  exact congrArg (whiskerLeft G.op)
    (toSheafify_plusPlusIsoSheafify_hom K (Type (max u₁ u₂ v₁ v₂)) F)

/-- Helper for Lemma 7.20.4: a map on abstract sheafifications is an isomorphism as soon as the
corresponding concrete weak-sheafify map is conjugate to it via `plusPlusIsoSheafify`. -/
lemma concrete_sheafifyMap_isIso_of_abstract_presheafToSheaf_map_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    {P Q : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)} (η : P ⟶ Q)
    [IsIso (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom)] :
    IsIso (J.sheafifyMap η) := by
  let αP := plusPlusIsoSheafify J (Type (max u₁ u₂ v₁ v₂)) P
  let αQ := plusPlusIsoSheafify J (Type (max u₁ u₂ v₁ v₂)) Q
  -- Naturality of `plusPlusFunctorIsoSheafification` identifies the concrete map with a conjugate
  -- of the abstract `presheafToSheaf` map.
  have hnat :
      J.sheafifyMap η ≫ αQ.hom =
        αP.hom ≫ (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) := by
    simpa [αP, αQ, GrothendieckTopology.sheafification_map, sheafification_map] using
      (plusPlusFunctorIsoSheafification J (Type (max u₁ u₂ v₁ v₂))).hom.naturality η
  have hconj :
      J.sheafifyMap η =
        αP.hom ≫ (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) ≫ αQ.inv := by
    simpa [Category.assoc] using congrArg (fun k => k ≫ αQ.inv) hnat
  rw [hconj]
  infer_instance

/-- Helper for Lemma 7.20.4: the owner-level compatibility component is an isomorphism after
forgetting to the underlying presheaf. -/
lemma pullbackCocontinuousSheafificationCompatibility_hom_app_underlying_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso ((sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
      ((pullbackCocontinuousSheafificationCompatibility G J K).hom.app F)) := by
  -- The owner comparison is a natural isomorphism, and `sheafToPresheaf` preserves isomorphisms.
  infer_instance

/-- Helper for Lemma 7.20.4: fix the whiskered `plusPlusIsoSheafify` comparison with explicit
source and target so universe elaboration happens once. -/
noncomputable def whiskered_plusPlusIsoSheafify_hom
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
        (GrothendieckTopology.sheafify (J := K) (D := Type (max u₁ u₂ v₁ v₂)) F) ⟶
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
        (CategoryTheory.sheafify (J := K) (D := Type (max u₁ u₂ v₁ v₂)) F) :=
  ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).map
    ((plusPlusIsoSheafify K (Type (max u₁ u₂ v₁ v₂)) F).hom)

/-- Helper for Lemma 7.20.4: the pulled-back concrete weak sheafification of `F`, named with its
ambient presheaf type to stabilize later `IsIso` statements. -/
noncomputable def whiskered_concreteSheafifyObj
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂) :=
  ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
    (GrothendieckTopology.sheafify (J := K) (D := Type (max u₁ u₂ v₁ v₂)) F)

/-- Helper for Lemma 7.20.4: the pulled-back abstract sheafification of `F`, named with its
ambient presheaf type to stabilize later `IsIso` statements. -/
noncomputable def whiskered_abstractSheafifyObj
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂) :=
  ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj
    (CategoryTheory.sheafify (J := K) (D := Type (max u₁ u₂ v₁ v₂)) F)

/-- Helper for Lemma 7.20.4: the concrete `J`-sheafification map induced by the named whiskered
`plusPlusIsoSheafify` comparison. -/
noncomputable def whiskered_plusPlusIsoSheafify_sheafifyMap
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    J.sheafify (whiskered_concreteSheafifyObj (G := G) (K := K) F) ⟶
      J.sheafify (whiskered_abstractSheafifyObj (G := G) (K := K) F) :=
  let η : whiskered_concreteSheafifyObj (G := G) (K := K) F ⟶
      whiskered_abstractSheafifyObj (G := G) (K := K) F :=
    whiskered_plusPlusIsoSheafify_hom (G := G) (K := K) F
  J.sheafifyMap η

/-- Helper for Lemma 7.20.4: the concrete `J`-sheafification of the whiskered abstract
`K`-sheafification unit. -/
noncomputable def whiskered_abstractUnit_sheafifyMap
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    J.sheafify (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
        (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F) ⟶
      J.sheafify (whiskered_abstractSheafifyObj (G := G) (K := K) F) :=
  let η :
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F ⟶
        whiskered_abstractSheafifyObj (G := G) (K := K) F :=
    whiskerLeft G.op
      ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F)
  J.sheafifyMap η

/-- Helper for Lemma 7.20.4: the concrete weak-sheafify map followed by the named whiskered
comparison recovers the whiskered abstract sheafification unit. -/
lemma whiskered_toSheafify_plusPlusIsoSheafify_hom
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    whiskerLeft G.op (K.toSheafify F) ≫
        whiskered_plusPlusIsoSheafify_hom (G := G) (K := K) F =
      whiskerLeft G.op
        ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F) := by
  -- Unfold the named comparison once and reuse the previously normalized whiskered unit identity.
  simpa [whiskered_plusPlusIsoSheafify_hom] using
    whiskerLeft_toSheafify_plusPlusIsoSheafify_hom (G := G) (K := K) F

/-- Helper for Lemma 7.20.4: the abstract `J`-sheafification of the named whiskered
`plusPlusIsoSheafify` comparison is an isomorphism. -/
lemma whiskered_plusPlusIsoSheafify_hom_presheafToSheaf_map_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map
      (whiskered_plusPlusIsoSheafify_hom (G := G) (K := K) F)).hom) := by
  let e :
      G.op ⋙ (GrothendieckTopology.sheafify (J := K)
        (D := Type (max u₁ u₂ v₁ v₂)) F) ≅
      G.op ⋙ (CategoryTheory.sheafify (J := K)
        (D := Type (max u₁ u₂ v₁ v₂)) F) :=
    Functor.isoWhiskerLeft G.op
      (plusPlusIsoSheafify K (Type (max u₁ u₂ v₁ v₂)) F)
  -- Keep the whiskered isomorphism local so universe elaboration is confined to this proof.
  let _ : IsIso ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map e.hom) := by
    infer_instance
  let _ : IsIso ((sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
      ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map e.hom)) := by
    infer_instance
  -- Rewrite the proof-local whiskered iso to the named morphism used throughout this file.
  simpa [e, whiskered_plusPlusIsoSheafify_hom] using
    (inferInstance :
      IsIso ((sheafToPresheaf J (Type (max u₁ u₂ v₁ v₂))).map
        ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map e.hom)))

/-- Helper for Lemma 7.20.4: the concrete weak sheafification of the named whiskered
`plusPlusIsoSheafify` comparison is an isomorphism. -/
lemma whiskered_plusPlusIsoSheafify_hom_sheafifyMap_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (whiskered_plusPlusIsoSheafify_sheafifyMap (G := G) (J := J) (K := K) F) := by
  let η :
      whiskered_concreteSheafifyObj (G := G) (K := K) F ⟶
        whiskered_abstractSheafifyObj (G := G) (K := K) F :=
    whiskered_plusPlusIsoSheafify_hom (G := G) (K := K) F
  change IsIso (J.sheafifyMap η)
  -- Transfer the abstract mapped-isomorphism to the concrete weak sheafification map.
  let _ : IsIso (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map
      η).hom) := by
    simpa [η] using
    whiskered_plusPlusIsoSheafify_hom_presheafToSheaf_map_isIso
      (G := G) (J := J) (K := K) F
  let αP := plusPlusIsoSheafify J (Type (max u₁ u₂ v₁ v₂))
    (whiskered_concreteSheafifyObj (G := G) (K := K) F)
  let αQ := plusPlusIsoSheafify J (Type (max u₁ u₂ v₁ v₂))
    (whiskered_abstractSheafifyObj (G := G) (K := K) F)
  -- Naturality of `plusPlusIsoSheafify` expresses the concrete map as a conjugate of the abstract one.
  have hnat :
      J.sheafifyMap η ≫ αQ.hom =
        αP.hom ≫ (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) := by
    simpa [αP, αQ, GrothendieckTopology.sheafification_map, sheafification_map] using
      (plusPlusFunctorIsoSheafification J (Type (max u₁ u₂ v₁ v₂))).hom.naturality η
  have hconj :
      J.sheafifyMap η =
        αP.hom ≫ (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) ≫ αQ.inv := by
    simpa [Category.assoc] using congrArg (fun k => k ≫ αQ.inv) hnat
  rw [hconj]
  infer_instance

/-- Helper for Lemma 7.20.4: the concrete `J`-sheafification of the whiskered abstract
`K`-sheafification unit is an isomorphism. -/
lemma pullbackCocontinuous_whiskered_unit_sheafifyMap_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (whiskered_abstractUnit_sheafifyMap (G := G) (J := J) (K := K) F) := by
  let η :
      ((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F ⟶
        whiskered_abstractSheafifyObj (G := G) (K := K) F :=
    whiskerLeft G.op
      ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F)
  change IsIso (J.sheafifyMap η)
  have hcomparison :
      ((pullbackCocontinuousSheafificationCompatibility G J K).hom.app F).hom =
        ((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map
          η).hom := by
    -- Normalize the owner comparison component to the explicit whiskered `K`-unit.
    simpa [pullbackCocontinuousSheafificationCompatibility_targetIso_hom_hom_eq_id
      (G := G) (J := J) (K := K) F, η] using
      pullbackCocontinuousSheafificationCompatibility_hom_app_hom
        (G := G) (J := J) (K := K) F
  have habstract :
      IsIso (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) := by
    -- The owner comparison is already an isomorphism on underlying presheaves.
    rw [← hcomparison]
    simpa using
      pullbackCocontinuousSheafificationCompatibility_hom_app_underlying_isIso
        (G := G) (J := J) (K := K) F
  -- Transfer the abstract isomorphism to the concrete weak sheafification map.
  let _ : IsIso (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map
      η).hom) :=
    habstract
  let αP := plusPlusIsoSheafify J (Type (max u₁ u₂ v₁ v₂))
    (((Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ
        (Type (max u₁ u₂ v₁ v₂))).obj G.op).obj F)
  let αQ := plusPlusIsoSheafify J (Type (max u₁ u₂ v₁ v₂))
    (whiskered_abstractSheafifyObj (G := G) (K := K) F)
  -- Naturality of `plusPlusIsoSheafify` again conjugates the concrete map to the abstract one.
  have hnat :
      J.sheafifyMap η ≫ αQ.hom =
        αP.hom ≫ (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) := by
    simpa [αP, αQ, GrothendieckTopology.sheafification_map, sheafification_map] using
      (plusPlusFunctorIsoSheafification J (Type (max u₁ u₂ v₁ v₂))).hom.naturality η
  have hconj :
      J.sheafifyMap η =
        αP.hom ≫ (((presheafToSheaf J (Type (max u₁ u₂ v₁ v₂))).map η).hom) ≫ αQ.inv := by
    simpa [Category.assoc] using congrArg (fun k => k ≫ αQ.inv) hnat
  rw [hconj]
  infer_instance

/-- Lemma 7.20.4, source-facing bridge: for a cocontinuous functor in the setup of Lemma 7.20.3,
the canonical map `(u^p ℱ)^# ⟶ (u^p (ℱ^#))^#` is an isomorphism. -/
theorem pullbackCocontinuousSheafificationComparison_isIso
    [HasWeakSheafify J (Type (max u₁ u₂ v₁ v₂))]
    [HasWeakSheafify K (Type (max u₁ u₂ v₁ v₂))]
    [G.IsCocontinuous J K]
    [∀ (F' : Cᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)), G.op.HasPointwiseRightKanExtension F']
    (F : Dᵒᵖ ⥤ Type (max u₁ u₂ v₁ v₂)) :
    IsIso (J.sheafifyMap (whiskerLeft G.op (K.toSheafify F))) := by
  have hcomp :
      J.sheafifyMap (whiskerLeft G.op (K.toSheafify F)) ≫
          whiskered_plusPlusIsoSheafify_sheafifyMap (G := G) (J := J) (K := K) F =
        whiskered_abstractUnit_sheafifyMap (G := G) (J := J) (K := K) F := by
    -- Expand the named concrete maps once, then use `sheafifyMap_comp` on the whiskered unit factorization.
    change J.sheafifyMap (whiskerLeft G.op (K.toSheafify F)) ≫
        J.sheafifyMap (whiskered_plusPlusIsoSheafify_hom (G := G) (K := K) F) =
      J.sheafifyMap
        (whiskerLeft G.op
          ((sheafificationAdjunction K (Type (max u₁ u₂ v₁ v₂))).unit.app F))
    rw [← CategoryTheory.GrothendieckTopology.sheafifyMap_comp]
    exact congrArg (J.sheafifyMap)
      (whiskered_toSheafify_plusPlusIsoSheafify_hom (G := G) (K := K) F)
  -- Cancel the right-hand whiskered `plusPlusIsoSheafify` factor from the composite isomorphism.
  exact @IsIso.of_isIso_comp_right _ _ _ _ _
    (J.sheafifyMap (whiskerLeft G.op (K.toSheafify F)))
    (whiskered_plusPlusIsoSheafify_sheafifyMap (G := G) (J := J) (K := K) F)
    (whiskered_plusPlusIsoSheafify_hom_sheafifyMap_isIso
      (G := G) (J := J) (K := K) F)
    (by
      rw [hcomp]
      exact pullbackCocontinuous_whiskered_unit_sheafifyMap_isIso
        (G := G) (J := J) (K := K) F)

end CategoryTheory.Functor
