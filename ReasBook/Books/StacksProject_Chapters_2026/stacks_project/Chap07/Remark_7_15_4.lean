module

public import stacks_project.Chap07.Definition_7_15_1_Topoi
public import stacks_project.Chap07.Lemma_7_12_4
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Limits

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

open scoped MorphismOfTopoiIn

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/- Domain-style sampling for Remark 7.15.4:
- primary domain: morphisms of topoi presented by sheafified representables on a site;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `J.uliftSheafifiedRepresentableFunctor`,
  `J.uliftSheafifiedRepresentableHomEquiv`,
  `Adjunction.leftAdjointUniq`;
- source/core/bridge triage:
  `source-facing`: the Stacks conditions on a sheaf-valued functor `Φ : C ⥤ Sh(K)` saying the
  Hom-presheaves are sheaves, the induced `Φ _*` has a left adjoint, and that left adjoint is left
  exact;
  `core/canonical`: the owner `MorphismOfTopoiIn J K`;
  `bridge/view`: the owner-derived presentation functor `f.presentationFunctor`, together with the
  comparison isomorphisms relating that presentation to the reconstructed morphism of topoi.

Primitive data here are the sheaf-valued functor `Φ` and the three source-facing conditions. The
resulting pushforward, inverse image, and comparison isomorphisms are derived API around the owner
`MorphismOfTopoiIn`, so this file should reuse the chapter owners for sheafified representables
rather than restating them locally. -/

namespace MorphismOfTopoiIn

/-- A morphism of topoi `f : Sh(K) ⟶ Sh(J)` gives a sheaf-valued functor
`U ↦ f^{-1}(h_U^#)` on the source site. -/
noncomputable abbrev presentationFunctor
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K) :
    C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, u₁, v₁} J ⋙ f⁻¹

end MorphismOfTopoiIn

/-- For a sheaf-valued functor `Φ` and a sheaf `F`, the associated Hom-presheaf on `C` is
`U ↦ Hom(Φ(U), F)`. -/
abbrev sheafFunctorHomPresheaf
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Cᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)) :=
  Φ.op ⋙ yoneda.obj F

noncomputable abbrev sheafFunctorPushforwardObj
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (sheafFunctorHomPresheaf Φ F))
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  ⟨sheafFunctorHomPresheaf Φ F, hΦ F⟩

/-- The morphism part of the pushforward reconstructed from a sheaf-valued functor presentation.
-/
noncomputable abbrev sheafFunctorPushforwardMap
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (sheafFunctorHomPresheaf Φ F))
    {F G : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G) :
    sheafFunctorPushforwardObj Φ hΦ F ⟶
      sheafFunctorPushforwardObj Φ hΦ G :=
  Sheaf.homEquiv.symm (Functor.whiskerLeft Φ.op (yoneda.map η))

-- Proof sketch: apply `Sheaf.homEquiv` to reduce the identity statement to the identity law for
-- the canonical `yoneda`-based Hom-presheaf.
/-- The reconstructed pushforward functor preserves identities. -/
theorem sheafFunctorPushforwardMap_id
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (sheafFunctorHomPresheaf Φ F))
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    sheafFunctorPushforwardMap Φ hΦ (𝟙 F) =
      𝟙 (sheafFunctorPushforwardObj Φ hΦ F) := by
  -- Compare the underlying presheaf morphisms, where the statement is the identity law for
  -- whiskering the `yoneda` identity morphism.
  apply Sheaf.homEquiv.injective
  rfl

-- Proof sketch: apply `Sheaf.homEquiv` and use functoriality of the canonical
-- `yoneda`-based Hom-presheaf.
/-- The reconstructed pushforward functor preserves composition. -/
theorem sheafFunctorPushforwardMap_comp
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (sheafFunctorHomPresheaf Φ F))
    {F G H : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G) (θ : G ⟶ H) :
    sheafFunctorPushforwardMap Φ hΦ (η ≫ θ) =
      sheafFunctorPushforwardMap Φ hΦ η ≫
        sheafFunctorPushforwardMap Φ hΦ θ := by
  -- Compare the underlying presheaf morphisms, where the statement reduces to composition in
  -- the whiskered `yoneda` morphisms.
  apply Sheaf.homEquiv.injective
  rfl

/-- When each Hom-presheaf attached to `Φ` is a sheaf on `(C, J)`, these sheaves assemble into the
direct-image functor `Φ _* : Sh(K) ⥤ Sh(J)`. -/
noncomputable def pushforwardFromHomSheaf
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (hΦ : ∀ F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))),
      Presheaf.IsSheaf J (sheafFunctorHomPresheaf Φ F)) :
    Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
      Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) where
  obj F := sheafFunctorPushforwardObj Φ hΦ F
  map η := sheafFunctorPushforwardMap Φ hΦ η
  map_id := sheafFunctorPushforwardMap_id Φ hΦ
  map_comp := sheafFunctorPushforwardMap_comp Φ hΦ

/-- Remark 7.15.4: for a sheaf-valued functor `Φ : C ⥤ Sh(K)`, the three questions in the
Stacks source ask whether the Hom-presheaves `U ↦ Hom(Φ(U), F)` are sheaves on `J`, whether the
induced functor `Φ _*` has a left adjoint `Φ⁻¹`, and whether `Φ⁻¹` is exact. This class records
the affirmative answers to those three questions. -/
class SheafFunctorPresentsMorphismOfTopoi
    (J : GrothendieckTopology C)
    (Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) where
  /-- For every sheaf `F` on `K`, the Hom-presheaf `U ↦ Hom(Φ(U), F)` is a sheaf on `J`. -/
  homSheaf (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Presheaf.IsSheaf J (Φ.op ⋙ yoneda.obj F)
  /-- The left-exact inverse-image functor `Φ⁻¹` reconstructed from the presentation data. -/
  inverseImage :
    Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤ₗ
      Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))
  /-- The reconstructed inverse image is left adjoint to the direct image `Φ _*` assembled from
  the Hom-sheaf condition. -/
  adjunction :
    inverseImage.obj ⊣ pushforwardFromHomSheaf Φ homSheaf

/-- A sheaf-valued functor presentation of a morphism of topoi canonically reconstructs the
corresponding morphism of topoi. -/
noncomputable def SheafFunctorPresentsMorphismOfTopoi.toMorphismOfTopoi
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) :
    MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K :=
  { inverseImageFunctor :=
      hΦ.inverseImage
    pushforward := pushforwardFromHomSheaf Φ hΦ.homSheaf
    adjunction := hΦ.adjunction
    }

noncomputable abbrev comparisonSectionEquiv
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) (U : C)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    (((hΦ.toMorphismOfTopoi).presentationFunctor).obj U ⟶ F) ≃
      (((hΦ.toMorphismOfTopoi) _*).obj F).obj.obj (op U) :=
  ((hΦ.toMorphismOfTopoi).adjunction.homEquiv
      (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) F).trans
    (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
      (((hΦ.toMorphismOfTopoi) _*).obj F) U)

noncomputable abbrev comparisonComponentHomEquiv
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) (U : C)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    (((hΦ.toMorphismOfTopoi).presentationFunctor).obj U ⟶ F) ≃
      (Φ.obj U ⟶ F) :=
  by
    change
      (((hΦ.toMorphismOfTopoi)⁻¹).obj
        (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) ⟶ F) ≃
        (Φ.obj U ⟶ F)
    exact
      (comparisonSectionEquiv hΦ U F).trans <|
        Equiv.cast <| by
          change (((hΦ.toMorphismOfTopoi) _*).obj F).obj.obj (op U) = (Φ.obj U ⟶ F)
          rfl

theorem comparisonComponentHomEquiv_comp
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) (U : C)
    {F G : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G)
    (α : ((hΦ.toMorphismOfTopoi).presentationFunctor).obj U ⟶ F) :
    comparisonComponentHomEquiv hΦ U G (α ≫ η) =
      comparisonComponentHomEquiv hΦ U F α ≫ η := by
  -- Push composition first through the adjunction equivalence and then through the sheafified
  -- representable section equivalence at `U`.
  have hcomp :
      comparisonComponentHomEquiv hΦ U G (α ≫ η) =
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
          (((hΦ.toMorphismOfTopoi) _*).obj G) U
          (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) G)
            (α ≫ η)) := by
    calc
      comparisonComponentHomEquiv hΦ U G (α ≫ η) =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            (((hΦ.toMorphismOfTopoi) _*).obj G) U
            (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) G)
              (α ≫ η)) := by
        rfl
      _ =
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
          (((hΦ.toMorphismOfTopoi) _*).obj G) U
          ((((hΦ.toMorphismOfTopoi).adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) F)
            α) ≫
            ((hΦ.toMorphismOfTopoi) _*).map η) := by
        exact
          congrArg
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
              (((hΦ.toMorphismOfTopoi) _*).obj G) U)
            ((hΦ.toMorphismOfTopoi).adjunction.homEquiv_naturality_right α η)
      _ =
        (((hΦ.toMorphismOfTopoi) _*).map η).hom.app (op U)
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            (((hΦ.toMorphismOfTopoi) _*).obj F) U
            (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) F)
              α)) := by
        exact
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{max u₂ v₂, u₁, v₁} J
            (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) F) α)
            (((hΦ.toMorphismOfTopoi) _*).map η))
  -- The remaining identification is definitional: the reconstructed pushforward acts by
  -- postcomposition with `η` on the Hom-presheaf.
  simpa [comparisonComponentHomEquiv, comparisonSectionEquiv,
    SheafFunctorPresentsMorphismOfTopoi.toMorphismOfTopoi, pushforwardFromHomSheaf,
    sheafFunctorPushforwardMap] using hcomp

noncomputable def comparisonComponentIso
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) (U : C) :
    ((hΦ.toMorphismOfTopoi).presentationFunctor).obj U ≅ Φ.obj U :=
  (Functor.FullyFaithful.preimageIso CategoryTheory.Coyoneda.fullyFaithful <|
    NatIso.ofComponents
      (fun F ↦ Equiv.toIso (comparisonComponentHomEquiv hΦ U F))
      (fun {F G} η ↦ by
        ext α
        simpa using comparisonComponentHomEquiv_comp hΦ U η α)).unop.symm

/-- Helper for Remark 7.15.4: the comparison of the recovered presentation with `Φ` is natural
in the site object. -/
theorem comparisonComponentHomEquiv_naturality
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) {U V : C} (f : U ⟶ V)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))))
    (α : ((hΦ.toMorphismOfTopoi).presentationFunctor).obj V ⟶ F) :
    comparisonComponentHomEquiv hΦ U F
        (((hΦ.toMorphismOfTopoi).presentationFunctor).map f ≫ α) =
      Φ.map f ≫ comparisonComponentHomEquiv hΦ V F α := by
  -- Push the left action through the adjunction equivalence, then identify the resulting section
  -- restriction with the underlying presheaf restriction for `Φ`.
  have hleft :
      comparisonComponentHomEquiv hΦ U F
          (((hΦ.toMorphismOfTopoi).presentationFunctor).map f ≫ α) =
        (((hΦ.toMorphismOfTopoi) _*).obj F).obj.map f.op
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            (((hΦ.toMorphismOfTopoi) _*).obj F) V
            (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J V) F)
              α)) := by
    calc
      comparisonComponentHomEquiv hΦ U F
          (((hΦ.toMorphismOfTopoi).presentationFunctor).map f ≫ α) =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            (((hΦ.toMorphismOfTopoi) _*).obj F) U
            (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U) F)
              (((hΦ.toMorphismOfTopoi).presentationFunctor).map f ≫ α)) := by
        rfl
      _ =
          GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            (((hΦ.toMorphismOfTopoi) _*).obj F) U
            (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, u₁, v₁} J).map
              f) ≫
              ((hΦ.toMorphismOfTopoi).adjunction.homEquiv
                (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J V) F)
                α) := by
        exact
          congrArg
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
              (((hΦ.toMorphismOfTopoi) _*).obj F) U)
            (by
              simpa [MorphismOfTopoiIn.presentationFunctor] using
                (hΦ.toMorphismOfTopoi).adjunction.homEquiv_naturality_left
                  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, u₁, v₁}
                    J).map f) α)
      _ =
          (((hΦ.toMorphismOfTopoi) _*).obj F).obj.map f.op
            (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
              (((hΦ.toMorphismOfTopoi) _*).obj F) V
              (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
                (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J V) F)
                α)) := by
        exact
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality.{max u₂ v₂, u₁, v₁}
            J f (((hΦ.toMorphismOfTopoi) _*).obj F)
            (((hΦ.toMorphismOfTopoi).adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J V) F)
              α))
  -- The last identification is definitional because `((hΦ.toMorphismOfTopoi) _*).obj F` is the
  -- Hom-presheaf attached to `Φ`.
  simpa [comparisonComponentHomEquiv, comparisonSectionEquiv,
    SheafFunctorPresentsMorphismOfTopoi.toMorphismOfTopoi, pushforwardFromHomSheaf] using hleft

theorem comparisonComponentIso_naturality
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) {U V : C} (f : U ⟶ V) :
    ((hΦ.toMorphismOfTopoi).presentationFunctor).map f ≫
        (comparisonComponentIso hΦ V).hom =
      (comparisonComponentIso hΦ U).hom ≫ Φ.map f := by
  -- Apply `coyoneda`, where the componentwise statement is exactly the naturality of
  -- `comparisonComponentHomEquiv` in the site object.
  apply Quiver.Hom.op_inj
  refine
    Functor.FullyFaithful.map_injective
      (F := CategoryTheory.coyoneda)
      CategoryTheory.Coyoneda.fullyFaithful ?_
  ext F α
  -- Compare the two composites after applying the Hom-equivalence at `U`; the left side uses the
  -- site-object naturality helper, while both occurrences of `comparisonComponentIso` collapse by
  -- construction.
  have hIsoV :
      comparisonComponentHomEquiv hΦ V (Φ.obj V) (comparisonComponentIso hΦ V).hom =
        𝟙 (Φ.obj V) := by
    change
      comparisonComponentHomEquiv hΦ V (Φ.obj V)
          ((comparisonComponentHomEquiv hΦ V (Φ.obj V)).symm (𝟙 (Φ.obj V))) =
        𝟙 (Φ.obj V)
    exact
      Equiv.apply_symm_apply (comparisonComponentHomEquiv hΦ V (Φ.obj V)) (𝟙 (Φ.obj V))
  have hIsoU :
      comparisonComponentHomEquiv hΦ U (Φ.obj U) (comparisonComponentIso hΦ U).hom =
        𝟙 (Φ.obj U) := by
    change
      comparisonComponentHomEquiv hΦ U (Φ.obj U)
          ((comparisonComponentHomEquiv hΦ U (Φ.obj U)).symm (𝟙 (Φ.obj U))) =
        𝟙 (Φ.obj U)
    exact
      Equiv.apply_symm_apply (comparisonComponentHomEquiv hΦ U (Φ.obj U)) (𝟙 (Φ.obj U))
  apply (comparisonComponentHomEquiv hΦ U F).injective
  calc
    comparisonComponentHomEquiv hΦ U F
        (hΦ.toMorphismOfTopoi.presentationFunctor.map f ≫ (comparisonComponentIso hΦ V).hom ≫ α) =
      Φ.map f ≫
        comparisonComponentHomEquiv hΦ V F ((comparisonComponentIso hΦ V).hom ≫ α) := by
          simpa [Category.assoc] using
            comparisonComponentHomEquiv_naturality hΦ f F ((comparisonComponentIso hΦ V).hom ≫ α)
    _ = Φ.map f ≫ α := by
      calc
        Φ.map f ≫ comparisonComponentHomEquiv hΦ V F ((comparisonComponentIso hΦ V).hom ≫ α) =
          Φ.map f ≫
            (comparisonComponentHomEquiv hΦ V (Φ.obj V) (comparisonComponentIso hΦ V).hom ≫
              α) := by
                exact
                  congrArg
                    (fun β ↦ Φ.map f ≫ β)
                    (by
                      simpa [Category.assoc] using
                        comparisonComponentHomEquiv_comp hΦ V α
                          (comparisonComponentIso hΦ V).hom)
        _ = Φ.map f ≫ α := by
          rw [hIsoV]
          simp
    _ =
      comparisonComponentHomEquiv hΦ U F
        ((comparisonComponentIso hΦ U).hom ≫ Φ.map f ≫ α) := by
          symm
          calc
            comparisonComponentHomEquiv hΦ U F
                ((comparisonComponentIso hΦ U).hom ≫ Φ.map f ≫ α) =
              comparisonComponentHomEquiv hΦ U (Φ.obj V)
                  ((comparisonComponentIso hΦ U).hom ≫ Φ.map f) ≫ α := by
                    simpa [Category.assoc] using
                      comparisonComponentHomEquiv_comp hΦ U α
                        ((comparisonComponentIso hΦ U).hom ≫ Φ.map f)
            _ =
              (comparisonComponentHomEquiv hΦ U (Φ.obj U) (comparisonComponentIso hΦ U).hom ≫
                  Φ.map f) ≫
                α := by
                  rw [comparisonComponentHomEquiv_comp hΦ U (Φ.map f)
                    (comparisonComponentIso hΦ U).hom]
            _ = Φ.map f ≫ α := by
              rw [hIsoU]
              simp

/-- The sheaf-valued functor recovered from the reconstructed morphism of topoi is naturally
isomorphic to the original `Φ`. Objectwise, this is the identification
`Φ(U) ≅ f⁻¹(h_U^#)` from Remark 7.15.4. -/
noncomputable def SheafFunctorPresentsMorphismOfTopoi.comparisonIso
    {Φ : C ⥤ Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))}
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (hΦ : SheafFunctorPresentsMorphismOfTopoi J Φ) :
    (hΦ.toMorphismOfTopoi).presentationFunctor ≅ Φ :=
  NatIso.ofComponents
    (comparisonComponentIso hΦ)
    (comparisonComponentIso_naturality hΦ)

namespace MorphismOfTopoiIn

-- Proof sketch: for fixed `F`, the presheaf `U ↦ Hom(f⁻¹(h_U^#), F)` identifies by adjunction
-- with the underlying presheaf of `f_* F`; since `f_* F` is already a sheaf, the Hom-presheaf is
-- a sheaf as well.
/-- Helper for Remark 7.15.4: the Hom-presheaf attached to the canonical presentation of `f` is
the underlying presheaf of `(f _*).obj F`. -/
noncomputable def presentationFunctor_homPresheafIso
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    f.presentationFunctor.op ⋙ yoneda.obj F ≅ ((f _*).obj F).obj :=
  NatIso.ofComponents
    (fun U ↦
      Equiv.toIso <|
        (f.adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U.unop) F).trans
          ((GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            ((f _*).obj F) U.unop).trans
            (Equiv.cast <| by
              change ((f _*).obj F).obj.obj (op U.unop) = ((f _*).obj F).obj.obj U
              simp)))
    (fun {U V} g ↦ by
      ext α
      dsimp
      -- First move the restriction map through the adjunction equivalence.
      have hleft :
          (f.adjunction.homEquiv
              (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J V.unop) F)
            (f⁻¹.map
                ((presheafToSheaf J (Type (max (max u₂ v₂) u₁ v₁))).map
                  (CategoryTheory.uliftYoneda.map g.unop)) ≫
              α) =
            ((presheafToSheaf J (Type (max (max u₂ v₂) u₁ v₁))).map
              (CategoryTheory.uliftYoneda.map g.unop)) ≫
              (f.adjunction.homEquiv
                (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U.unop)
                F) α := by
        simpa using
          (f.adjunction.homEquiv_naturality_left
            ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₂ v₂, u₁, v₁} J).map
              g.unop) α)
      rw [hleft]
      -- Then identify the restriction map with the underlying presheaf restriction of `f_* F`.
      simpa using
        (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_naturality.{max u₂ v₂, u₁, v₁}
          J g.unop ((f _*).obj F)
          ((f.adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U.unop) F)
            α)))

/-- For the canonical functor attached to a morphism of topoi, the Hom-presheaf against any sheaf
`F` on the target is a sheaf on the source site. -/
theorem presentationFunctor_homSheaf
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    Presheaf.IsSheaf J
      (f.presentationFunctor.op ⋙ yoneda.obj F) := by
  -- Transport the existing sheaf condition on `(f _*).obj F` across the canonical presheaf iso.
  exact (Presheaf.isSheaf_of_iso_iff (presentationFunctor_homPresheafIso f F)).2 ((f _*).obj F).property

noncomputable abbrev presentationFunctor_pushforwardObjHomEquiv
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) (U : Cᵒᵖ) :
    (sheafFunctorPushforwardObj
      f.presentationFunctor
      (presentationFunctor_homSheaf f) F).obj.obj U ≃
      ((f _*).obj F).obj.obj U :=
  ((presentationFunctor_homPresheafIso f F).app U).toEquiv

noncomputable def presentationFunctor_pushforwardObjIso
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    (F : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    sheafFunctorPushforwardObj
        f.presentationFunctor
        (presentationFunctor_homSheaf f) F ≅
      (f _*).obj F :=
  Functor.FullyFaithful.preimageIso
    (CategoryTheory.fullyFaithfulSheafToPresheaf J (Type (max (max u₁ v₁) (max u₂ v₂))))
    (presentationFunctor_homPresheafIso f F)

theorem presentationFunctor_pushforwardObjIso_naturality
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K)
    {F G : Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))} (η : F ⟶ G) :
    (pushforwardFromHomSheaf
        f.presentationFunctor
        (presentationFunctor_homSheaf f)).map η ≫
      (presentationFunctor_pushforwardObjIso f G).hom =
    (presentationFunctor_pushforwardObjIso f F).hom ≫
      (f _*).map η := by
  -- The comparison isomorphism is defined by preimaging the presheaf-level iso, so after passing
  -- to underlying presheaves the naturality square is definitionally the square for that iso.
  apply Sheaf.homEquiv.injective
  ext U α
  -- Evaluate the sectionwise comparison isomorphism and push composition through the adjunction
  -- and the sheafified-representable section equivalence.
  change
    presentationFunctor_pushforwardObjHomEquiv f G U
        (((pushforwardFromHomSheaf
          f.presentationFunctor
          (presentationFunctor_homSheaf f)).map η).hom.app U α) =
      ((f _*).map η).hom.app U (presentationFunctor_pushforwardObjHomEquiv f F U α)
  have hmap :
      (((pushforwardFromHomSheaf
          f.presentationFunctor
          (presentationFunctor_homSheaf f)).map η).hom.app U α) =
        α ≫ η := by
    rfl
  rw [hmap]
  calc
    presentationFunctor_pushforwardObjHomEquiv f G U (α ≫ η) =
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
          ((f _*).obj G) U.unop
          ((f.adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U.unop) G)
            (α ≫ η)) := by
      rfl
    _ =
        GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
          ((f _*).obj G) U.unop
          (((f.adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U.unop) F)
            α) ≫
            (f _*).map η) := by
      exact
        congrArg
          (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv.{max u₂ v₂, u₁, v₁} J
            ((f _*).obj G) U.unop)
          (f.adjunction.homEquiv_naturality_right α η)
    _ = ((f _*).map η).hom.app U (presentationFunctor_pushforwardObjHomEquiv f F U α) := by
      exact
        (GrothendieckTopology.uliftSheafifiedRepresentableHomEquiv_comp.{max u₂ v₂, u₁, v₁} J
          ((f.adjunction.homEquiv
            (GrothendieckTopology.uliftSheafifiedRepresentable.{max u₂ v₂, u₁, v₁} J U.unop) F) α)
          ((f _*).map η))

-- Proof sketch: the reconstructed pushforward functor attached to the canonical presentation is
-- exactly `pushforwardFromHomSheaf f.presentationFunctor (presentationFunctor_homSheaf f)`.
/-- For the canonical presentation `U ↦ f⁻¹(h_U^#)`, the reconstructed pushforward functor
`pushforwardFromHomSheaf f.presentationFunctor (presentationFunctor_homSheaf f)` is canonically
isomorphic to the original direct image functor `f _*`. -/
noncomputable def presentationFunctor_pushforwardIso
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K) :
    pushforwardFromHomSheaf f.presentationFunctor (presentationFunctor_homSheaf f) ≅ f _* :=
  NatIso.ofComponents
    (presentationFunctor_pushforwardObjIso f)
    (presentationFunctor_pushforwardObjIso_naturality f)

/-- The canonical sheaf-valued functor attached to a morphism of topoi satisfies the presentation
conditions from `SheafFunctorPresentsMorphismOfTopoi`. -/
noncomputable instance
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₁, u₂, v₁, v₂, max (max u₁ v₁) (max u₂ v₂)} J K) :
    SheafFunctorPresentsMorphismOfTopoi J
      f.presentationFunctor where
  homSheaf := presentationFunctor_homSheaf f
  inverseImage := f.inverseImageFunctor
  adjunction := f.adjunction.ofNatIsoRight (presentationFunctor_pushforwardIso f).symm

end MorphismOfTopoiIn

end CategoryTheory
