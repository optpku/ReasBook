module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.Over
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite
open CategoryTheory.Functor.sheafPullbackConstruction

universe w v u

noncomputable section

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]

/-- The sheafification of the left Kan extension of the unit `toSheafify` is an isomorphism. -/
-- Proof sketch: the unit `toSheafify (J.over U) G` is a local equivalence for `J.over U`; apply
-- `W_map_of_adjunction_of_isContinuous` to its left Kan extension along `(Over.forget U).op`, then
-- use `J.W_iff` to convert the resulting `J`-local equivalence into an `IsIso` after sheafifying.
noncomputable instance localization_lowerShriek_toSheafify_map_isIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    IsIso ((presheafToSheaf J (Type w)).map
      (((Over.forget U).op.lan).map (toSheafify (J.over U) G))) := by
  -- Transport the slice-site local equivalence across the left Kan extension along
  -- `(Over.forget U).op`.
  have hW : J.W (((Over.forget U).op.lan).map (toSheafify (J.over U) G)) := by
    exact (Over.forget U).W_map_of_adjunction_of_isContinuous (J.over U) J ((Over.forget U).op.lan)
      ((Over.forget U).op.lanAdjunction (Type w)) (toSheafify (J.over U) G)
      ((J.over U).W_toSheafify G)
  -- Convert the transported `W`-statement into the required isomorphism after sheafification.
  exact (J.W_iff _).1 hW

/-- Lemma 7.25.2: for a site `C`, an object `U`, and a presheaf `G` on the slice site `C/U`, the
localization lower shriek `j_{U!}(G^#)` is canonically isomorphic to the sheaf associated to the
canonical left Kan extension of `G` along `(Over.forget U).op`, equivalently to the presheaf
`V ↦ ∐_{φ : V ⟶ U} G(V \xrightarrow{φ} U)`. -/
noncomputable def localization_lowerShriek_associatedSheafIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    (((Over.forget U).sheafPullback (Type w) (J.over U) J).obj
      ((presheafToSheaf (J.over U) (Type w)).obj G)) ≅
      (presheafToSheaf J (Type w)).obj ((Over.forget U).op.lan.obj G) :=
  let η := ((Over.forget U).op.lan).map (toSheafify (J.over U) G)
  letI : IsIso ((presheafToSheaf J (Type w)).map η) :=
    localization_lowerShriek_toSheafify_map_isIso J U G
  (sheafPullbackIso (Over.forget U) (Type w) (J.over U) J).app
      ((presheafToSheaf (J.over U) (Type w)).obj G) ≪≫
    eqToIso rfl ≪≫
    (asIso ((presheafToSheaf J (Type w)).map η)).symm

/-- The underlying morphism of `localization_lowerShriek_associatedSheafIso` is an isomorphism. -/
-- Proof sketch: this morphism is the forward map of the canonical isomorphism
-- `localization_lowerShriek_associatedSheafIso`.
theorem localization_lowerShriek_associatedSheafIso_hom_isIso
    (J : GrothendieckTopology C) (U : C) (G : (Over U)ᵒᵖ ⥤ Type w)
    [∀ F : (Over U)ᵒᵖ ⥤ Type w, (Over.forget U).op.HasLeftKanExtension F]
    [HasWeakSheafify (J.over U) (Type w)]
    [HasWeakSheafify J (Type w)] :
    IsIso (localization_lowerShriek_associatedSheafIso J U G).hom := by
  -- The forward map of any isomorphism is an isomorphism.
  infer_instance

end
