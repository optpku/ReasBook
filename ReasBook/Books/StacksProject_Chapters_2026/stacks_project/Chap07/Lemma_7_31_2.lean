module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_13_5
public import stacks_project.Chap07.Lemma_7_28_1
public import stacks_project.Chap07.Lemma_7_28_2
public import stacks_project.Chap07.Lemma_7_30_5
public import stacks_project.Chap07.Lemma_7_30_7
public import stacks_project.Chap07.Lemma_7_31_1

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn SheafifiedRepresentable

universe u₁ v₁

noncomputable section

namespace CategoryTheory

attribute [local instance] Types.instConcreteCategory
attribute [local instance] Types.instFunLike

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₁} [Category.{v₁} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/- Domain-style sampling for Lemma 7.31.2:
- primary domain: localization of a morphism of topoi at sheafified representables and its
  comparison with the slice-site morphism of Lemma `7.28.1`, expressed on inverse-image functors;
- sampled owner API:
  `continuous_sheafified_representable_iso`,
  `TwoSquare.overPost.rightAdjointIso`,
  `GrothendieckTopology.representableLocalizationComparison_inverseImageIso`,
  `Over.starPullbackIsoStar`,
  `LeftExactAdjunction.localization`;
- best owner abstraction: the localized morphism of topoi is already owned by
  `LeftExactAdjunction.localization`; Lemma `7.31.2` is a bridge/view statement transporting that
  owner through the representable identifications from Lemmas `7.13.5` and `7.30.5` so that its
  inverse image agrees with the slice-site inverse image from Lemma `7.28.2`;
- primitive data: a morphism of sites `u : D ⥤ C`, an object `V : D`, the representable
  identification
  `continuous_sheafified_representable_iso u JD JC V :
    h[u.obj V]^#[JC] ≅ u⁻¹(h[V]^#[JD])`,
  and the comparison equivalences
  `JC.representableLocalizationComparison (u.obj V)` and
  `JD.representableLocalizationComparison V`;
- derived API: the inverse-image comparison isomorphism below, comparing the slice-site inverse
  image from Lemma `7.28.2` with the inverse image of the localized morphism of topoi from
  Lemma `7.31.1` after transporting along the representable localization equivalences.

Source/core/bridge triage:
- `source-facing`: Lemma `7.31.2`, asserting that after identifying
  `𝒢 = h[V]^#[JD]`, `𝒡 = h[u.obj V]^#[JC] = f⁻¹ 𝒢`, and `j_𝒢 = j_V`, `j_𝒡 = j_{u(V)}`, the
  localized topos diagram of Lemma `7.31.1` is the one from Lemma `7.28.1`;
- `core/canonical`: `LeftExactAdjunction.localization` and the right-adjoint comparison owner
  `TwoSquare.overPost.rightAdjointIso`;
- `bridge/view`: the inverse-image comparison isomorphism below, transporting those owners through
  the representable localization equivalences.
-/

section

variable (u : D ⥤ C) [IsMorphismOfSites JD JC u]
variable [HasSheafify JD (Type (max u₁ v₁))]
variable [HasSheafify JC (Type (max u₁ v₁))]
variable [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
variable [Limits.PreservesFiniteLimits
  (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
variable (V : D)
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
variable [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ v₁),
  (Over.forget (u.obj V)).op.HasLeftKanExtension P]
variable [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
variable [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ v₁))]

/-- Lemma 7.31.2: after identifying the slice topoi
`Sh(C, JC) / h[u.obj V]^#[JC]` and `Sh(D, JD) / h[V]^#[JD]` with the slice sites
`Sh(C/u(V), JC.over (u.obj V))` and `Sh(D/V, JD.over V)`, and transporting the source slice along
the canonical representable isomorphism
`h[u.obj V]^#[JC] ≅ f⁻¹(h[V]^#[JD])`, the inverse image of the localized morphism of topoi from
Lemma `7.31.1` agrees with the slice-site inverse image from Lemma `7.28.2`. -/
noncomputable def representable_localization_comparison_inverseImageIso :
    u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V) ≅
      JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
          (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
        Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom := by
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := JD.sheafifiedRepresentable V
  let e := continuous_sheafified_representable_iso u JD JC V
  -- The slice-site comparison from Lemma 7.28.2 applies to `f⁻¹` because inverse-image
  -- functors of morphisms of topoi preserve finite limits, hence all binary products.
  let _ : PreservesFiniteLimits (f⁻¹) := by
    simpa using MorphismOfTopoiIn.inverseImage_preservesFiniteLimits f
  let _ : ∀ Y : Sheaf JD A, PreservesLimit (pair 𝒢 Y) (f⁻¹) := fun Y ↦ by
    infer_instance
  exact
    Functor.associator (u.sheafPullback A JD JC) (JC.overPullback A (u.obj V))
      (JC.representableLocalizationComparison (u.obj V)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
      (JC.representableLocalizationComparison_inverseImageIso (u.obj V)) ≪≫
    Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
      (Over.starPullbackIsoStar e.hom).symm ≪≫
    (Functor.associator (u.sheafPullback A JD JC) (Over.star ((f⁻¹).obj 𝒢))
      (Over.pullback e.hom)).symm ≪≫
    Functor.isoWhiskerRight
      (TwoSquare.overPost.rightAdjointIso (f⁻¹) 𝒢).symm
      (Over.pullback e.hom) ≪≫
    Functor.associator (Over.star 𝒢) (Over.post (f⁻¹)) (Over.pullback e.hom) ≪≫
    (Functor.isoWhiskerRight
      (JD.representableLocalizationComparison_inverseImageIso V)
      (Over.post (f⁻¹) ⋙ Over.pullback e.hom)).symm ≪≫
    Functor.associator (JD.overPullback A V) (JD.representableLocalizationComparison V)
      (Over.post (f⁻¹) ⋙ Over.pullback e.hom)

-- Proof sketch: `representable_localization_comparison_inverseImageIso u V` is already a natural
-- isomorphism, so every component of its `hom` is an isomorphism.
/-- Each component of the functor-level comparison map in Lemma 7.31.2 is an isomorphism. -/
theorem representable_localization_comparison_inverseImageIso_hom_app_isIso
    (ℱ : Sheaf JD (Type (max u₁ v₁))) :
    IsIso
      (show
        ((u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
              JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
              JC.representableLocalizationComparison (u.obj V)).obj ℱ ⟶
            (JD.overPullback (Type (max u₁ v₁)) V ⋙
                JD.representableLocalizationComparison V ⋙
                ((u.morphismOfTopoiInOfContinuous JD JC).localization
                  (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
                Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom).obj ℱ)
          from ((representable_localization_comparison_inverseImageIso u V).hom.app ℱ)) := by
  -- The displayed morphism is the `ℱ`-component of a natural isomorphism.
  -- Hence it is an isomorphism by the canonical componentwise `IsIso` instance.
  simpa using
    (show IsIso (((representable_localization_comparison_inverseImageIso u V).app ℱ).hom) by
      infer_instance)

/-- Objectwise form of Lemma 7.31.2, obtained by evaluating the functor-level comparison at a
sheaf `ℱ` on `D`. -/
noncomputable def representable_localization_comparison_inverseImage_obj
    (ℱ : Sheaf JD (Type (max u₁ v₁))) :
    ((u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V)).obj ℱ) ≅
      ((JD.overPullback (Type (max u₁ v₁)) V ⋙
          JD.representableLocalizationComparison V ⋙
          ((u.morphismOfTopoiInOfContinuous JD JC).localization
            (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
          Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom).obj ℱ) := by
  simpa using (representable_localization_comparison_inverseImageIso u V).app ℱ

/-- The objectwise comparison is exactly the `ℱ`-component of the functor-level comparison
isomorphism. -/
@[simp] theorem representable_localization_comparison_inverseImage_obj_eq_app
    (ℱ : Sheaf JD (Type (max u₁ v₁))) :
    representable_localization_comparison_inverseImage_obj u V ℱ =
      (show
        ((u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
              JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
              JC.representableLocalizationComparison (u.obj V)).obj ℱ ≅
            (JD.overPullback (Type (max u₁ v₁)) V ⋙
                JD.representableLocalizationComparison V ⋙
                ((u.morphismOfTopoiInOfContinuous JD JC).localization
                  (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
                Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom).obj ℱ)
          from (representable_localization_comparison_inverseImageIso u V).app ℱ) := rfl

/-- Proposition-level companion to
`representable_localization_comparison_inverseImageIso`. -/
theorem representable_localization_comparison_agrees_with_localized_inverseImage
    :
    IsIsomorphic
      (u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V))
      (JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
          (JD.sheafifiedRepresentable V : Sheaf JD (Type (max u₁ v₁)))).inverseImage ⋙
        Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom) := by
  exact ⟨representable_localization_comparison_inverseImageIso u V⟩

end

end CategoryTheory
