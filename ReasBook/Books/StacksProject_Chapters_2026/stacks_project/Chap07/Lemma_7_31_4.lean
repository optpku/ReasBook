module

public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Definition_7_15_1_Topoi
public import stacks_project.Chap07.Lemma_7_13_5
public import stacks_project.Chap07.Lemma_7_25_9
public import stacks_project.Chap07.Lemma_7_28_2
public import stacks_project.Chap07.Lemma_7_30_7
public import stacks_project.Chap07.Lemma_7_31_1
public import stacks_project.Chap07.Lemma_7_31_2

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.GrothendieckTopology
open scoped MorphismOfTopoiIn SheafifiedRepresentable

universe u₁ v₁

noncomputable section

namespace CategoryTheory

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₁} [Category.{v₁} D]
variable {JC : GrothendieckTopology C} {JD : GrothendieckTopology D}

/-
Domain-style sampling for Lemma 7.31.4:
- primary domain: localized inverse-image comparisons for morphisms of sites at sheafified
  representables, together with the canonical slice pullback induced by `c : U ⟶ u.obj V`;
- sampled owner declarations:
  `continuous_sheafified_representable_iso`,
  `representable_localization_comparison_agrees_with_localized_inverseImage`,
  `localization_inverseImage_pullback_base_change`,
  `Over.pullback`;
- best owner abstraction:
  the owner-level localized inverse image is already
  `LeftExactAdjunction.localization`, specialized in this chapter by
  `representable_localization_comparison_agrees_with_localized_inverseImage` and then base-changed
  by `localization_inverseImage_pullback_base_change`. The map
  `h[U]^# ⟶ u⁻¹(h[V]^#)` induced by `c` is derived data, so this file should use the canonical
  composite
  `JC.sheafifiedRepresentableMap c ≫ (continuous_sheafified_representable_iso u JD JC V).hom`
  directly instead of introducing a parallel local owner;
- primitive data vs derived API:
  primitive data are the site morphism `u`, the objects `U`, `V`, and the arrow `c : U ⟶ u.obj V`;
  the comparison morphism on sheafified representables and the resulting slice pullback functor are
  derived from the canonical owners above;
- source/core/bridge triage:
  `source-facing`: the theorem below, matching the Stacks comparison for `c : U ⟶ u.obj V`;
  `core/canonical`: `LeftExactAdjunction.localization`, `Over.pullback`, and
    `continuous_sheafified_representable_iso`;
  `bridge/view`: the theorem below, combining the representable-localization comparison with the
    canonical localized pullback/base-change comparison from Lemma `7.31.3`.
-/

-- Proof sketch: combine Lemma `7.31.2`, which identifies the representable-localized inverse
-- image for `u`, with the pullback/base-change comparison from Lemma `7.31.3` for the canonical
-- map `h[U]^# ⟶ u⁻¹(h[V]^#)` induced by `c`.
/-- Helper for Lemma 7.31.4: the source-side relocalization comparison identifies the slice-site
pullback along `c` with pullback in the slice topos over the induced map of sheafified
representables. -/
-- Route correction: we use the canonical relocalization comparison from Lemma `7.25.9`
-- directly, and only whisker it by the outer slice equivalence at `X`.
noncomputable def representable_localization_source_pullback_iso
    {X Y : C}
    [HasWeakSheafify JC (Type (max u₁ v₁))]
    [∀ P : (Over X)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget X).op.HasLeftKanExtension P]
    [∀ P : (Over Y)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget Y).op.HasLeftKanExtension P]
    (c : Y ⟶ X) :
    JC.overPullback (Type (max u₁ v₁)) X ⋙
        JC.overMapPullback (Type (max u₁ v₁)) c ⋙
        JC.representableLocalizationComparison Y ≅
      JC.overPullback (Type (max u₁ v₁)) X ⋙
        JC.representableLocalizationComparison X ⋙
        Over.pullback (JC.sheafifiedRepresentableMap c) := by
  -- The entire source-side comparison is already proved for relocalization in Lemma `7.25.9`.
  exact Functor.isoWhiskerLeft (JC.overPullback (Type (max u₁ v₁)) X)
    (JC.relocalization_inverse_image_over_pullback c)

/-- Helper for Lemma 7.31.4: Lemma 7.31.2 specialized to `u` and `V`, transporting the localized
inverse image at `u(V)` to the inverse image of the localization at `h[V]^#`. -/
noncomputable def representable_localization_target_inverseImageIso
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    (V : D)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : (Over (u.obj V))ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget (u.obj V)).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
    [HasWeakSheafify (JC.over (u.obj V)) (Type (max u₁ v₁))] :
    u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) (u.obj V) ⋙
        JC.representableLocalizationComparison (u.obj V) ≅
      JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization h[V]^#[JD]).inverseImage ⋙
        Over.pullback (continuous_sheafified_representable_iso u JD JC V).hom := by
  -- This is exactly Lemma `7.31.2`, specialized from `JD.sheafifiedRepresentable V`
  -- to the local notation `h[V]^#[JD]`.
  simpa using representable_localization_comparison_inverseImageIso
    (JD := JD) (JC := JC) u V

/-- Helper for Lemma 7.31.4: the pullback functor along the canonical map
`h[U]^# ⟶ f⁻¹(h[V]^#)`, with the sheaf universe and pullback-existence instance fixed
explicitly.  This keeps module-mode typeclass search from introducing a universe metavariable while
elaborating the comparison statements below. -/
noncomputable def representable_localization_induced_pullback
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))] :
    let A := Type (max u₁ v₁)
    let f := u.morphismOfTopoiInOfContinuous JD JC
    let 𝒢 : Sheaf JD A := h[V]^#[JD]
    Over ((f⁻¹).obj 𝒢) ⥤ Over h[U]^#[JC] := by
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := h[V]^#[JD]
  let s : h[U]^#[JC] ⟶ (f⁻¹).obj 𝒢 :=
    JC.sheafifiedRepresentableMap c ≫
      (continuous_sheafified_representable_iso u JD JC V).hom
  haveI : HasPullbacksAlong s := fun {W} h => inferInstance
  exact Over.pullback s

/-- Helper for Lemma 7.31.4: the remaining target-side composite of pullbacks is the specialized
base-change comparison from Lemma 7.31.3. -/
noncomputable def representable_localization_target_base_change_iso
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))] :
    let A := Type (max u₁ v₁)
    let f := u.morphismOfTopoiInOfContinuous JD JC
    let 𝒢 : Sheaf JD A := h[V]^#[JD]
    let a : h[U]^#[JC] ⟶ h[u.obj V]^#[JC] := JC.sheafifiedRepresentableMap c
    let e := continuous_sheafified_representable_iso u JD JC V
    ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
      (f.localization 𝒢).inverseImage ⋙ representable_localization_induced_pullback u c := by
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := h[V]^#[JD]
  let a : h[U]^#[JC] ⟶ h[u.obj V]^#[JC] := JC.sheafifiedRepresentableMap c
  let e := continuous_sheafified_representable_iso u JD JC V
  let s : h[U]^#[JC] ⟶ (f⁻¹).obj 𝒢 := a ≫ e.hom
  haveI : HasPullbacksAlong s := fun {W} h => inferInstance
  -- The remaining target-side step is only the canonical composition law for pullback
  -- functors, with one associator to expose the two pullbacks next to each other.
  change ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
      (f.localization 𝒢).inverseImage ⋙ Over.pullback s
  exact
    Functor.associator ((f.localization 𝒢).inverseImage) (Over.pullback e.hom)
      (Over.pullback a) ≪≫
    Functor.isoWhiskerLeft ((f.localization 𝒢).inverseImage)
      (Over.pullbackComp a e.hom).symm

/-- Helper for Lemma 7.31.4: after localizing at `h[V]^#`, the extra pullback along
`h[U]^# ⟶ u⁻¹(h[V]^#)` is the base-change comparison from Lemma `7.31.3` specialized to the
canonical map induced by `c`. -/
noncomputable def representable_localization_comparison_agrees_with_localized_pullback_iso
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget U).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))] :
    u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) U ⋙
        JC.representableLocalizationComparison U ≅
      JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
            h[V]^#[JD]).inverseImage ⋙
        representable_localization_induced_pullback u c := by
  -- We follow the source proof literally: first rewrite the source through relocalization at
  -- `u(V)`, then transport across Lemma `7.31.2`, and finally package the remaining pullback by
  -- the base-change comparison from Lemma `7.31.3`.
  let A := Type (max u₁ v₁)
  let f := u.morphismOfTopoiInOfContinuous JD JC
  let 𝒢 : Sheaf JD A := h[V]^#[JD]
  let a : h[U]^#[JC] ⟶ h[u.obj V]^#[JC] :=
    JC.sheafifiedRepresentableMap c
  let e := continuous_sheafified_representable_iso u JD JC V
  let sourceIso :
      u.sheafPullback A JD JC ⋙
          JC.overPullback A U ⋙
          JC.representableLocalizationComparison U ≅
        u.sheafPullback A JD JC ⋙
          JC.overPullback A (u.obj V) ⋙
          JC.representableLocalizationComparison (u.obj V) ⋙
          Over.pullback a :=
    Functor.associator (u.sheafPullback A JD JC) (JC.overPullback A U)
      (JC.representableLocalizationComparison U) ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
        ((Functor.sheafPushforwardContinuousComp'
          (Over.mapForget c) A (JC.over U) (JC.over (u.obj V)) JC).symm))
      (JC.representableLocalizationComparison U) ≪≫
    (Functor.associator (u.sheafPullback A JD JC)
      (JC.overPullback A (u.obj V) ⋙ JC.overMapPullback A c)
      (JC.representableLocalizationComparison U)).symm ≪≫
    Functor.isoWhiskerLeft (u.sheafPullback A JD JC)
      (representable_localization_source_pullback_iso (JC := JC) c)
  let targetIso :
      ((f.localization 𝒢).inverseImage ⋙ Over.pullback e.hom ⋙ Over.pullback a) ≅
        (f.localization 𝒢).inverseImage ⋙ Over.pullback (a ≫ e.hom) :=
    representable_localization_target_base_change_iso u c
  -- Compose the verified source rewrite, the representable-localization comparison from
  -- Lemma `7.31.2`, and the target-side base-change packaging.
  exact
    sourceIso ≪≫
      Functor.isoWhiskerRight
        (representable_localization_target_inverseImageIso (JD := JD) (JC := JC) u V)
        (Over.pullback a) ≪≫
      Functor.isoWhiskerLeft
      (JD.overPullback A V ⋙ JD.representableLocalizationComparison V)
        targetIso

/-- Lemma 7.31.4: let `f : (C, JC) ⟶ (D, JD)` be the morphism of sites presented by the continuous
representably flat functor `u : D ⥤ C`, let `V : D`, and let `c : U ⟶ u.obj V`. If
`𝒢 = h_V^#`, `ℱ = h_U^#`, and `s : ℱ ⟶ f^{-1} 𝒢` is the morphism induced by `c`, then via the
identifications `j_ℱ = j_U` and `j_𝒢 = j_V`, the localized site diagram of Lemma `7.28.3`
agrees with the localized sheaf-over-sheaf diagram of Lemma `7.31.3`. In Lean, this is the
comparison between the two inverse-image composites after identifying `Sh(D/V)` and `Sh(C/U)`
with the slice topoi over `h_V^#` and `h_U^#`; the right-hand composite uses the canonical
localized inverse image `((f.localization _).inverseImage ⋙ Over.pullback _)` from
Lemma `7.31.3`, not a separate Chapter 7 alias. -/
theorem representable_localization_comparison_agrees_with_localized_pullback
    (u : D ⥤ C) [IsMorphismOfSites JD JC u]
    [HasSheafify JD (Type (max u₁ v₁))]
    [HasSheafify JC (Type (max u₁ v₁))]
    [∀ P : Dᵒᵖ ⥤ Type (max u₁ v₁), u.op.HasLeftKanExtension P]
    [PreservesFiniteLimits
      (u.op.lan : (Dᵒᵖ ⥤ Type (max u₁ v₁)) ⥤ Cᵒᵖ ⥤ Type (max u₁ v₁))]
    {V : D} {U : C} (c : U ⟶ u.obj V)
    [∀ P : (Over V)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget V).op.HasLeftKanExtension P]
    [∀ P : (Over U)ᵒᵖ ⥤ Type (max u₁ v₁), (Over.forget U).op.HasLeftKanExtension P]
    [HasWeakSheafify (JD.over V) (Type (max u₁ v₁))]
    [HasWeakSheafify (JC.over U) (Type (max u₁ v₁))] :
    IsIsomorphic
      (u.sheafPullback (Type (max u₁ v₁)) JD JC ⋙
        JC.overPullback (Type (max u₁ v₁)) U ⋙
        JC.representableLocalizationComparison U)
      (JD.overPullback (Type (max u₁ v₁)) V ⋙
        JD.representableLocalizationComparison V ⋙
        ((u.morphismOfTopoiInOfContinuous JD JC).localization
            h[V]^#[JD]).inverseImage ⋙
        representable_localization_induced_pullback u c) := by
  exact ⟨representable_localization_comparison_agrees_with_localized_pullback_iso u c⟩

end

end CategoryTheory
