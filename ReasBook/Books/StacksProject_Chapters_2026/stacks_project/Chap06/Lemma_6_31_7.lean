module

public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Filtered
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import stacks_project.Chap06.Extension_by_zero_by_the_initial_object
public import stacks_project.Chap06.Lemma_6_21_5
public import stacks_project.Chap06.Definition_6_31_5

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open TopologicalSpace.Opens

noncomputable section

universe w u

namespace OpenSubsetExtensionByInitial

section

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{w} C] [HasInitial C] [HasColimits C]

/- Domain-style sampling for Lemma 6.31.7:
- primary domain: extension by the initial object along the open immersion `j : U ↪ X`, viewed as
  the left adjoint to restriction / pullback on presheaves and sheaves;
- sampled owner declarations:
  `openSubsetPresheafExtensionByInitialObject`,
  `openSubsetSheafExtensionByInitialObject`,
  `(U.isOpenEmbedding.functor.op).lanAdjunction`,
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`,
  `IsOpenMap.pullbackIso`,
  `Topology.IsOpenEmbedding.sheafPullbackIso`;
- owner abstraction: the core owners are the restriction functors
  `TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U)` and
  `TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)`, together with their canonical
  left-adjoint constructions coming from left Kan extension on presheaves and sheaf pullback
  construction on sheaves;
- primitive data: the open subset `U` and the canonical extension-by-initial functors already
  defined upstream in `Extension_by_zero_by_the_initial_object`;
- derived API: the adjunctions, unit isomorphisms, and stalk descriptions below.

Source/core/bridge triage:
- `source-facing`: the Stacks-project adjunction, unit, and stalk statements for `j_!`;
- `core/canonical`: the owner adjunctions built from `lanAdjunction` and
  `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous`, transported along the canonical
  pullback comparison isomorphisms;
- `bridge/view`: the identifications of the explicit source-facing extension-by-initial functors
  with those owner left adjoints. This file should therefore reuse those owners directly rather
  than keep parallel local wrappers around them. -/

public abbrev openSubsetOpenFunctor (U : Opens X) :
    Opens (extensionByZeroOpenSubsetSpace U) ⥤ Opens X :=
  U.isOpenEmbedding.functor

public noncomputable instance openSubsetOpenFunctor_full (U : Opens X) :
    (openSubsetOpenFunctor U).Full := by
  letI : Mono (extensionByZeroOpenSubsetInclusion U) :=
    (TopCat.mono_iff_injective _).2 Subtype.val_injective
  let h : IsOpenMap (extensionByZeroOpenSubsetInclusion U) := U.isOpenEmbedding.isOpenMap
  change h.functor.Full
  infer_instance

/-- Helper for Lemma 6.31.7: the functor on opens induced by the open immersion is cocontinuous
for the Grothendieck topologies on opens. -/
public instance openSubsetOpenFunctor_isCocontinuous (U : Opens X) :
    (openSubsetOpenFunctor U).IsCocontinuous
      (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Opens.grothendieckTopology X) := by
  let h : IsOpenMap (extensionByZeroOpenSubsetInclusion U) := U.isOpenEmbedding.isOpenMap
  change h.functor.IsCocontinuous
    (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
    (Opens.grothendieckTopology X)
  -- The direct-image functor on opens is cocontinuous because the right adjoint `Opens.map`
  -- preserves covering sieves for open maps.
  exact (Adjunction.isCocontinuous_iff_coverPreserving
    (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
    (Opens.grothendieckTopology X) h.adjunction).2
    (coverPreserving_opens_map (extensionByZeroOpenSubsetInclusion U))

public theorem imageOpen_le_openSubset (U : Opens X)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (openSubsetOpenFunctor U).obj V ≤ U := by
  intro x hx
  change x ∈ (((openSubsetOpenFunctor U).obj V : Opens X) : Set X) at hx
  change x ∈ (U : Set X)
  simp [openSubsetOpenFunctor, Topology.IsOpenEmbedding.functor, IsOpenMap.functor] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

public theorem preimage_imageOpen_eq (U : Opens X)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V) = V := by
  ext x
  simp [openSubsetPreimageOpen, openSubsetOpenFunctor, Topology.IsOpenEmbedding.functor,
    IsOpenMap.functor]

public theorem image_preimageOpen_eq_of_le (U W : Opens X) (h : W ≤ U) :
    (openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) = W := by
  ext x
  constructor
  · intro hx
    change x ∈ (((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) : Opens X) : Set X) at hx
    simp [openSubsetOpenFunctor, openSubsetPreimageOpen, Topology.IsOpenEmbedding.functor,
      IsOpenMap.functor] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    change x ∈ (((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) : Opens X) : Set X)
    refine ⟨⟨x, h hx⟩, ?_, rfl⟩
    simpa [openSubsetPreimageOpen]

/-- Helper for Lemma 6.31.7: after pulling an image open of the subspace back along the
inclusion, the original presheaf section object is recovered. -/
public theorem openSubsetPresheafExtensionByInitial_source_eq
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    ℱ.obj V =
      ℱ.obj (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj (unop V)))) := by
  -- Rewrite the pulled-back image open back to the original open of the subspace.
  simpa [preimage_imageOpen_eq] using
    congrArg (fun T => ℱ.obj (op T)) (preimage_imageOpen_eq U (unop V)).symm

/-- Helper for Lemma 6.31.7: the pullback of the restriction map between image opens is the
original restriction map of the presheaf, up to the canonical image-preimage identifications. -/
public theorem openSubsetPresheafExtensionByInitial_source_map_eq
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
        ((openSubsetOpenFunctor U).map i.unop)).op =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V).symm ≫
        ℱ.map i ≫
          eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ W) := by
  have hmorph :
      ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
          ((openSubsetOpenFunctor U).map i.unop)).op =
        eqToHom
            (by
              simpa [preimage_imageOpen_eq] using
                congrArg op (preimage_imageOpen_eq U (unop V)).symm) ≫
          i ≫
            eqToHom
              (by
                simpa [preimage_imageOpen_eq] using
                  congrArg op (preimage_imageOpen_eq U (unop W))) := by
    exact Subsingleton.elim _ _
  -- Apply the presheaf map to the thin-category equality above and simplify the `eqToHom` terms.
  simpa [openSubsetPresheafExtensionByInitial_source_eq, CategoryTheory.eqToHom_map,
    Category.assoc] using congrArg ℱ.map hmorph

/-- Helper for Lemma 6.31.7: on the ambient side, the value of a presheaf on
`image (preimage W)` identifies with the value on `W` when `W ≤ U`. -/
public theorem openSubsetPresheafExtensionByInitial_target_eq_of_le
    (U : Opens X) (𝒢 : X.Presheaf C) {W : (Opens X)ᵒᵖ} (hW : unop W ≤ U) :
    𝒢.obj (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U (unop W)))) =
      𝒢.obj W := by
  -- Rewrite `image (preimage W)` back to `W` inside the ambient presheaf.
  simpa using congrArg (fun T : Opens X => 𝒢.obj (op T)) (image_preimageOpen_eq_of_le U (unop W) hW)

/-- Helper for Lemma 6.31.7: after restricting to the open subspace and pushing back to the
ambient space, the induced map on the ambient presheaf is the original restriction map. -/
public theorem openSubsetPresheafExtensionByInitial_target_map_eq
    (U : Opens X) (𝒢 : X.Presheaf C) {V W : (Opens X)ᵒᵖ} (i : V ⟶ W)
    (hV : unop V ≤ U) (hW : unop W ≤ U) :
    𝒢.map
        ((openSubsetOpenFunctor U).op.map
          ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op) =
      eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) ≫
        𝒢.map i ≫
          eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW).symm := by
  have hmorph :
      ((openSubsetOpenFunctor U).op.map
          ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op) =
        eqToHom
            (by
              simpa using
                congrArg op (image_preimageOpen_eq_of_le U (unop V) hV)) ≫
          i ≫
            eqToHom
              (by
                simpa using
                  congrArg op (image_preimageOpen_eq_of_le U (unop W) hW).symm) := by
    exact Subsingleton.elim _ _
  -- Apply the ambient presheaf to the thin-category equality and simplify the transports.
  simpa [openSubsetPresheafExtensionByInitial_target_eq_of_le, CategoryTheory.eqToHom_map,
    Category.assoc] using congrArg 𝒢.map hmorph

/-- Helper for Lemma 6.31.7: the comparison unit from a presheaf on the open subspace to the
restriction of its explicit extension only uses the inside branch. -/
public theorem openSubsetPresheafExtensionByInitial_comparisonUnit_obj_eq
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    ℱ.obj V = (((openSubsetOpenFunctor U).op ⋙ (jₚ! U).obj ℱ).obj V) :=
  (openSubsetPresheafExtensionByInitial_source_eq U ℱ V).trans
    (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
      (imageOpen_le_openSubset U (unop V))).symm

/-- Helper for Lemma 6.31.7: the comparison unit from a presheaf on the open subspace to the
restriction of its explicit extension only uses the inside branch. -/
public noncomputable def openSubsetPresheafExtensionByInitial_comparisonUnit_app
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    ℱ.obj V ⟶ (((openSubsetOpenFunctor U).op ⋙ (jₚ! U).obj ℱ).obj V) :=
  -- Route correction: define the comparison component directly in the visible two-step transport
  -- normal form, so later naturality proofs do not have to reconstruct it from `eqToHom_trans`.
  eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
    eqToHom
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
        (imageOpen_le_openSubset U (unop V))).symm

/-- Helper for Lemma 6.31.7: expanding the single comparison transport recovers the original
source transport followed by the explicit ambient-inside identification. -/
public theorem openSubsetPresheafExtensionByInitial_comparisonUnit_app_eq_source_transport
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ V =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
            (imageOpen_le_openSubset U (unop V))).symm := by
  -- The component is now defined in exactly this transport normal form.
  rfl

/-- Helper for Lemma 6.31.7: the ambient inside-branch identification cancels with its inverse. -/
public theorem openSubsetPresheafExtensionByInitial_inside_transport_cancel
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    eqToHom
        (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
          (imageOpen_le_openSubset U (unop V))).symm ≫
      eqToHom
        (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
          (imageOpen_le_openSubset U (unop V))) =
        𝟙 _ := by
  -- The two ambient identifications compose to the identity because the underlying equality proof
  -- is proposition-valued and hence proof-irrelevant.
  rw [CategoryTheory.eqToHom_trans]
  simpa using congrArg eqToHom
    (show
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
          (imageOpen_le_openSubset U (unop V))).symm.trans
        (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
          (imageOpen_le_openSubset U (unop V))) = rfl from
        Subsingleton.elim _ _)

/-- Helper for Lemma 6.31.7: precomposing the inside-branch cancellation by the source transport
still yields the same source transport. -/
public theorem openSubsetPresheafExtensionByInitial_source_transport_comp_inside_cancel
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
        (eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
              (imageOpen_le_openSubset U (unop V))).symm ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
              (imageOpen_le_openSubset U (unop V)))) =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) := by
  -- Reuse the ambient cancellation and simplify the resulting right identity.
  simpa using congrArg
    (fun k ↦ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫ k)
    (openSubsetPresheafExtensionByInitial_inside_transport_cancel U ℱ V)

/-- Helper for Lemma 6.31.7: after postcomposing the comparison component with the ambient-inside
identification, only the source-side transport remains. -/
public theorem openSubsetPresheafExtensionByInitial_comparisonUnit_app_comp_obj_eq
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ V ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
            (imageOpen_le_openSubset U (unop V))) =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) := by
  -- Expand the comparison component and cancel the ambient inside-branch identification.
  simpa [openSubsetPresheafExtensionByInitial_comparisonUnit_app, Category.assoc] using
    openSubsetPresheafExtensionByInitial_source_transport_comp_inside_cancel U ℱ V

/-- Helper for Lemma 6.31.7: a morphism of presheaves commutes with the source-side transport
that identifies an image open with its pulled-back preimage. -/
public theorem openSubsetPresheafExtensionByInitial_source_transport_naturality
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    η.app V ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U 𝒢 V) =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
        η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj (unop V)))) := by
  -- Apply naturality to the canonical map from `V` to the pulled-back image open.
  let e :
      V ⟶ op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj (unop V))) :=
    eqToHom
      (by
        simpa [preimage_imageOpen_eq] using
          congrArg op (preimage_imageOpen_eq U (unop V)).symm)
  simpa [e, openSubsetPresheafExtensionByInitial_source_eq, CategoryTheory.eqToHom_map] using
    η.naturality e

/-- Helper for Lemma 6.31.7: for an ambient presheaf restricted to the open subspace, the
source-side transport and the target-side transport are inverse to each other on image opens. -/
public theorem openSubsetPresheafExtensionByInitial_target_transport_cancel
    (U : Opens X) (𝒢 : X.Presheaf C)
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    eqToHom
        (openSubsetPresheafExtensionByInitial_source_eq U
          (((openSubsetOpenFunctor U).op ⋙ 𝒢)) V) ≫
      eqToHom
        (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢
          (imageOpen_le_openSubset U (unop V))) =
        𝟙 _ := by
  -- Both transports come from the same equality `image (preimage (image V)) = image V`.
  rw [CategoryTheory.eqToHom_trans]
  simpa using congrArg eqToHom
    (show
      (openSubsetPresheafExtensionByInitial_source_eq U
          (((openSubsetOpenFunctor U).op ⋙ 𝒢)) V).trans
        (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢
          (imageOpen_le_openSubset U (unop V))) = rfl from
        Subsingleton.elim _ _)

/-- Helper for Lemma 6.31.7: the comparison unit is natural on the open subspace because both
its source and target maps are the original restriction maps, up to canonical transports. -/
public theorem openSubsetPresheafExtensionByInitial_comparisonUnit_naturality
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    ℱ.map i ≫ openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ W =
      openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ V ≫
        ((jₚ! U).obj ℱ).map ((openSubsetOpenFunctor U).op.map i) := by
  let hV : unop (((openSubsetOpenFunctor U).op).obj V) ≤ U :=
    imageOpen_le_openSubset U (unop V)
  let hW : unop (((openSubsetOpenFunctor U).op).obj W) ≤ U :=
    imageOpen_le_openSubset U (unop W)
  have hmap :
      ((jₚ! U).obj ℱ).map ((openSubsetOpenFunctor U).op.map i) =
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
            ((openSubsetOpenFunctor U).map i.unop)).op ≫
            eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := by
    simpa [openSubsetPresheafExtensionByInitialObject] using
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le U ℱ
        (((openSubsetOpenFunctor U).op).map i) hV hW)
  -- Rewrite the target map and both comparison components into the common pulled-back source
  -- object of `ℱ`.
  rw [openSubsetPresheafExtensionByInitial_comparisonUnit_app_eq_source_transport]
  conv_rhs =>
    rw [openSubsetPresheafExtensionByInitial_comparisonUnit_app_eq_source_transport]
    rw [hmap]
  let hs := openSubsetPresheafExtensionByInitial_source_map_eq U ℱ i
  have hs' :
      ℱ.map i ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ W) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm =
        eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
          ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
            ((openSubsetOpenFunctor U).map i.unop)).op ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
            k ≫
              eqToHom
                (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm)
        hs.symm
  -- After those rewrites, every transport appears as an inverse pair and cancels.
  calc
    ℱ.map i ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ W) ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
        ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
          ((openSubsetOpenFunctor U).map i.unop)).op ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := hs'
    _ =
      (eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ V) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV).symm) ≫
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
            ((openSubsetOpenFunctor U).map i.unop)).op ≫
            eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := by
      simp [Category.assoc]

/-- Helper for Lemma 6.31.7: the canonical comparison unit is a natural transformation. -/
public noncomputable def openSubsetPresheafExtensionByInitial_comparisonUnit
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    ℱ ⟶ ((openSubsetOpenFunctor U).op ⋙ (jₚ! U).obj ℱ) where
  app := openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
  naturality := by
    intro V W i
    simpa [Functor.comp_map] using
      openSubsetPresheafExtensionByInitial_comparisonUnit_naturality U ℱ i

/-- Helper for Lemma 6.31.7: the comparison unit is natural in the input presheaf morphism. -/
public theorem openSubsetPresheafExtensionByInitial_comparisonUnit_map_naturality
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢) :
    η ≫ openSubsetPresheafExtensionByInitial_comparisonUnit U 𝒢 =
      openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
        Functor.whiskerLeft ((openSubsetOpenFunctor U).op) ((jₚ! U).map η) := by
  ext V
  let hV : (openSubsetOpenFunctor U).obj V ≤ U :=
    imageOpen_le_openSubset U V
  have hη :
      ((jₚ! U).map η).app (op ((openSubsetOpenFunctor U).obj V)) =
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
            eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
    simpa [openSubsetPresheafExtensionByInitialObject] using
      (openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le U η
        (op ((openSubsetOpenFunctor U).obj V)) hV)
  -- Evaluate at the ambient open `V` and rewrite the extension component using the inside branch.
  change η.app (op V) ≫ openSubsetPresheafExtensionByInitial_comparisonUnit_app U 𝒢 (op V) =
    openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ (op V) ≫
      ((jₚ! U).map η).app (op ((openSubsetOpenFunctor U).obj V))
  rw [openSubsetPresheafExtensionByInitial_comparisonUnit_app_eq_source_transport]
  rw [openSubsetPresheafExtensionByInitial_comparisonUnit_app_eq_source_transport]
  rw [hη]
  let hs := openSubsetPresheafExtensionByInitial_source_transport_naturality U η (op V)
  have hs' :
      η.app (op V) ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U 𝒢 (op V)) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm =
        eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ (op V)) ≫
          η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
    calc
      η.app (op V) ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U 𝒢 (op V)) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm =
        (η.app (op V) ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U 𝒢 (op V))) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
        rw [← Category.assoc]
      _ =
        (eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ (op V)) ≫
            η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V)))) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
        rw [hs]
      _ =
        eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ (op V)) ≫
          η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
        simp [Category.assoc]
  -- The remaining equality is exactly naturality of `η` across the source-side transport.
  calc
    η.app (op V) ≫ eqToHom (openSubsetPresheafExtensionByInitial_source_eq U 𝒢 (op V)) ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ (op V)) ≫
        η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := hs'
    _ =
      (eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ (op V)) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV).symm) ≫
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          η.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
            eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
      simp [Category.assoc]

/-- Helper for Lemma 6.31.7: classical decidability lets the explicit descendant split on
membership in the open subset. -/
public noncomputable instance openSubsetPresheafExtensionByInitial_desc_app_decidable
    (U : Opens X) (W : (Opens X)ᵒᵖ) : Decidable (unop W ≤ U) :=
  Classical.decPred (fun W' : (Opens X)ᵒᵖ => unop W' ≤ U) W

/-- Helper for Lemma 6.31.7: the ambient target value appearing in the universal descendant is
the original ambient value after identifying `image (preimage W)` with `W`. -/
public noncomputable def openSubsetPresheafExtensionByInitial_desc_app
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢) (W : (Opens X)ᵒᵖ) :
    ((jₚ! U).obj ℱ).obj W ⟶ 𝒢.obj W :=
  if hW : unop W ≤ U then
    eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW) ≫
      τ.app (op (openSubsetPreimageOpen U (unop W))) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW)
  else
    eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) ≫
      initial.to (𝒢.obj W)

/-- Helper for Lemma 6.31.7: on the outside branch, the universal descendant factors through the
unique map from the initial object. -/
public theorem openSubsetPresheafExtensionByInitial_desc_app_from_initial
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢) (W : (Opens X)ᵒᵖ) :
    initial.to (((jₚ! U).obj ℱ).obj W) ≫
      openSubsetPresheafExtensionByInitial_desc_app U τ W =
        initial.to (𝒢.obj W) := by
  -- Regardless of the branch, this is the unique morphism from the initial object to `𝒢.obj W`.
  by_cases hW : unop W ≤ U
  · rw [openSubsetPresheafExtensionByInitial_desc_app, dif_pos hW]
    apply initial.hom_ext
  · rw [openSubsetPresheafExtensionByInitial_desc_app, dif_neg hW]
    apply initial.hom_ext

/-- Helper for Lemma 6.31.7: every morphism out of an outside branch of extension by the initial
object is the unique map from the initial object, after the canonical identification. -/
public theorem openSubsetPresheafExtensionByInitial_outside_hom_eq_initial
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {W : (Opens X)ᵒᵖ} (hW : ¬ unop W ≤ U) {A : C}
    (f : ((jₚ! U).obj ℱ).obj W ⟶ A) :
    f =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) ≫
        initial.to A := by
  -- Rewrite the outside branch to the initial object and use uniqueness of maps from `⊥_ C`.
  have hinitial :
      eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW).symm ≫
        f =
      initial.to A := by
    simpa [openSubsetPresheafExtensionByInitialObject] using
      (initial.hom_ext
        (eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW).symm ≫
          f)
        (initial.to A))
  calc
    f =
      eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) ≫
        (eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW).symm ≫
          f) := by
      simp [Category.assoc]
    _ =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) ≫
        initial.to A := by
      rw [hinitial]

/-- Helper for Lemma 6.31.7: on the inside branch, the universal descendant is natural because it
is induced by the original presheaf map and the naturality square for `τ`. -/
public theorem openSubsetPresheafExtensionByInitial_desc_inside_naturality
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : unop V ≤ U) :
    ((jₚ! U).obj ℱ).map i ≫ openSubsetPresheafExtensionByInitial_desc_app U τ W =
      openSubsetPresheafExtensionByInitial_desc_app U τ V ≫ 𝒢.map i := by
  let hW : unop W ≤ U := le_trans i.unop.le hV
  have hmap :
      ((jₚ! U).obj ℱ).map i =
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
            eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := by
    simpa [openSubsetPresheafExtensionByInitialObject] using
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le U ℱ i hV hW)
  have hτ :
      ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
          τ.app (op (openSubsetPreimageOpen U (unop W))) =
        τ.app (op (openSubsetPreimageOpen U (unop V))) ≫
          𝒢.map
            ((openSubsetOpenFunctor U).op.map
              ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op) := by
    simpa [Functor.comp_map] using
      τ.naturality (((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)
  -- Rewrite both branches into the same inside normal form and then invoke naturality of `τ`.
  rw [openSubsetPresheafExtensionByInitial_desc_app, dif_pos hW]
  rw [openSubsetPresheafExtensionByInitial_desc_app, dif_pos hV]
  rw [hmap]
  have htarget :
      𝒢.map
          ((openSubsetOpenFunctor U).op.map
            ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op) =
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) ≫
          𝒢.map i ≫
            eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW).symm :=
    openSubsetPresheafExtensionByInitial_target_map_eq U 𝒢 i hV hW
  have hτ' :
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          (ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
            τ.app (op (openSubsetPreimageOpen U (unop W)))) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW) =
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          (τ.app (op (openSubsetPreimageOpen U (unop V))) ≫
            𝒢.map
              ((openSubsetOpenFunctor U).op.map
                ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)) ≫
          eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW) := by
    exact congrArg
      (fun k ↦
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          k ≫ eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW))
      hτ
  have htarget' :
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          (τ.app (op (openSubsetPreimageOpen U (unop V))) ≫
            𝒢.map
              ((openSubsetOpenFunctor U).op.map
                ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW) =
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          (τ.app (op (openSubsetPreimageOpen U (unop V))) ≫
            (eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) ≫
              𝒢.map i ≫
                eqToHom
                  (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW).symm)) ≫
          eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW) := by
    exact congrArg
      (fun k ↦
        eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          (τ.app (op (openSubsetPreimageOpen U (unop V))) ≫ k) ≫
            eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW))
      htarget
  calc
    (eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
            eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm) ≫
        (eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW) ≫
          τ.app (op (openSubsetPreimageOpen U (unop W))) ≫
            eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW)) =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
        (ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
          τ.app (op (openSubsetPreimageOpen U (unop W)))) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW) := by
      simp [Category.assoc]
    _ =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
        (τ.app (op (openSubsetPreimageOpen U (unop V))) ≫
          𝒢.map
            ((openSubsetOpenFunctor U).op.map
              ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hW) := by
      exact hτ'
    _ =
      (eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          τ.app (op (openSubsetPreimageOpen U (unop V))) ≫
            eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV)) ≫
        𝒢.map i := by
      rw [htarget']
      simp [Category.assoc]

/-- Helper for Lemma 6.31.7: the universal descendant is natural in the ambient open. -/
public theorem openSubsetPresheafExtensionByInitial_desc_naturality
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    ((jₚ! U).obj ℱ).map i ≫ openSubsetPresheafExtensionByInitial_desc_app U τ W =
      openSubsetPresheafExtensionByInitial_desc_app U τ V ≫ 𝒢.map i := by
  by_cases hV : unop V ≤ U
  · -- On the inside branch, every term reduces to the original restriction maps on the subspace.
    exact openSubsetPresheafExtensionByInitial_desc_inside_naturality U τ i hV
  · have hmap :
        ((jₚ! U).obj ℱ).map i =
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            initial.to (((jₚ! U).obj ℱ).obj W) := by
      simpa [openSubsetPresheafExtensionByInitialObject] using
        (openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le U ℱ i hV)
    have hleft :
        ((jₚ! U).obj ℱ).map i ≫ openSubsetPresheafExtensionByInitial_desc_app U τ W =
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            initial.to (𝒢.obj W) := by
      rw [hmap]
      calc
        (eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            initial.to (((jₚ! U).obj ℱ).obj W)) ≫
            openSubsetPresheafExtensionByInitial_desc_app U τ W =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            (initial.to (((jₚ! U).obj ℱ).obj W) ≫
              openSubsetPresheafExtensionByInitial_desc_app U τ W) := by
            simp [Category.assoc]
        _ =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            initial.to (𝒢.obj W) := by
            rw [openSubsetPresheafExtensionByInitial_desc_app_from_initial]
    have hright :
        openSubsetPresheafExtensionByInitial_desc_app U τ V ≫ 𝒢.map i =
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            initial.to (𝒢.obj W) :=
      openSubsetPresheafExtensionByInitial_outside_hom_eq_initial U ℱ hV
        (openSubsetPresheafExtensionByInitial_desc_app U τ V ≫ 𝒢.map i)
    -- Outside `U`, both composites are the unique morphism out of the initial object.
    exact hleft.trans hright.symm

/-- Helper for Lemma 6.31.7: the explicit universal descendant is a natural transformation out of
the presheaf extension by the initial object. -/
public noncomputable def openSubsetPresheafExtensionByInitial_desc
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢) :
    ((jₚ! U).obj ℱ) ⟶ 𝒢 where
  app := openSubsetPresheafExtensionByInitial_desc_app U τ
  naturality := by
    intro V W i
    exact openSubsetPresheafExtensionByInitial_desc_naturality U τ i

/-- Helper for Lemma 6.31.7: composing the comparison unit with the universal descendant
recovers the original transformation on the open subspace. -/
public theorem openSubsetPresheafExtensionByInitial_desc_fac
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢) :
    openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
        Functor.whiskerLeft ((openSubsetOpenFunctor U).op)
          (openSubsetPresheafExtensionByInitial_desc U τ) =
      τ := by
  ext V
  let Vop : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ := op V
  let hV : (openSubsetOpenFunctor U).obj V ≤ U :=
    imageOpen_le_openSubset U V
  have hcomp' :
      openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ Vop ≫
          (eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
            τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
              eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV)) =
        eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ Vop) ≫
            τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
          eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) := by
    simpa [Category.assoc] using
      congrArg
        (fun k ↦
          k ≫ τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
            eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV))
        (openSubsetPresheafExtensionByInitial_comparisonUnit_app_comp_obj_eq U ℱ Vop)
  have hsRaw :
      (eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ Vop) ≫
          τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj (unop Vop))))) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) =
        (τ.app Vop ≫
            eqToHom
              (openSubsetPresheafExtensionByInitial_source_eq U
                (((openSubsetOpenFunctor U).op ⋙ 𝒢)) Vop)) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) := by
    exact congrArg
      (fun k ↦ k ≫ eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV))
      (openSubsetPresheafExtensionByInitial_source_transport_naturality U τ Vop).symm
  have hs' :
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ Vop) ≫
          τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) =
        τ.app Vop ≫
          (eqToHom
              (openSubsetPresheafExtensionByInitial_source_eq U
                (((openSubsetOpenFunctor U).op ⋙ 𝒢)) Vop) ≫
            eqToHom
              (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV)) := by
    simpa [Vop, Category.assoc] using hsRaw
  -- Evaluate the factorization on the image open and collapse the source/target transports.
  change openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ Vop ≫
      openSubsetPresheafExtensionByInitial_desc_app U τ
        (op ((openSubsetOpenFunctor U).obj V)) =
    τ.app Vop
  rw [openSubsetPresheafExtensionByInitial_desc_app, dif_pos hV]
  calc
    openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ Vop ≫
        (eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
          τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
            eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV)) =
      eqToHom (openSubsetPresheafExtensionByInitial_source_eq U ℱ Vop) ≫
          τ.app (op (openSubsetPreimageOpen U ((openSubsetOpenFunctor U).obj V))) ≫
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV) := by
      exact hcomp'
    _ =
      τ.app Vop ≫
        (eqToHom
            (openSubsetPresheafExtensionByInitial_source_eq U
              (((openSubsetOpenFunctor U).op ⋙ 𝒢)) Vop) ≫
          eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 hV)) := by
      exact hs'
    _ = τ.app Vop := by
      rw [openSubsetPresheafExtensionByInitial_target_transport_cancel U 𝒢 Vop]
      simp

/-- Helper for Lemma 6.31.7: on an ambient open contained in `U`, naturality of `γ` along the
image-preimage equality transports the component at `image (preimage W)` back to the component at
`W`. -/
public theorem openSubsetPresheafExtensionByInitial_gamma_component_transport
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (γ : ((jₚ! U).obj ℱ) ⟶ 𝒢)
    {W : Opens X} (hW : W ≤ U) :
    openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
          (op (openSubsetPreimageOpen U W)) ≫
        γ.app (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W))) ≫
      eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW) =
      eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
            (V := op W) hW).symm ≫
        γ.app (op W) := by
  -- Apply naturality of `γ` to the equality morphism `image (preimage W) ⟶ W`.
  let e :
      op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W)) ⟶ op W :=
    eqToHom (by simpa using congrArg op (image_preimageOpen_eq_of_le U W hW))
  let hSource : (openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W) ≤ U :=
    imageOpen_le_openSubset U (openSubsetPreimageOpen U W)
  have hnat := γ.naturality e
  have hmap :
      ((jₚ! U).obj ℱ).map e =
        eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hSource) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitial_source_eq U ℱ
              (op (openSubsetPreimageOpen U W))).symm ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
              (V := op W) hW).symm := by
    -- The source-side map is induced by an equality of opens, so only transports remain.
    have hmap₀ :=
      openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le U ℱ e hSource hW
    have hmorph :
        ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map e.unop).op =
          eqToHom
            (openSubsetPresheafExtensionByInitial_source_eq U ℱ
              (op (openSubsetPreimageOpen U W))).symm := by
      have hmorph₀ :
          ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map e.unop).op =
            eqToHom
              (by
                simpa [preimage_imageOpen_eq] using
                  congrArg op (preimage_imageOpen_eq U (openSubsetPreimageOpen U W))) := by
        exact Subsingleton.elim _ _
      simpa [openSubsetPresheafExtensionByInitial_source_eq, CategoryTheory.eqToHom_map] using
        congrArg ℱ.map hmorph₀
    change (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map e =
      eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hSource) ≫
        eqToHom
          (openSubsetPresheafExtensionByInitial_source_eq U ℱ
            (op (openSubsetPreimageOpen U W))).symm ≫
        eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
            (V := op W) hW).symm
    rw [hmap₀, hmorph]
  have htarget :
      𝒢.map e =
        eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW) := by
    -- The target-side map is also the map of an equality morphism.
    dsimp [e]
    simpa [openSubsetPresheafExtensionByInitial_target_eq_of_le, CategoryTheory.eqToHom_map]
      using (show 𝒢.map (eqToHom (by simpa using congrArg op (image_preimageOpen_eq_of_le U W hW))) =
          𝒢.map (eqToHom (by simpa using congrArg op (image_preimageOpen_eq_of_le U W hW))) by
            rfl)
  -- Rewrite both sides of naturality into the explicit transport normal form.
  calc
    openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
          (op (openSubsetPreimageOpen U W)) ≫
        γ.app (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W))) ≫
          eqToHom (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW) =
      openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
          (op (openSubsetPreimageOpen U W)) ≫
        (γ.app (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W))) ≫
          𝒢.map e) := by
      simpa [Category.assoc] using congrArg
        (fun k ↦
          openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
            (op (openSubsetPreimageOpen U W)) ≫
          γ.app (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W))) ≫ k) htarget.symm
    _ =
      openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
          (op (openSubsetPreimageOpen U W)) ≫
        (((jₚ! U).obj ℱ).map e ≫ γ.app (op W)) := by
      simpa [Category.assoc] using congrArg
        (fun k ↦
          openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
            (op (openSubsetPreimageOpen U W)) ≫ k) hnat.symm
    _ =
      openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
          (op (openSubsetPreimageOpen U W)) ≫
        (eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hSource) ≫
          eqToHom
            (openSubsetPresheafExtensionByInitial_source_eq U ℱ
              (op (openSubsetPreimageOpen U W))).symm ≫
          eqToHom
            (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
              (V := op W) hW).symm) ≫
        γ.app (op W) := by
      simpa [Category.assoc] using congrArg
        (fun k ↦
          openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ
            (op (openSubsetPreimageOpen U W)) ≫ k ≫ γ.app (op W)) hmap
    _ =
      eqToHom
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
            (V := op W) hW).symm ≫
        γ.app (op W) := by
      simpa [Category.assoc] using congrArg
        (fun k ↦
          k ≫
            eqToHom
              (openSubsetPresheafExtensionByInitial_source_eq U ℱ
                (op (openSubsetPreimageOpen U W))).symm ≫
            eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
                (V := op W) hW).symm ≫
            γ.app (op W))
        (openSubsetPresheafExtensionByInitial_comparisonUnit_app_comp_obj_eq U ℱ
          (op (openSubsetPreimageOpen U W)))

/-- Helper for Lemma 6.31.7: any morphism satisfying the universal factorization condition is
equal to the explicit descendant. -/
public theorem openSubsetPresheafExtensionByInitial_desc_unique
    (U : Opens X)
    {ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C} {𝒢 : X.Presheaf C}
    (τ : ℱ ⟶ (openSubsetOpenFunctor U).op ⋙ 𝒢)
    (γ : ((jₚ! U).obj ℱ) ⟶ 𝒢)
    (hγ :
      openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
          Functor.whiskerLeft ((openSubsetOpenFunctor U).op) γ =
        τ) :
    γ = openSubsetPresheafExtensionByInitial_desc U τ := by
  ext W
  by_cases hW : W ≤ U
  · let V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ := op (openSubsetPreimageOpen U W)
    have hcomp :
        openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ V ≫
            γ.app (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W))) =
          τ.app V := by
      simpa [Functor.whiskerLeft_app] using NatTrans.congr_app hγ V
    have htransport :=
      openSubsetPresheafExtensionByInitial_gamma_component_transport U γ hW
    -- Evaluate the factorization on `preimage W`, then transport the `γ`-component back to `W`.
    have hinside :
        γ.app (op W) =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
                (V := op W) hW) ≫
            τ.app V ≫
              eqToHom
                (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW) := by
      calc
        γ.app (op W) =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
                (V := op W) hW) ≫
            (openSubsetPresheafExtensionByInitial_comparisonUnit_app U ℱ V ≫
                γ.app (op ((openSubsetOpenFunctor U).obj (openSubsetPreimageOpen U W))) ≫
              eqToHom
                (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW)) := by
          rw [htransport]
          simp [Category.assoc]
        _ =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
                (V := op W) hW) ≫
            (τ.app V ≫
              eqToHom
                (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW)) := by
          simpa [Category.assoc] using congrArg
            (fun k ↦
              eqToHom
                  (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
                    (V := op W) hW) ≫
                k ≫
                  eqToHom
                    (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢
                      (W := op W) hW)) hcomp
        _ =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ
                (V := op W) hW) ≫
            τ.app V ≫
              eqToHom
                (openSubsetPresheafExtensionByInitial_target_eq_of_le U 𝒢 (W := op W) hW) := by
          simp [Category.assoc]
    simpa [openSubsetPresheafExtensionByInitial_desc, openSubsetPresheafExtensionByInitial_desc_app,
      hW, Category.assoc] using hinside
  · have hleft :
        γ.app (op W) =
          eqToHom
              (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ
                (V := op W) hW) ≫
            initial.to (𝒢.obj (op W)) :=
      openSubsetPresheafExtensionByInitial_outside_hom_eq_initial U ℱ (W := op W) hW (γ.app (op W))
    -- Outside `U`, both maps are the unique morphism from the initial object.
    simpa [openSubsetPresheafExtensionByInitial_desc, openSubsetPresheafExtensionByInitial_desc_app,
      hW] using hleft

/-- Helper for Lemma 6.31.7: the explicit extension-by-initial-object presheaf realizes the left
Kan extension along the inclusion of the open subspace. -/
public theorem openSubsetPresheafExtensionByInitial_isLeftKanExtension
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    ((jₚ! U).obj ℱ).IsLeftKanExtension
      (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ) := by
  refine ⟨⟨Limits.IsInitial.ofUniqueHom (fun Y ↦ ?_) (fun Y m ↦ ?_)⟩⟩
  · -- The universal descendant is the candidate morphism to any competing left-extension datum.
    exact StructuredArrow.homMk (openSubsetPresheafExtensionByInitial_desc U Y.hom)
      (openSubsetPresheafExtensionByInitial_desc_fac U Y.hom)
  · -- Uniqueness is exactly `openSubsetPresheafExtensionByInitial_desc_unique`.
    ext1
    exact openSubsetPresheafExtensionByInitial_desc_unique U Y.hom m.right
      (StructuredArrow.w m)

/-- Helper for Lemma 6.31.7: the owner `lan` object carries its canonical left Kan extension
structure at each presheaf. -/
public theorem openSubsetPresheafExtensionByInitial_lan_isLeftKanExtension
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    (((openSubsetOpenFunctor U).op).lan.obj ℱ).IsLeftKanExtension
      (((openSubsetOpenFunctor U).op).lanUnit.app ℱ) := by
  let L := (openSubsetOpenFunctor U).op
  letI :
      ∀ F : (extensionByZeroOpenSubsetSpace U).Presheaf C,
        L.HasLeftKanExtension F := by
    intro F
    infer_instance
  -- The owner `lan` comes equipped with its defining universal property.
  change (Functor.leftKanExtension L ℱ).IsLeftKanExtension
    (Functor.leftKanExtensionUnit L ℱ)
  infer_instance

/-- Helper for Lemma 6.31.7: the universal property of the explicit extension produces the
comparison morphism to the owner `lan` object. -/
public noncomputable def openSubsetPresheafExtensionByInitial_toLanApp
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    ((jₚ! U).obj ℱ) ⟶ (((openSubsetOpenFunctor U).op).lan.obj ℱ) :=
  let L := (openSubsetOpenFunctor U).op
  letI :
      ((jₚ! U).obj ℱ).IsLeftKanExtension
        (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ) :=
    openSubsetPresheafExtensionByInitial_isLeftKanExtension U ℱ
  ((jₚ! U).obj ℱ).descOfIsLeftKanExtension
    (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ)
    (L.lan.obj ℱ) (L.lanUnit.app ℱ)

/-- Helper for Lemma 6.31.7: the descended comparison morphism factors the explicit comparison
unit through the owner `lan` unit. -/
public theorem openSubsetPresheafExtensionByInitial_toLanApp_fac
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
        Functor.whiskerLeft ((openSubsetOpenFunctor U).op)
          (openSubsetPresheafExtensionByInitial_toLanApp U ℱ) =
      ((openSubsetOpenFunctor U).op).lanUnit.app ℱ := by
  let L := (openSubsetOpenFunctor U).op
  letI :
      ((jₚ! U).obj ℱ).IsLeftKanExtension
        (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ) :=
    openSubsetPresheafExtensionByInitial_isLeftKanExtension U ℱ
  -- This is the defining factorization returned by `descOfIsLeftKanExtension`.
  have hraw :=
    (((jₚ! U).obj ℱ).descOfIsLeftKanExtension_fac
      (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ)
      (L.lan.obj ℱ) (L.lanUnit.app ℱ))
  change openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
      Functor.whiskerLeft L (openSubsetPresheafExtensionByInitial_toLanApp U ℱ) =
    L.lanUnit.app ℱ at hraw
  exact hraw

/-- Helper for Lemma 6.31.7: the comparison morphism to `lan` is natural in the source
presheaf. -/
public theorem openSubsetPresheafExtensionByInitial_toLan_naturality
    (U : Opens X)
    {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C}
    (η : ℱ ⟶ 𝒢) :
    (jₚ! U).map η ≫ openSubsetPresheafExtensionByInitial_toLanApp U 𝒢 =
      openSubsetPresheafExtensionByInitial_toLanApp U ℱ ≫
        ((openSubsetOpenFunctor U).op).lan.map η := by
  let L := (openSubsetOpenFunctor U).op
  letI :
      ((jₚ! U).obj ℱ).IsLeftKanExtension
        (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ) :=
    openSubsetPresheafExtensionByInitial_isLeftKanExtension U ℱ
  letI :
      ((jₚ! U).obj 𝒢).IsLeftKanExtension
        (openSubsetPresheafExtensionByInitial_comparisonUnit U 𝒢) :=
    openSubsetPresheafExtensionByInitial_isLeftKanExtension U 𝒢
  -- Route correction: prove naturality once for the hom transformation before packaging any
  -- componentwise isomorphisms into a `NatIso`.
  apply ((jₚ! U).obj ℱ).hom_ext_of_isLeftKanExtension
    (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ)
  have h₁ :
      openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
          Functor.whiskerLeft L
            ((jₚ! U).map η ≫ openSubsetPresheafExtensionByInitial_toLanApp U 𝒢) =
        η ≫ L.lanUnit.app 𝒢 := by
    have hnat := congrArg
      (fun k ↦ k ≫ Functor.whiskerLeft L (openSubsetPresheafExtensionByInitial_toLanApp U 𝒢))
      (openSubsetPresheafExtensionByInitial_comparisonUnit_map_naturality U η).symm
    calc
      openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
          Functor.whiskerLeft L
            ((jₚ! U).map η ≫ openSubsetPresheafExtensionByInitial_toLanApp U 𝒢) =
        (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
            Functor.whiskerLeft L ((jₚ! U).map η)) ≫
          Functor.whiskerLeft L (openSubsetPresheafExtensionByInitial_toLanApp U 𝒢) := by
        rw [Functor.whiskerLeft_comp, Category.assoc]
        rfl
      _ =
        (η ≫ openSubsetPresheafExtensionByInitial_comparisonUnit U 𝒢) ≫
          Functor.whiskerLeft L (openSubsetPresheafExtensionByInitial_toLanApp U 𝒢) := by
        exact hnat
      _ = η ≫ L.lanUnit.app 𝒢 := by
        rw [Category.assoc]
        exact congrArg (fun k ↦ η ≫ k)
          (openSubsetPresheafExtensionByInitial_toLanApp_fac U 𝒢)
  have h₂ :
      η ≫ L.lanUnit.app 𝒢 =
        L.lanUnit.app ℱ ≫ Functor.whiskerLeft L (L.lan.map η) := by
    -- The owner `lanUnit` already satisfies the required naturality relation.
    simpa [L] using (L.lanUnit.naturality η)
  have h₃ :
      L.lanUnit.app ℱ ≫ Functor.whiskerLeft L (L.lan.map η) =
        openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
          Functor.whiskerLeft L
            (openSubsetPresheafExtensionByInitial_toLanApp U ℱ ≫ L.lan.map η) := by
    calc
      L.lanUnit.app ℱ ≫ Functor.whiskerLeft L (L.lan.map η) =
        (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
            Functor.whiskerLeft L (openSubsetPresheafExtensionByInitial_toLanApp U ℱ)) ≫
          Functor.whiskerLeft L (L.lan.map η) := by
        exact congrArg (fun k ↦ k ≫ Functor.whiskerLeft L (L.lan.map η))
          (openSubsetPresheafExtensionByInitial_toLanApp_fac U ℱ).symm
      _ =
        openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
          (Functor.whiskerLeft L (openSubsetPresheafExtensionByInitial_toLanApp U ℱ) ≫
            Functor.whiskerLeft L (L.lan.map η)) := by
        simp [Category.assoc]
      _ =
        openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
          Functor.whiskerLeft L
            (openSubsetPresheafExtensionByInitial_toLanApp U ℱ ≫ L.lan.map η) := by
        rw [Functor.whiskerLeft_comp]
        rfl
  exact h₁.trans (h₂.trans h₃)

/-- Helper for Lemma 6.31.7: packaging the objectwise descendants gives a natural transformation
from the explicit extension functor to the owner `lan`. -/
public noncomputable def openSubsetPresheafExtensionByInitial_toLan
    (U : Opens X) :
    jₚ! U ⟶
      (((openSubsetOpenFunctor U).op).lan :
        (extensionByZeroOpenSubsetSpace U).Presheaf C ⥤ X.Presheaf C) where
  app ℱ := openSubsetPresheafExtensionByInitial_toLanApp U ℱ
  naturality {_ _} η := openSubsetPresheafExtensionByInitial_toLan_naturality U η

/-- Helper for Lemma 6.31.7: the packaged natural transformation still satisfies the same
factorization identity against the comparison unit. -/
public theorem openSubsetPresheafExtensionByInitial_toLan_app_fac
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ ≫
        Functor.whiskerLeft ((openSubsetOpenFunctor U).op)
          ((openSubsetPresheafExtensionByInitial_toLan U).app ℱ) =
      ((openSubsetOpenFunctor U).op).lanUnit.app ℱ := by
  -- This is the objectwise factorization rewritten through the packaged natural transformation.
  simpa [openSubsetPresheafExtensionByInitial_toLan] using
    openSubsetPresheafExtensionByInitial_toLanApp_fac U ℱ

/-- Helper for Lemma 6.31.7: each component of the packaged comparison to `lan` is an
isomorphism because both sides realize the same left Kan extension. -/
public theorem openSubsetPresheafExtensionByInitial_toLan_app_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    IsIso ((openSubsetPresheafExtensionByInitial_toLan U).app ℱ) := by
  let L := (openSubsetOpenFunctor U).op
  letI :
      ((jₚ! U).obj ℱ).IsLeftKanExtension
        (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ) :=
    openSubsetPresheafExtensionByInitial_isLeftKanExtension U ℱ
  have hLan : (L.lan.obj ℱ).IsLeftKanExtension (L.lanUnit.app ℱ) :=
    openSubsetPresheafExtensionByInitial_lan_isLeftKanExtension U ℱ
  -- The uniqueness part of the universal property upgrades the comparison morphism to an iso.
  exact (Functor.isLeftKanExtension_iff_isIso
    ((openSubsetPresheafExtensionByInitial_toLan U).app ℱ)
    (openSubsetPresheafExtensionByInitial_comparisonUnit U ℱ)
    (L.lanUnit.app ℱ)
    (openSubsetPresheafExtensionByInitial_toLan_app_fac U ℱ)).1 hLan

/-- Helper for Lemma 6.31.7: `asIso` can use the objectwise invertibility of the packaged
comparison to `lan`. -/
public noncomputable instance openSubsetPresheafExtensionByInitial_toLan_app_isIso_inst
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    IsIso ((openSubsetPresheafExtensionByInitial_toLan U).app ℱ) :=
  openSubsetPresheafExtensionByInitial_toLan_app_isIso U ℱ

/-- Helper for Lemma 6.31.7: the hom components built from the packaged `toLan` transformation
already satisfy the functorial naturality equation needed for `NatIso.ofComponents`. -/
public theorem openSubsetPresheafExtensionByInitialObjectIsoLan_naturality
    (U : Opens X)
    {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C}
    (η : ℱ ⟶ 𝒢) :
    (jₚ! U).map η ≫
        (asIso ((openSubsetPresheafExtensionByInitial_toLan U).app 𝒢)).hom =
      (asIso ((openSubsetPresheafExtensionByInitial_toLan U).app ℱ)).hom ≫
        (((openSubsetOpenFunctor U).op).lan.map η) := by
  -- The naturality of the `NatIso` hom is just the naturality of the underlying hom
  -- transformation, rewritten through `asIso`.
  simpa using (openSubsetPresheafExtensionByInitial_toLan U).naturality η

-- Proof sketch: for an open immersion, the explicit extension-by-initial-object presheaf functor
-- agrees with the canonical left Kan extension along the induced functor on opens.
/-- The explicit presheaf extension-by-initial-object functor agrees with the owner left Kan
extension along the inclusion of opens. -/
public noncomputable abbrev openSubsetPresheafExtensionByInitialObjectIsoLan
    (U : Opens X) :
    jₚ! U ≅
      (((openSubsetOpenFunctor U).op).lan :
        (extensionByZeroOpenSubsetSpace U).Presheaf C ⥤ X.Presheaf C) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((openSubsetPresheafExtensionByInitial_toLan U).app ℱ))
    (fun η ↦ openSubsetPresheafExtensionByInitialObjectIsoLan_naturality U η)
/-- Lemma 6.31.7 (1): extension by the initial object on presheaves is left adjoint to
restriction to the open subset `U`. -/
noncomputable abbrev presheafExtensionByInitialAdjunction (U : Opens X) :
    jₚ! U ⊣
      TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
  ((((openSubsetOpenFunctor U).op).lanAdjunction C).ofNatIsoRight
      (IsOpenMap.pullbackIso U.isOpenEmbedding.isOpenMap).symm).ofNatIsoLeft
    (openSubsetPresheafExtensionByInitialObjectIsoLan U).symm

-- Proof sketch: this is the standard fact that the unit of a fully faithful left adjoint along
-- an open immersion is invertible, transported through the canonical adjunction above.
/-- The unit of the presheaf extension-by-initial adjunction is an isomorphism on every presheaf
over `U`. -/
theorem presheafExtensionByInitialAdjunction_unit_app_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    IsIso ((presheafExtensionByInitialAdjunction U).unit.app ℱ) := by
  -- The transported unit is a composite of isomorphisms: the `lanAdjunction` unit for the fully
  -- faithful open-immersion functor, the pullback comparison isomorphism, and the chosen
  -- comparison from the explicit extension-by-initial-object functor to the owner `lan`.
  let L := (openSubsetOpenFunctor U).op
  letI : L.Full := by
    dsimp [L]
    infer_instance
  letI : L.Faithful := by
    dsimp [L]
    infer_instance
  letI : L.HasPointwiseLeftKanExtension ℱ := by
    intro Y
    infer_instance
  letI : ∀ F : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ ⥤ C, L.HasLeftKanExtension F := by
    intro F
    infer_instance
  rw [presheafExtensionByInitialAdjunction]
  dsimp [Adjunction.ofNatIsoLeft, Adjunction.ofNatIsoRight]
  rw [Functor.lanAdjunction_unit]
  haveI : IsIso (L.lanUnit.app ℱ) := by
    infer_instance
  have ePullback :
      IsIso ((IsOpenMap.pullbackIso U.isOpenEmbedding.isOpenMap).inv.app (L.lan.obj ℱ)) := by
    infer_instance
  letI := ePullback
  haveI :
      IsIso
        ((TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).map
          ((openSubsetPresheafExtensionByInitialObjectIsoLan U).inv.app ℱ)) := by
    infer_instance
  refine IsIso.comp_isIso' ?_ inferInstance
  refine IsIso.comp_isIso' ?_ ?_
  · simpa [L] using (show IsIso (L.lanUnit.app ℱ) from inferInstance)
  · simpa [L] using ePullback

public instance presheafExtensionByInitial_unit_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    IsIso ((presheafExtensionByInitialAdjunction U).unit.app ℱ) :=
  presheafExtensionByInitialAdjunction_unit_app_isIso U ℱ

/-- Lemma 6.31.7 (4): on presheaves over `U`, the unit
`\mathrm{id} \to j_p j_{p!}` is a natural isomorphism. -/
noncomputable abbrev presheafExtensionByInitialUnitIso (U : Opens X) :
    𝟭 ((extensionByZeroOpenSubsetSpace U).Presheaf C) ≅
      jₚ! U ⋙
        TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((presheafExtensionByInitialAdjunction U).unit.app ℱ))
    (by
      intro ℱ 𝒢 f
      simpa using (presheafExtensionByInitialAdjunction U).unit.naturality f)

-- Proof sketch: `presheafExtensionByInitialUnitIso` is defined by applying `asIso` to each
-- component of the adjunction unit, so its hom component is exactly that unit map.
/-- The hom component of the presheaf unit isomorphism is the unit morphism of the adjunction. -/
theorem presheafExtensionByInitialUnitIso_hom_app
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    (presheafExtensionByInitialUnitIso U).hom.app ℱ =
      (presheafExtensionByInitialAdjunction U).unit.app ℱ := by
  -- This is immediate from the definition using `NatIso.ofComponents` and `asIso`.
  rfl

section Sheaf

variable {FC : C → C → Type w} {CC : C → Type w}
variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{w} C FC]
variable [HasLimits C] [PreservesLimits (CategoryTheory.forget C)]
variable [PreservesFilteredColimits (CategoryTheory.forget C)]
variable [(CategoryTheory.forget C).ReflectsIsomorphisms]
variable [HasWeakSheafify (Opens.grothendieckTopology X) C]

-- Proof sketch: sheafifying the presheaf extension-by-initial-object construction gives the same
-- left adjoint as the canonical sheaf pullback construction attached to the open inclusion.
/-- The explicit sheaf extension-by-initial-object functor agrees with the owner sheaf-pullback
construction for the inclusion of opens. -/
public noncomputable def openSubsetSheafExtensionByInitialObjectIsoSheafPullback
    (U : Opens X) :
    j! U ≅
      Functor.sheafPullbackConstruction.sheafPullback
        U.isOpenEmbedding.functor C
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X) := by
  simpa [openSubsetSheafExtensionByInitialObject,
    Functor.sheafPullbackConstruction.sheafPullback] using
    Functor.isoWhiskerLeft (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U))
      (Functor.isoWhiskerRight (openSubsetPresheafExtensionByInitialObjectIsoLan U)
        (CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C))

/-- Helper for Lemma 6.31.7: the owner sheaf-pullback composite reduces to the identity after
transporting the presheaf unit isomorphism through sheafification and restriction. -/
public noncomputable abbrev sheafExtensionByInitial_ownerCompIso
    (U : Opens X)
    [(openSubsetOpenFunctor U).IsContinuous
      (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Opens.grothendieckTopology X)]
    [(openSubsetOpenFunctor U).IsCocontinuous
      (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
      (Opens.grothendieckTopology X)] :
    Functor.sheafPullbackConstruction.sheafPullback
        (openSubsetOpenFunctor U) C
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X) ⋙
      (openSubsetOpenFunctor U).sheafPushforwardContinuous C
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X) ≅
      𝟭 ((extensionByZeroOpenSubsetSpace U).Sheaf C) :=
  let JU : GrothendieckTopology (Opens (extensionByZeroOpenSubsetSpace U)) :=
    Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U)
  let JX : GrothendieckTopology (Opens X) :=
    Opens.grothendieckTopology X
  let F : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ ⥤ (Opens X)ᵒᵖ :=
    (openSubsetOpenFunctor U).op
  let presheafLanUnitIso :
      𝟭 ((extensionByZeroOpenSubsetSpace U).Presheaf C) ≅
        F.lan ⋙ (Functor.whiskeringLeft _ _ C).obj F :=
    (presheafExtensionByInitialUnitIso U) ≪≫
      Functor.isoWhiskerRight (openSubsetPresheafExtensionByInitialObjectIsoLan U)
        (TopCat.Presheaf.pullback C (extensionByZeroOpenSubsetInclusion U)) ≪≫
      Functor.isoWhiskerLeft F.lan (IsOpenMap.pullbackIso U.isOpenEmbedding.isOpenMap)
  Functor.associator
      ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)) ⋙ F.lan)
      (CategoryTheory.presheafToSheaf JX C)
      ((openSubsetOpenFunctor U).sheafPushforwardContinuous C JU JX) ≪≫
    Functor.isoWhiskerLeft
      ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)) ⋙ F.lan)
      (((openSubsetOpenFunctor U).pushforwardContinuousSheafificationCompatibility
        C JU JX).symm) ≪≫
    (Functor.associator
        (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U))
        F.lan
        (((Functor.whiskeringLeft _ _ C).obj F) ⋙ CategoryTheory.presheafToSheaf JU C)) ≪≫
    Functor.isoWhiskerLeft
      (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U))
      (Functor.associator F.lan ((Functor.whiskeringLeft _ _ C).obj F)
        (CategoryTheory.presheafToSheaf JU C)).symm ≪≫
    Functor.isoWhiskerLeft
      (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U))
      (Functor.isoWhiskerRight presheafLanUnitIso.symm
        (CategoryTheory.presheafToSheaf JU C)) ≪≫
    Functor.isoWhiskerLeft
      (TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U))
      (Functor.leftUnitor (CategoryTheory.presheafToSheaf JU C)) ≪≫
    (CategoryTheory.sheafificationNatIso JU C).symm

/-- Lemma 6.31.7 (2): extension by the initial object on sheaves is left adjoint to restriction
to the open subset `U`. -/
noncomputable abbrev sheafExtensionByInitialAdjunction (U : Opens X) :
    j! U ⊣
      TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        U.isOpenEmbedding.functor C
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X)).ofNatIsoRight
      (Topology.IsOpenEmbedding.sheafPullbackIso C U.isOpenEmbedding).symm).ofNatIsoLeft
      (openSubsetSheafExtensionByInitialObjectIsoSheafPullback U).symm

-- Proof sketch: the sheaf adjunction is obtained from the canonical sheaf-pullback adjunction,
-- whose unit is invertible on the essential image determined by the open immersion.
/-- The unit of the sheaf extension-by-initial adjunction is an isomorphism on every sheaf over
`U`. -/
theorem sheafExtensionByInitialAdjunction_unit_app_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) :
    IsIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ) := by
  let JU : GrothendieckTopology (Opens (extensionByZeroOpenSubsetSpace U)) :=
    Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U)
  let JX : GrothendieckTopology (Opens X) :=
    Opens.grothendieckTopology X
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  letI :
      (openSubsetOpenFunctor U).IsCocontinuous
        (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
        (Opens.grothendieckTopology X) := inferInstance
  let ownerR :=
    (openSubsetOpenFunctor U).sheafPushforwardContinuous C JU JX
  let ownerL :=
    Functor.sheafPullbackConstruction.sheafPullback
      (openSubsetOpenFunctor U) C JU JX
  have ownerCompIso :
      ownerL ⋙ ownerR ≅ 𝟭 ((extensionByZeroOpenSubsetSpace U).Sheaf C) := by
    -- Reuse the extracted owner composite iso instead of rebuilding the transport chain inline.
    simpa [ownerL, ownerR, JU, JX] using sheafExtensionByInitial_ownerCompIso (U := U) (C := C)
  haveI :
      IsIso
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
            (openSubsetOpenFunctor U) C JU JX).unit.app ℱ) := by
    let _ :=
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (openSubsetOpenFunctor U) C JU JX).isIso_unit_of_iso ownerCompIso
    infer_instance
  rw [sheafExtensionByInitialAdjunction]
  dsimp [Adjunction.ofNatIsoLeft, Adjunction.ofNatIsoRight]
  have ePullback :
      IsIso ((Topology.IsOpenEmbedding.sheafPullbackIso C U.isOpenEmbedding).inv.app (ownerL.obj ℱ)) := by
    infer_instance
  letI := ePullback
  haveI :
      IsIso
        ((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).map
          ((openSubsetSheafExtensionByInitialObjectIsoSheafPullback U).inv.app ℱ)) := by
    infer_instance
  -- The explicit unit is the owner unit followed by the two comparison isomorphisms.
  refine IsIso.comp_isIso' ?_ inferInstance
  refine IsIso.comp_isIso' ?_ ?_
  · simpa [JU, JX, ownerL] using
      (show
        IsIso
          ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
              (openSubsetOpenFunctor U) C JU JX).unit.app ℱ) from inferInstance)
  · simpa [ownerL] using ePullback

public instance sheafExtensionByInitial_unit_isIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) :
    IsIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ) :=
  sheafExtensionByInitialAdjunction_unit_app_isIso U ℱ

/-- Lemma 6.31.7 (5): on sheaves over `U`, the unit
`\mathrm{id} \to j^{-1} j_!` is a natural isomorphism. -/
noncomputable abbrev sheafExtensionByInitialUnitIso (U : Opens X) :
    𝟭 ((extensionByZeroOpenSubsetSpace U).Sheaf C) ≅
      j! U ⋙
        TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ))
    (by
      intro ℱ 𝒢 f
      simpa using (sheafExtensionByInitialAdjunction U).unit.naturality f)

-- Proof sketch: `sheafExtensionByInitialUnitIso` is assembled from the adjunction unit by
-- applying `asIso` componentwise, so its hom component is the unit map.
/-- The hom component of the sheaf unit isomorphism is the unit morphism of the adjunction. -/
theorem sheafExtensionByInitialUnitIso_hom_app
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) :
    (sheafExtensionByInitialUnitIso U).hom.app ℱ =
      (sheafExtensionByInitialAdjunction U).unit.app ℱ := by
  -- This is immediate from the componentwise `asIso` construction of the unit isomorphism.
  rfl

section Stalks

/-- Helper for Lemma 6.31.7: transporting an isomorphism across an equality of targets and then
composing with the corresponding `eqToIso` recovers the original isomorphism. -/
public theorem cast_iso_comp_eqToIso {A B B' : C} (p : B = B') (e : A ≅ B) :
    cast (congrArg (fun Z : C => A ≅ Z) p) e ≪≫ eqToIso p.symm = e := by
  cases p
  simp

public noncomputable def outsideNeighbourhoodDiagramIsoConstInitial
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) {x : X}
    (hx : x ∉ (U : Set X)) :
    (OpenNhds.inclusion x).op ⋙ ((jₚ! U).obj ℱ) ≅
      (Functor.const (OpenNhds x)ᵒᵖ).obj (⊥_ C) :=
  NatIso.ofComponents
    (fun V ↦
      eqToIso (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ
        (show ¬ unop (op (unop V).1) ≤ U from by
          intro h
          exact hx (h (unop V).2))))
    (by
      intro V W i
      have hV : ¬ unop (op (unop V).1) ≤ U := by
        intro h
        exact hx (h (unop V).2)
      have hW : ¬ unop (op (unop W).1) ≤ U := by
        intro h
        exact hx (h (unop W).2)
      -- Rewrite the source map on the outside branch, where every map is forced from `⊥_ C`.
      change ((jₚ! U).obj ℱ).map ((OpenNhds.inclusion x).op.map i) ≫
            eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) =
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            𝟙 (⊥_ C)
      have hmap :
          ((jₚ! U).obj ℱ).map ((OpenNhds.inclusion x).op.map i) =
            eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
              initial.to (((jₚ! U).obj ℱ).obj (op (unop W).1)) := by
        simpa [openSubsetPresheafExtensionByInitialObject] using
          (openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le U ℱ
            ((OpenNhds.inclusion x).op.map i) hV)
      rw [hmap]
      have hcomp :
          initial.to (((jₚ! U).obj ℱ).obj (op (unop W).1)) ≫
              eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hW) =
            𝟙 (⊥_ C) := by
        apply initial.hom_ext
      have hcomp' :=
        congrArg
          (fun k ↦
            eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
              k)
          hcomp
      simpa only [← Category.assoc, Category.comp_id] using hcomp')

public noncomputable def openSubsetPresheafExtensionByInitialObject_stalk_isInitial_of_not_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) {x : X}
    (hx : x ∉ (U : Set X)) :
    IsInitial (((jₚ! U).obj ℱ).stalk x) := by
  refine IsInitial.ofIso initialIsInitial ?_
  exact (CategoryTheory.Limits.colimitConstInitial).symm ≪≫
    (HasColimit.isoOfNatIso (outsideNeighbourhoodDiagramIsoConstInitial U ℱ hx)).symm

-- Proof sketch: outside `U`, every sufficiently small neighbourhood still misses `U`, so the
-- extension-by-initial presheaf is constantly the initial object on the filtered diagram defining
-- the stalk.
/-- If `x ∉ U`, then the stalk of `j_! ℱ` at `x` is an initial object of `C`. -/
noncomputable def sheafExtensionByInitial_stalk_isInitial_of_not_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) {x : X}
    (hx : x ∉ (U : Set X)) :
    IsInitial (((j! U).obj ℱ).presheaf.stalk x) := by
  let m := (TopCat.Presheaf.stalkFunctor C x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      ((jₚ! U).obj ℱ.1))
  have hm : IsIso m := by
    simpa [m] using
      (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x C
        ((jₚ! U).obj ℱ.1))
  change IsInitial
    (TopCat.Presheaf.stalk
      (CategoryTheory.sheafify (Opens.grothendieckTopology X)
        ((jₚ! U).obj ℱ.1))
      x)
  let e :
      TopCat.Presheaf.stalk ((jₚ! U).obj ℱ.1) x ≅
        TopCat.Presheaf.stalk
          (CategoryTheory.sheafify (Opens.grothendieckTopology X)
            ((jₚ! U).obj ℱ.1))
          x := by
    exact @CategoryTheory.asIso _ _ _ _ m hm
  exact IsInitial.ofIso
    (openSubsetPresheafExtensionByInitialObject_stalk_isInitial_of_not_mem U ℱ.1 hx)
    e

-- Proof sketch: the unit `ℱ ⟶ j^{-1} j_! ℱ` is an isomorphism, and taking stalks preserves this;
-- for an open inclusion, the stalk of the pullback sheaf is the stalk of `j_! ℱ` at the
-- corresponding point of `X`.
/-- At a point of `U`, the stalk of `j_! ℱ` at the corresponding point of `X` is canonically
isomorphic to the stalk of `ℱ`. -/
public noncomputable def sheafExtensionByInitial_stalkIsoAtPoint
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C)
    (x : extensionByZeroOpenSubsetSpace U) :
    (((j! U).obj ℱ).presheaf.stalk
      (extensionByZeroOpenSubsetInclusion U x)) ≅
      ℱ.presheaf.stalk x := by
  let e :
      (((j! U).obj ℱ).presheaf.stalk
        (extensionByZeroOpenSubsetInclusion U x)) ≅
        (((TopCat.Sheaf.pullback C (extensionByZeroOpenSubsetInclusion U)).obj
          ((j! U).obj ℱ)).presheaf.stalk x) :=
    TopCat.Sheaf.stalkPullbackIso (extensionByZeroOpenSubsetInclusion U)
      ((j! U).obj ℱ) x
  exact
    e ≪≫
    ((TopCat.Presheaf.stalkFunctor C x).mapIso
      ((TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U)).mapIso
        (asIso ((sheafExtensionByInitialAdjunction U).unit.app ℱ)))).symm

open Classical in
/-- Lemma 6.31.7 (3): for a point `x` of `X`, the stalk of `j_! ℱ` is canonically identified
with the stalk of `ℱ` when `x ∈ U`, and with the initial object of `C` when `x ∉ U`. -/
noncomputable def sheafExtensionByInitial_stalkIso
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C) (x : X) :
    (((j! U).obj ℱ).presheaf.stalk x) ≅
      if hx : x ∈ (U : Set X) then
        ℱ.presheaf.stalk ⟨x, hx⟩
      else
        ⊥_ C := by
  by_cases hx : x ∈ (U : Set X)
  · simpa [hx] using sheafExtensionByInitial_stalkIsoAtPoint U ℱ ⟨x, hx⟩
  · simpa [hx] using
      (initialIsoIsInitial
        (sheafExtensionByInitial_stalk_isInitial_of_not_mem U ℱ hx)).symm

-- Proof sketch: compose the by-cases isomorphism `sheafExtensionByInitial_stalkIso` with the
-- canonical identification of the inside branch of the `if`, then compare with the explicit stalk
-- isomorphism at the corresponding point of the open subspace.
/-- On the branch `x ∈ U`, the global stalk comparison agrees with the explicit stalk
identification at the corresponding point of the open subspace. -/
theorem sheafExtensionByInitial_stalkIso_comp_eq_of_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C)
    (x : X) (hx : x ∈ (U : Set X)) :
    sheafExtensionByInitial_stalkIso U ℱ x ≪≫
        eqToIso (by simp [hx]) =
      sheafExtensionByInitial_stalkIsoAtPoint U ℱ ⟨x, hx⟩ := by
  -- TODO for Lemma 6.31.7: unfold `sheafExtensionByInitial_stalkIso`, choose the inside branch,
  -- and remove the remaining proof-irrelevance cast between the two subtype points over `x`.
  classical
  simp [sheafExtensionByInitial_stalkIso, hx]
  have hsub :
      (⟨x, by simpa using hx⟩ : extensionByZeroOpenSubsetSpace U) = ⟨x, hx⟩ := by
    ext
    rfl
  cases hsub
  simpa using
    cast_iso_comp_eqToIso
      (p := by simp [hx])
      (e := sheafExtensionByInitial_stalkIsoAtPoint U ℱ ⟨x, hx⟩)

-- Proof sketch: compose the by-cases isomorphism `sheafExtensionByInitial_stalkIso` with the
-- canonical identification of the outside branch of the `if`, then compare with the unique
-- isomorphism coming from the initiality of the stalk.
/-- On the branch `x ∉ U`, the global stalk comparison agrees with the canonical isomorphism from
the stalk to the initial object. -/
theorem sheafExtensionByInitial_stalkIso_comp_eq_of_not_mem
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Sheaf C)
    (x : X) (hx : x ∉ (U : Set X)) :
    sheafExtensionByInitial_stalkIso U ℱ x ≪≫
        eqToIso (by simp [hx]) =
      (initialIsoIsInitial
        (sheafExtensionByInitial_stalk_isInitial_of_not_mem U ℱ hx)).symm := by
  -- TODO for Lemma 6.31.7: unfold `sheafExtensionByInitial_stalkIso`, choose the outside branch,
  -- and simplify the residual proof-irrelevance cast on the initial-object isomorphism.
  classical
  simp [sheafExtensionByInitial_stalkIso, hx]
  have hproof : (show x ∉ (U : Set X) from by simpa using hx) = hx := Subsingleton.elim _ _
  cases hproof
  simpa using
    cast_iso_comp_eqToIso
      (p := by simp [hx])
      (e := (initialIsoIsInitial
        (sheafExtensionByInitial_stalk_isInitial_of_not_mem U ℱ hx)).symm)

end Stalks
end Sheaf
end

end OpenSubsetExtensionByInitial
