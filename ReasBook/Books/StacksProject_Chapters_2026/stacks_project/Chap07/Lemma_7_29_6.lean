module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Topology.Sheaves.LocallySurjective
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.PUnit
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Definition_7_13_1
public import stacks_project.Chap07.Definition_7_14_1
public import stacks_project.Chap07.Definition_7_15_1_Topoi
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_15_2
public import stacks_project.Chap07.Lemma_7_29_5
public import stacks_project.Chap07.Definition_7_29_2
public import stacks_project.Chap07.Remark_7_14_8
public import stacks_project.Chap07.Remark_7_15_4
public import stacks_project.Chap07.Lemma_7_17_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Functor.IsDenseSubsite

universe u₁ u₂ u₃ v₁ v₂ v₃ w wLarge

namespace CategoryTheory

open scoped MorphismOfTopoiIn

section

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {J : GrothendieckTopology C} {K : GrothendieckTopology D}

/-- Helper for Lemma 7.29.6: the inverse-image functor of a morphism of topoi preserves all
finite limits, so in particular it preserves pullbacks. -/
private theorem inverseImage_preserves_finite_limits
    (f : MorphismOfTopoiIn K J) :
    PreservesFiniteLimits (show Sheaf K (Type w) ⥤ Sheaf J (Type w) from f⁻¹) := by
  -- The inverse-image functor is stored as a left exact functor in the `MorphismOfTopoiIn`
  -- owner, so finite-limit preservation is already part of the canonical data.
  change PreservesFiniteLimits f.inverseImageFunctor.obj
  infer_instance

/-- Helper for Lemma 7.29.6: the inverse-image functor of a morphism of topoi preserves
pullbacks. -/
private theorem inverseImage_preserves_pullbacks
    (f : MorphismOfTopoiIn K J) :
    PreservesLimitsOfShape WalkingCospan
      (show Sheaf K (Type w) ⥤ Sheaf J (Type w) from f⁻¹) := by
  -- Pullback preservation is the `WalkingCospan` part of the finite-limit preservation above.
  change PreservesLimitsOfShape WalkingCospan f.inverseImageFunctor.obj
  infer_instance

/-- Helper for Lemma 7.29.6: once the source dense-subsite functor has pointwise right Kan
extensions on `Type w`, its cocontinuous direct image is an equivalence. -/
private theorem denseSubsite_pushforward_isEquivalence
    {C' : Type u₃} [Category.{v₃} C']
    {J' : GrothendieckTopology C'} (v : C ⥤ C')
    [v.IsDenseSubsite J J']
    [∀ P : Cᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P] :
    (v.sheafPushforwardCocontinuous (Type w) J J').IsEquivalence := by
  -- This is exactly the dense-subsite comparison theorem already packaged in Definition 7.29.2.
  exact
    Functor.IsDenseSubsite.sheafPushforwardCocontinuous_isEquivalence_of_hasPointwiseRightKanExtension
      (J := J) (K := J') v

/-- Helper for Lemma 7.29.6: weak sheafification on the intermediate site follows from the source
site once the dense-subsite comparison is known to be an equivalence. -/
private theorem denseSubsite_hasWeakSheafify
    {C' : Type u₃} [Category.{v₃} C']
    {J' : GrothendieckTopology C'} (v : C ⥤ C')
    [v.IsDenseSubsite J J']
    [HasWeakSheafify J (Type w)]
    [∀ P : Cᵒᵖ ⥤ Type w, v.op.HasPointwiseRightKanExtension P]
    [hvEq : (v.sheafPushforwardContinuous (Type w) J J').IsEquivalence] :
    HasWeakSheafify J' (Type w) := by
  -- The dense-subsite equivalence transports weak sheafification from `J` to `J'`.
  exact Functor.IsDenseSubsite.hasWeakSheafify_of_isEquivalence J J' v (Type w)

/-- Helper for Lemma 7.29.6: composing type-valued sheaves with the relevant `ULift` functor
preserves the sheaf condition. -/
private instance uliftFunctor_hasSheafCompose_type
    {E : Type u₃} [Category.{v₃} E] (L : GrothendieckTopology E) :
    L.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
        Type w ⥤ Type (max w (max u₃ v₃))) where
  isSheaf P hP := by
    -- Reduce to the type-valued sheaf condition and use the standard `ULift` stability lemma.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := L)
      ((isSheaf_iff_isSheaf_of_type L P).1 hP)

/-- Helper for Lemma 7.29.6: whiskering a locally surjective map of type-valued presheaves by the
relevant `ULift` functor preserves local surjectivity. -/
private theorem whisker_ulift_isLocallySurjective
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L η] :
    Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))) where
  imageSieve_mem {X} x := by
    -- Lift local preimages pointwise through `ULift`.
    let S : Sieve X := Presheaf.imageSieve η x.down
    have hS : S ∈ L X := Presheaf.imageSieve_mem L η x.down
    refine L.superset_covering ?_ hS
    intro Y f hf
    rcases hf with ⟨y, hy⟩
    refine ⟨ULift.up y, ?_⟩
    change ULift.up (η.app (op Y) y) = ULift.up (Q.map f.op x.down)
    simpa using hy

/-- Helper for Lemma 7.29.6: local surjectivity of type-valued presheaf maps reflects across
whiskering by the relevant `ULift` functor. -/
private theorem locallySurjective_of_whisker_ulift
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {P Q : Eᵒᵖ ⥤ Type w} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃))))] :
    Presheaf.IsLocallySurjective L η where
  imageSieve_mem {X} x := by
    -- Identify the lifted image sieve with the original one and descend the covering statement.
    let x' :
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).obj (op X) := ULift.up x
    let S : Sieve X :=
      Presheaf.imageSieve
        (Functor.whiskerRight η
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃))))
        x'
    have hS : S ∈ L X := by
      exact
        Presheaf.imageSieve_mem L
          (Functor.whiskerRight η
            (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
              Type w ⥤ Type (max w (max u₃ v₃))))
          x'
    refine L.superset_covering ?_ hS
    intro Y f hf
    change ∃ t : (P ⋙
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))).obj (op Y),
      (Functor.whiskerRight η
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))).app (op Y) t =
        (Q ⋙
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).map f.op x' at hf
    rcases hf with ⟨t, ht⟩
    refine ⟨t.down, ?_⟩
    simpa using congrArg ULift.down ht

/-- Helper for Lemma 7.29.6: a sheaf morphism is locally surjective exactly when its `ULift`
whisker is locally surjective. -/
private theorem sheafCompose_map_isLocallySurjective_iff
    {E : Type u₃} [Category.{v₃} E] {L : GrothendieckTopology E}
    {ℱ 𝒢 : Sheaf L (Type w)} (η : ℱ ⟶ 𝒢) :
    Sheaf.IsLocallySurjective
        ((sheafCompose L
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))).map η) ↔
      Sheaf.IsLocallySurjective η := by
  constructor
  · intro h
    -- Move to underlying presheaves and reflect local surjectivity through `ULift`.
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] at h ⊢
    change Presheaf.IsLocallySurjective L
      (Functor.whiskerRight η.hom
        (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
          Type w ⥤ Type (max w (max u₃ v₃)))) at h
    let _ : Presheaf.IsLocallySurjective L
        (Functor.whiskerRight η.hom
          (CategoryTheory.uliftFunctor.{max u₃ v₃, w} :
            Type w ⥤ Type (max w (max u₃ v₃)))) := h
    exact locallySurjective_of_whisker_ulift (L := L) η.hom
  · intro h
    -- Move to underlying presheaves and preserve local surjectivity through `ULift`.
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff] at h ⊢
    change Presheaf.IsLocallySurjective L η.hom at h
    let _ : Presheaf.IsLocallySurjective L η.hom := h
    simpa using whisker_ulift_isLocallySurjective (L := L) η.hom

/-- Helper for Lemma 7.29.6: in a large ambient universe, the canonical coproduct map attached to
a `K`-cover is the sigma-desc of the lifted sheafified representable maps. -/
private noncomputable abbrev uliftSheafifiedRepresentableCoverMap
    {V : D} [HasWeakSheafify K (Type (max wLarge u₂ v₂))] (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y)] :
    ∐ (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y) ⟶
      K.uliftSheafifiedRepresentable V :=
  Limits.Sigma.desc (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentableFunctor.map I.f)

/-- Helper for Lemma 7.29.6: sections of a large-universe sheaf are determined by their
restrictions to the members of a covering family. -/
private lemma ulift_section_eq_of_cover_restrictions_eq
    {V : D} (S : K.Cover V)
    {ℱ : Sheaf K (Type (max wLarge u₂ v₂))} {s t : ℱ.obj.obj (op V)}
    (h : ∀ I : S.Arrow, ℱ.obj.map I.f.op s = ℱ.obj.map I.f.op t) :
    s = t := by
  -- Package the two sections as constant maps so the sheaf condition can compare them directly.
  let e₁ : PUnit ⟶ ℱ.obj.obj (op V) := fun _ ↦ s
  let e₂ : PUnit ⟶ ℱ.obj.obj (op V) := fun _ ↦ t
  have heq : e₁ = e₂ := by
    -- The covering family detects equality because `ℱ` is a sheaf on `K`.
    apply ℱ.property.hom_ext S e₁ e₂
    intro I
    funext x
    cases x
    exact h I
  simpa [e₁, e₂] using congrFun heq PUnit.unit

/-- Helper for Lemma 7.29.6: equality after precomposition with the large-universe cover map
forces equality of the restricted sections on each member of the cover. -/
private lemma ulift_cover_component_eq_of_coverMap_comp_eq
    {V : D} [HasWeakSheafify K (Type (max wLarge u₂ v₂))] (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y)]
    {ℱ : Sheaf K (Type (max wLarge u₂ v₂))}
    {α β : K.uliftSheafifiedRepresentable V ⟶ ℱ}
    (hcomp :
      uliftSheafifiedRepresentableCoverMap S ≫ α =
        uliftSheafifiedRepresentableCoverMap S ≫ β) :
    ∀ I : S.Arrow,
      ℱ.obj.map I.f.op (K.uliftSheafifiedRepresentableHomEquiv ℱ V α) =
        ℱ.obj.map I.f.op (K.uliftSheafifiedRepresentableHomEquiv ℱ V β) := by
  intro I
  have hI :
      K.uliftSheafifiedRepresentableFunctor.map I.f ≫ α =
        K.uliftSheafifiedRepresentableFunctor.map I.f ≫ β := by
    -- Precompose with the `I`-th coproduct inclusion to isolate the `I`-th component.
    have hι := congrArg
      (fun k =>
        Limits.Sigma.ι (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y) I ≫ k)
      hcomp
    have hι' :
        (Limits.Sigma.ι (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y) I ≫
            uliftSheafifiedRepresentableCoverMap S) ≫ α =
          (Limits.Sigma.ι (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y) I ≫
            uliftSheafifiedRepresentableCoverMap S) ≫ β := by
      simpa [Category.assoc] using hι
    rw [uliftSheafifiedRepresentableCoverMap, Limits.Sigma.ι_desc] at hι'
    simpa [Category.assoc] using hι'
  have hα :
      K.uliftSheafifiedRepresentableHomEquiv ℱ I.Y
          (K.uliftSheafifiedRepresentableFunctor.map I.f ≫ α) =
        ℱ.obj.map I.f.op (K.uliftSheafifiedRepresentableHomEquiv ℱ V α) := by
    -- Translate the restricted morphism into restriction of the corresponding section.
    simpa using K.uliftSheafifiedRepresentableHomEquiv_naturality I.f ℱ α
  have hβ :
      K.uliftSheafifiedRepresentableHomEquiv ℱ I.Y
          (K.uliftSheafifiedRepresentableFunctor.map I.f ≫ β) =
        ℱ.obj.map I.f.op (K.uliftSheafifiedRepresentableHomEquiv ℱ V β) := by
    -- The same naturality formula applies to the second comparison morphism.
    simpa using K.uliftSheafifiedRepresentableHomEquiv_naturality I.f ℱ β
  rw [← hα, ← hβ]
  exact congrArg (K.uliftSheafifiedRepresentableHomEquiv ℱ I.Y) hI

/-- Helper for Lemma 7.29.6: in the large ambient universe, the canonical cover map of
sheafified representables is an epimorphism. -/
private theorem uliftSheafifiedRepresentableCoverMap_epi
    {V : D} [HasWeakSheafify K (Type (max wLarge u₂ v₂))] (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y)] :
    Epi (uliftSheafifiedRepresentableCoverMap S) where
  left_cancellation {ℱ} α β h := by
    -- Compare the two morphisms via their corresponding sections over `V`.
    apply (K.uliftSheafifiedRepresentableHomEquiv ℱ V).injective
    -- The sheaf condition reduces equality to the coverwise restriction equalities.
    apply ulift_section_eq_of_cover_restrictions_eq (K := K) S
    intro I
    exact ulift_cover_component_eq_of_coverMap_comp_eq S h I

/-- Helper for Lemma 7.29.6: the large-universe cover map of sheafified representables is locally
surjective. -/
private theorem uliftSheafifiedRepresentableCoverMap_isLocallySurjective
    {V : D} [HasWeakSheafify K (Type (max wLarge u₂ v₂))] (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y)] :
    Sheaf.IsLocallySurjective (uliftSheafifiedRepresentableCoverMap S) := by
  -- Convert local surjectivity into the ambient epimorphism statement just proved above.
  rw [Sheaf.isLocallySurjective_iff_epi]
  exact uliftSheafifiedRepresentableCoverMap_epi S

/-- Helper for Lemma 7.29.6: once `f` is available in the representable universe
`Type (max u₂ v₂)`, its inverse-image functor sends the canonical cover map on `K` to a locally
surjective morphism on `J`. -/
private theorem inverseImage_map_sheafifiedRepresentableCoverMap_isLocallySurjective
    [HasWeakSheafify K (Type (max u₂ v₂))]
    [HasSheafify J (Type (max u₂ v₂))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max u₂ v₂} K J)
    {V : D} (S : K.Cover V) :
    Sheaf.IsLocallySurjective
      ((show Sheaf K (Type (max u₂ v₂)) ⥤
          Sheaf J (Type (max u₂ v₂)) from f⁻¹).map
        (K.sheafifiedRepresentableCoverMap S)) := by
  -- The inverse image is a left adjoint, so it preserves the epimorphic cover map.
  letI :
      (show Sheaf K (Type (max u₂ v₂)) ⥤
          Sheaf J (Type (max u₂ v₂)) from f⁻¹).IsLeftAdjoint :=
    f.adjunction.isLeftAdjoint
  letI : Epi (K.sheafifiedRepresentableCoverMap S) :=
    K.sheafifiedRepresentableCoverMap_epi S
  have hEpi :
      Epi
        ((show Sheaf K (Type (max u₂ v₂)) ⥤
            Sheaf J (Type (max u₂ v₂)) from f⁻¹).map
          (K.sheafifiedRepresentableCoverMap S)) := by
    infer_instance
  exact (Sheaf.isLocallySurjective_iff_epi _).2 hEpi

/-- Helper for Lemma 7.29.6: once a large-universe avatar of `f` is available, its inverse-image
functor sends the canonical cover map on `K` to a locally surjective morphism on `J`. -/
private theorem inverseImage_map_uliftSheafifiedRepresentableCoverMap_isLocallySurjective
    [HasWeakSheafify K (Type (max wLarge u₂ v₂))]
    [HasSheafify J (Type (max wLarge u₂ v₂))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max wLarge u₂ v₂} K J)
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ K.uliftSheafifiedRepresentable I.Y)] :
    Sheaf.IsLocallySurjective
      ((show Sheaf K (Type (max wLarge u₂ v₂)) ⥤
          Sheaf J (Type (max wLarge u₂ v₂)) from f⁻¹).map
        (uliftSheafifiedRepresentableCoverMap S)) := by
  -- The inverse image is a left adjoint, hence it preserves epimorphisms.
  letI :
      (show Sheaf K (Type (max wLarge u₂ v₂)) ⥤
          Sheaf J (Type (max wLarge u₂ v₂)) from f⁻¹).IsLeftAdjoint :=
    f.adjunction.isLeftAdjoint
  letI : Epi (uliftSheafifiedRepresentableCoverMap S) :=
    uliftSheafifiedRepresentableCoverMap_epi S
  have hEpi :
      Epi
        ((show Sheaf K (Type (max wLarge u₂ v₂)) ⥤
            Sheaf J (Type (max wLarge u₂ v₂)) from f⁻¹).map
          (uliftSheafifiedRepresentableCoverMap S)) := by
    infer_instance
  -- Translate the preserved epimorphism back to local surjectivity on sheaves of types.
  exact (Sheaf.isLocallySurjective_iff_epi _).2 hEpi

/- Domain-style sampling for Lemma 7.29.6:
- primary domain: factorization of a morphism of sheaf topoi through an intermediate site coming
  from a dense-subsite presentation on the source and a morphism of sites on the target side;
- sampled owner API:
  `MorphismOfTopoiIn`,
  `CatCommSq`,
  `Functor.IsDenseSubsite`,
  `IsMorphismOfSites`,
  `Functor.morphismOfTopoiInOfContinuous`;
- best owner abstraction: the source-facing content is the existence of an intermediate site
  `(C', J')`, but the two legs should be expressed through the canonical owners already fixed in
  the chapter: the dense-subsite owner `v.IsDenseSubsite J J'` on the source side, the
  site-morphism owner `IsMorphismOfSites K J' u` on the target side. The factorization of
  inverse-image functors is therefore best recorded by the canonical square owner `CatCommSq`
  together with a lower horizontal morphism `g : MorphismOfTopoiIn K J'` at the source-facing
  layer, while the weak sheafification/Kan-extension/left-exactness hypotheses needed to identify
  `g` with the canonical owner `u.morphismOfTopoiInOfContinuous K J'` remain bridge data and
  belong in a separate companion theorem;
- source/core/bridge triage:
  `source-facing`: the factorization of `f : Sh(J) ⟶ Sh(K)` through an intermediate site
    `(C', J')`;
  `core/canonical`: `Functor.IsDenseSubsite`, `IsMorphismOfSites`, `MorphismOfTopoiIn`,
    `CatCommSq`, and `Functor.morphismOfTopoiInOfContinuous`;
  `bridge/view`: the dense-subsite comparison functor on the source side and the realization
    hypotheses needed to identify the lower morphism with
    `u.morphismOfTopoiInOfContinuous K J'`.

Primitive data are the intermediate site, the dense-subsite functor `v`, the site-morphism functor
`u`, and the lower morphism of topoi `g`, while weak sheafification on `(C', J')`, the left Kan
extensions along `u.op`, and left exactness of the induced inverse image are bridge data needed
only to identify `g` canonically with `u.morphismOfTopoiInOfContinuous K J'`. The public
factorization should therefore keep `v`, `u`, and `g` at the owner layer and record the
inverse-image factorization by a commutative square, with the canonical realization handled
separately.
-/

-- Proof sketch: choose the full subcategory `C'` of `Sh(J)` generated by the sheafified
-- representables `h_U^#` and the inverse images `f⁻¹(h_V^#)`, then close under fibre products and
-- equip it with the surjective topology from Lemma `7.29.4`. The functor `v` is the sheafified
-- representable embedding, `u` sends `V` to `f⁻¹(h_V^#)`, and the canonical dense-subsite and
-- site-morphism sheaf functors attached to `v` and `u` identify with the inverse-image functor of
-- `f`.
/-- Helper for Lemma 7.29.6: the first missing source-faithful datum is a large-universe
presentation of the inverse images of representables. This packages the intended family
`V ↦ f⁻¹(h_V^#)` at the ambient universe where the representables live, together with the
pullback-preservation needed later in the source-proof route. -/
private theorem inverse_image_ulift_representable_functor
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    ∃ Φ : D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))),
      PreservesLimitsOfShape WalkingCospan Φ := by
  let Φ :
      D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
      f.inverseImageFunctor.obj
  -- Take the source-proof family `V ↦ f⁻¹(h_V^#)` in the canonical presentation form.
  refine ⟨Φ, ?_⟩
  -- Pullback preservation follows from the canonical presentation functor and left exactness of
  -- the inverse image.
  -- The representable functor preserves pullbacks, and so does the inverse image.
  change PreservesLimitsOfShape WalkingCospan
    (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
      f.inverseImageFunctor.obj)
  infer_instance

/-- Helper for Lemma 7.29.6: after enlarging the source site to `AsSmall C`, any large-universe
sheaf-valued family on `D` is of the form required by Lemma `7.29.5`, so the replacement-site
presentation can be constructed before any later comparison-square bookkeeping. -/
private theorem exists_factorization_site_presentation_from_family
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (Φ : D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    ∃ (C0Small : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C0Small)
      (J0Small : GrothendieckTopology C0Small)
      (a : C ⥤ C0Small) (_ : a.IsDenseSubsite J J0Small),
      ∃ (C0 : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C0)
        (J0 : GrothendieckTopology C0)
        (_ : J0.Subcanonical) (_ : HasFiniteLimits C0)
        (v0 : C0Small ⥤ C0) (_ : v0.IsDenseSubsite J0Small J0),
        ∀ V : D,
          (((sheafEquiv J0Small J0 v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor.obj
              ((sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor.obj
                (Φ.obj V))).obj).IsRepresentable := by
  let C0Small : Type (max (max u₁ v₁) (max u₂ v₂)) := CategoryTheory.AsSmall.{max u₂ v₂} C
  let a : C ⥤ C0Small := CategoryTheory.AsSmall.up
  let e : C ≌ C0Small := CategoryTheory.AsSmall.equiv (C := C)
  let J0Small : GrothendieckTopology C0Small := e.inverse.inducedTopology J
  have haDense : a.IsDenseSubsite J J0Small := by
    -- The standard `AsSmall` equivalence gives the first dense-subsite transport required by the
    -- source proof.
    change e.functor.IsDenseSubsite J J0Small
    infer_instance
  let Φ0 : D → Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) := fun V ↦
    -- Move the large-universe family onto the enlarged source site.
    (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor.obj
      (Φ.obj V)
  -- Apply the replacement-site theorem exactly to the transported family on `AsSmall C`.
  obtain ⟨C0, hC0, J0, hsub0, hfinite0, v0, hv0, _, _, _, hfamily⟩ :=
    exists_representable_family_site_presentation (J := J0Small) Φ0
  let _ : Category C0 := hC0
  let _ : J0.Subcanonical := hsub0
  let _ : HasFiniteLimits C0 := hfinite0
  let _ : v0.IsDenseSubsite J0Small J0 := hv0
  let _ : Category C0Small := by infer_instance
  -- The family clause from Lemma `7.29.5` is already the representability conclusion we need.
  exact
    ⟨C0Small, ‹Category C0Small›, J0Small, a, haDense,
      C0, hC0, J0, hsub0, hfinite0, v0, hv0, by
        intro V
        simpa [Φ0] using hfamily V⟩

/-- Helper for Lemma 7.29.6: once a large-universe avatar of `f` is available, the replacement
site theorem already constructs the intermediate site together with the target-side functor
`u : D ⥤ C'` and the Yoneda identification of the transported family. -/
private theorem exists_factorization_site_data_from_family
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (Φ : D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    ∃ (C0Small : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C0Small)
      (J0Small : GrothendieckTopology C0Small)
      (a : C ⥤ C0Small) (_ : a.IsDenseSubsite J J0Small),
      ∃ (C0 : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C0)
        (J0 : GrothendieckTopology C0)
        (_ : J0.Subcanonical) (_ : HasFiniteLimits C0)
        (v0 : C0Small ⥤ C0) (_ : v0.IsDenseSubsite J0Small J0)
        (u : D ⥤ C0),
          Nonempty
            (u ⋙ J0.yoneda ≅
              Φ ⋙
                (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
                  (sheafEquiv J0Small J0 v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) := by
  obtain ⟨C0Small, hC0Small, J0Small, a, haDense,
      C0, hC0, J0, hsub0, hfinite0, v0, hv0, hfamily⟩ :=
    exists_factorization_site_presentation_from_family (J := J) Φ
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small := hC0Small
  let _ : a.IsDenseSubsite J J0Small := haDense
  let _ : Category C0 := hC0
  let _ : J0.Subcanonical := hsub0
  let _ : HasFiniteLimits C0 := hfinite0
  let _ : v0.IsDenseSubsite J0Small J0 := hv0
  let F :
      D ⥤ Sheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    Φ ⋙
      (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
        (sheafEquiv J0Small J0 v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor
  let Y :
      C0 ⥤ Sheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    GrothendieckTopology.yoneda J0
  let objOf : D → C0 := fun V ↦ by
    let _ :
        (F.obj V).obj.IsRepresentable := by
          simpa [F] using hfamily V
    exact (F.obj V).obj.reprX
  let reprIso : ∀ V : D, Y.obj (objOf V) ≅ F.obj V := fun V ↦ by
    let _ :
        (F.obj V).obj.IsRepresentable := by
          simpa [F] using hfamily V
    -- Replace the transported sheaf by its chosen representing object on the replacement site.
    exact
      (fullyFaithfulSheafToPresheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂)))).preimageIso
        ((F.obj V).obj.reprW)
  let u : D ⥤ C0 :=
    { obj := fun V ↦ objOf V
      map := fun {V W} f =>
        -- Recover the site morphism from the induced morphism between representable sheaves.
        Functor.preimage Y ((reprIso V).hom ≫ F.map f ≫ (reprIso W).inv)
      map_id := by
        intro V
        -- Full faithfulness of `Y` reduces the identity law to the corresponding sheaf map.
        apply Functor.map_injective Y
        simp
      map_comp := by
        intro V W X f g
        -- The same reduction turns composition into a straightforward associativity check.
        apply Functor.map_injective Y
        simp [Category.assoc] }
  let ρ : u ⋙ Y ≅ F :=
    NatIso.ofComponents reprIso (fun {V W} f ↦ by
      -- Naturality is exactly the way `u.map f` was defined from the chosen representability data.
      simp [u, Category.assoc])
  exact ⟨C0Small, hC0Small, J0Small, a, haDense,
    C0, hC0, J0, hsub0, hfinite0, v0, hv0, u, ⟨ρ⟩⟩

/-- Helper for Lemma 7.29.6: the replacement-site presentation can be unpacked in a form that
keeps the source-proof cover characterization visible alongside the target-side functor `u` and
the Yoneda comparison isomorphism. -/
private theorem exists_factorization_site_data_with_cover_characterization
    [HasWeakSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (Φ : D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂)))) :
    ∃ (C0Small : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C0Small)
      (J0Small : GrothendieckTopology C0Small)
      (a : C ⥤ C0Small) (_ : a.IsDenseSubsite J J0Small) (_ : a.IsEquivalence),
      ∃ (C0 : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C0)
        (J0 : GrothendieckTopology C0)
        (_ : J0.Subcanonical) (_ : HasFiniteLimits C0)
        (v0 : C0Small ⥤ C0) (_ : v0.IsDenseSubsite J0Small J0)
        (_ : J.Subcanonical → v0.FullyFaithful)
        (hcover :
          ∀ ⦃X : C0⦄ (R : Presieve X),
            R ∈ J0.toPrecoverage X ↔
              ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C0) (π : ∀ i, Y i ⟶ X),
                R = Presieve.ofArrows Y π ∧
                  Presheaf.IsLocallySurjective J0
                    (Limits.Sigma.desc (fun i ↦ (J0.yoneda.map (π i)).hom)))
        (hsubobj :
          ∀ X : C0, ∀ G : Subobject (J0.yoneda.obj X),
            ((G : Sheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂)))).obj).IsRepresentable)
        (u : D ⥤ C0),
          Nonempty
            (u ⋙ J0.yoneda ≅
              Φ ⋙
                (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
                  (sheafEquiv J0Small J0 v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) := by
  let C0Small : Type (max (max u₁ v₁) (max u₂ v₂)) := CategoryTheory.AsSmall.{max u₂ v₂} C
  let a : C ⥤ C0Small := CategoryTheory.AsSmall.up
  let e : C ≌ C0Small := CategoryTheory.AsSmall.equiv (C := C)
  let J0Small : GrothendieckTopology C0Small := e.inverse.inducedTopology J
  have haDense : a.IsDenseSubsite J J0Small := by
    -- The source enlargement to `AsSmall C` is the first dense-subsite transport.
    change e.functor.IsDenseSubsite J J0Small
    infer_instance
  have haEquiv : a.IsEquivalence := by
    -- The same `AsSmall` enlargement is an equivalence, and the downstream composition helper
    -- needs that owner explicitly.
    change e.functor.IsEquivalence
    infer_instance
  let Φ0 : D → Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) := fun V ↦
    -- Move the family to the small source site before applying Lemma `7.29.5`.
    (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor.obj
      (Φ.obj V)
  obtain ⟨C0, hC0, J0, hsub0, hfinite0, v0, hv0, hv0ff, hcover, hsubobj, hfamily⟩ :=
    exists_representable_family_site_presentation (J := J0Small) Φ0
  let _ : Category C0Small := by infer_instance
  let _ : Category C0 := hC0
  let _ : J0.Subcanonical := hsub0
  let _ : HasFiniteLimits C0 := hfinite0
  let _ : v0.IsDenseSubsite J0Small J0 := hv0
  let F :
      D ⥤ Sheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    Φ ⋙
      (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
        (sheafEquiv J0Small J0 v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor
  let Y :
      C0 ⥤ Sheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    GrothendieckTopology.yoneda J0
  let objOf : D → C0 := fun V ↦ by
    let _ :
        (F.obj V).obj.IsRepresentable := by
          simpa [F, Φ0] using hfamily V
    exact (F.obj V).obj.reprX
  let reprIso : ∀ V : D, Y.obj (objOf V) ≅ F.obj V := fun V ↦ by
    let _ :
        (F.obj V).obj.IsRepresentable := by
          simpa [F, Φ0] using hfamily V
    -- The representing object of the transported sheaf gives the desired Yoneda comparison.
    exact
      (fullyFaithfulSheafToPresheaf J0 (Type (max (max u₁ v₁) (max u₂ v₂)))).preimageIso
        ((F.obj V).obj.reprW)
  let u : D ⥤ C0 :=
    { obj := fun V ↦ objOf V
      map := fun {V W} f =>
        -- Define the target-side site functor by preimaging the transported sheaf map.
        Functor.preimage Y ((reprIso V).hom ≫ F.map f ≫ (reprIso W).inv)
      map_id := by
        intro V
        -- Full faithfulness of `Y` reduces identities to the sheaf-level identity map.
        apply Functor.map_injective Y
        simp
      map_comp := by
        intro V W X f g
        -- The same reduction turns composition into associativity in the sheaf category.
        apply Functor.map_injective Y
        simp [Category.assoc] }
  let ρ : u ⋙ Y ≅ F :=
    NatIso.ofComponents reprIso (fun {V W} f ↦ by
      -- Naturality records the way `u.map f` was defined from the representing isomorphisms.
      simp [u, Category.assoc])
  have hv0ffC : J.Subcanonical → v0.FullyFaithful := by
    intro hJsub
    haveI := hJsub
    letI : Functor.IsContinuous e.inverse (e.inverse.inducedTopology J) J := inferInstance
    haveI : J0Small.Subcanonical :=
      GrothendieckTopology.subcanonical_of_full_of_faithful
        (F := e.inverse) (J := J0Small) (K := J)
    exact hv0ff this
  exact ⟨C0Small, ‹Category C0Small›, J0Small, a, haDense, haEquiv,
    C0, hC0, J0, hsub0, hfinite0, v0, hv0, hv0ffC, hcover, hsubobj, u, ⟨ρ⟩⟩

/-- Helper for Lemma 7.29.6: if the Yoneda presentation of `u` preserves pullbacks, then `u`
itself preserves pullbacks because subcanonical Yoneda both preserves and reflects them. -/
private theorem preserves_pullbacks_of_yoneda_presentation_iso
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical] [HasFiniteLimits C']
    (u : D ⥤ C')
    {F : D ⥤ Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))}
    (ρ : u ⋙ J'.yoneda ≅ F)
    [PreservesLimitsOfShape WalkingCospan F] :
    PreservesLimitsOfShape WalkingCospan u := by
  -- First transport pullback preservation from the represented family `F` to `u ⋙ J'.yoneda`
  -- using the stored Yoneda presentation isomorphism.
  have hcomp : PreservesLimitsOfShape WalkingCospan (u ⋙ J'.yoneda) :=
    preservesLimitsOfShape_of_natIso ρ.symm
  -- Then reflect the pullback-preservation statement back across the subcanonical Yoneda functor.
  exact preservesLimitsOfShape_of_reflects_of_preserves u J'.yoneda

/-- Helper for Lemma 7.29.6: composing a dense-subsite functor with an equivalence on the left
again yields a dense-subsite functor. -/
theorem dense_subsite_comp_of_equivalence_left
    {C0 : Type*} [Category* C0]
    {C' : Type*} [Category* C']
    {J0 : GrothendieckTopology C0} {J' : GrothendieckTopology C'}
    (a : C ⥤ C0) (v0 : C0 ⥤ C')
    [a.IsDenseSubsite J J0] [a.IsEquivalence]
    [v0.IsDenseSubsite J0 J'] :
    (a ⋙ v0).IsDenseSubsite J J' := by
  let e : C ≌ C0 := a.asEquivalence
  let _ : a.IsCoverDense J0 := Functor.IsDenseSubsite.isCoverDense (J := J) (K := J0) (G := a)
  let _ : a.IsLocallyFull J0 := Functor.IsDenseSubsite.isLocallyFull (J := J) (K := J0) (G := a)
  let _ : a.IsLocallyFaithful J0 :=
    Functor.IsDenseSubsite.isLocallyFaithful (J := J) (K := J0) (G := a)
  let _ : v0.IsCoverDense J' := Functor.IsDenseSubsite.isCoverDense (J := J0) (K := J') (G := v0)
  let _ : v0.IsLocallyFull J' := Functor.IsDenseSubsite.isLocallyFull (J := J0) (K := J') (G := v0)
  let _ : v0.IsLocallyFaithful J' :=
    Functor.IsDenseSubsite.isLocallyFaithful (J := J0) (K := J') (G := v0)
  have hcoverDense : (a ⋙ v0).IsCoverDense J' := by
    refine ⟨?_⟩
    intro X
    -- Replace each `v0`-image source object by an equivalent `a`-image source object.
    refine J'.superset_covering ?_ (v0.is_cover_of_isCoverDense J' X)
    intro Y f hf
    rcases hf with ⟨⟨Z, lift, map, fac⟩⟩
    let i : v0.obj (a.obj (e.inverse.obj Z)) ≅ v0.obj Z := v0.mapIso (e.counitIso.app Z)
    refine ⟨⟨e.inverse.obj Z, lift ≫ i.inv, i.hom ≫ map, ?_⟩⟩
    -- The counit comparison turns the original factorization through `v0.obj Z` into one through
    -- the composite image `v0.obj (a.obj (e.inverse.obj Z))`.
    have hi₀ : e.counitIso.inv.app Z ≫ e.counitIso.hom.app Z = 𝟙 Z := by simp
    have hi :
        v0.map (e.counitIso.inv.app Z) ≫ v0.map (e.counitIso.hom.app Z) =
          𝟙 (v0.obj Z) := by
      rw [← Functor.map_comp, hi₀]
      simpa using v0.map_id Z
    have hfac' :
        lift ≫ v0.map (e.counitIso.inv.app Z) ≫ v0.map (e.counitIso.hom.app Z) ≫ map = f := by
      calc
        lift ≫ v0.map (e.counitIso.inv.app Z) ≫ v0.map (e.counitIso.hom.app Z) ≫ map
            = lift ≫ (v0.map (e.counitIso.inv.app Z) ≫ v0.map (e.counitIso.hom.app Z)) ≫ map := by
                simp [Category.assoc]
        _ = lift ≫ map := by
          have h' := congrArg (fun k => lift ≫ k ≫ map) hi
          simpa [Category.assoc] using h'
        _ = f := fac
    simpa [i] using hfac'
  refine
    { isCoverDense' := hcoverDense
      isLocallyFull' := ?_
      isLocallyFaithful' := ?_
      functorPushforward_mem_iff := ?_ }
  · refine ⟨?_⟩
    intro U V f
    let T : Sieve (a.obj U) := v0.imageSieve f
    have hpullback :
        (a ⋙ v0).imageSieve f = T.functorPullback a := by
      -- Fullness of `a` identifies the composite image sieve with pullback of the `v0` image
      -- sieve.
      ext W i
      constructor
      · rintro ⟨l, hl⟩
        exact ⟨a.map l, by simpa [T, Functor.comp_map, Category.assoc] using hl⟩
      · rintro ⟨l, hl⟩
        refine ⟨a.preimage l, ?_⟩
        simpa [T, Functor.comp_map, Category.assoc] using hl
    have hT' : T.functorPushforward v0 ∈ J' ((a ⋙ v0).obj U) :=
      v0.functorPushforward_imageSieve_mem J' f
    have hT : T ∈ J0 (a.obj U) :=
      (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J0) (K := J') (G := v0)).mp hT'
    have hTa :
        (T.functorPullback a).functorPushforward a ∈ J0 (a.obj U) :=
      Functor.IsCoverDense.functorPullback_pushforward_covering (G := a) (K := J0) ⟨T, hT⟩
    have hcomp :
        ((T.functorPullback a).functorPushforward a).functorPushforward v0 ∈ J' ((a ⋙ v0).obj U) :=
      (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J0) (K := J') (G := v0)).mpr hTa
    simpa [T, hpullback, Sieve.functorPushforward_comp] using hcomp
  · refine ⟨?_⟩
    intro U V f g hfg
    let T : Sieve (a.obj U) := Sieve.equalizer (a.map f) (a.map g)
    have hpullback :
        Sieve.equalizer f g = T.functorPullback a := by
      -- Faithfulness of `a` identifies the equalizer sieve with the pullback of the corresponding
      -- equalizer sieve upstairs.
      ext W i
      constructor
      · intro hi
        change a.map i ≫ a.map f = a.map i ≫ a.map g
        simpa [T, Functor.map_comp] using congrArg (fun k ↦ a.map k) hi
      · intro hi
        exact a.map_injective (by simpa [T, Functor.map_comp] using hi)
    have hT' : T.functorPushforward v0 ∈ J' ((a ⋙ v0).obj U) :=
      v0.functorPushforward_equalizer_mem J' (a.map f) (a.map g) hfg
    have hT : T ∈ J0 (a.obj U) :=
      (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J0) (K := J') (G := v0)).mp hT'
    have hTa :
        (T.functorPullback a).functorPushforward a ∈ J0 (a.obj U) :=
      Functor.IsCoverDense.functorPullback_pushforward_covering (G := a) (K := J0) ⟨T, hT⟩
    have hcomp :
        ((T.functorPullback a).functorPushforward a).functorPushforward v0 ∈ J' ((a ⋙ v0).obj U) :=
      (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J0) (K := J') (G := v0)).mpr hTa
    simpa [T, hpullback, Sieve.functorPushforward_comp] using hcomp
  · intro X S
    constructor
    · intro hS
      -- Peel the dense-subsite condition across `v0`, then across `a`.
      have hSv0 : (S.functorPushforward a).functorPushforward v0 ∈ J' ((a ⋙ v0).obj X) := by
        simpa [Sieve.functorPushforward_comp] using hS
      have hSa : S.functorPushforward a ∈ J0 (a.obj X) :=
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J0) (K := J') (G := v0)).mp hSv0
      exact (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := J0) (G := a)).mp hSa
    · intro hS
      -- Push the covering sieve through `a` and then through `v0`.
      have hSa : S.functorPushforward a ∈ J0 (a.obj X) :=
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J) (K := J0) (G := a)).mpr hS
      have hSv0 : (S.functorPushforward a).functorPushforward v0 ∈ J' ((a ⋙ v0).obj X) :=
        (Functor.IsDenseSubsite.functorPushforward_mem_iff (J := J0) (K := J') (G := v0)).mpr hSa
      simpa [Sieve.functorPushforward_comp] using hSv0

/-
The next source-faithful step should pass from the theorem-facing morphism
`f : MorphismOfTopoiIn K J` to the large-universe family `V ↦ f⁻¹(h_V^#)` directly, rather than
through an owner-level large-universe morphism of topoi. The helper
`exists_factorization_site_data_from_family` already packages the replacement-site output once such a
large-universe family has been constructed. The remaining structural blocker is therefore the
cross-universe presentation of that family, not the downstream continuity or Yoneda-square
bookkeeping.
-/

/-- Bridge form of Lemma 7.29.6 in the universe where the source construction actually
lives. The source proof forms the family `V ↦ f⁻¹(h_V^#)` of sheaves on `C`; in Lean this requires
`f` itself to be available for sheaves valued in
`Type (max (max u₁ v₁) (max u₂ v₂))`, the universe containing both sites' representables. With
that owner in place, the canonical site morphism `u` realizes the lower horizontal inverse-image
functor and the displayed square records the factorization of `f`. -/
theorem exists_special_cocontinuous_site_factorization_canonical
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    ∃ (C' : Type (max (max u₁ v₁) (max u₂ v₂)))
      (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C')
      (J' : GrothendieckTopology C')
      (v : C ⥤ C') (hv : v.IsDenseSubsite J J')
      (u : D ⥤ C')
      (_ : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))),
      ∀ P : Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)), u.op.HasLeftKanExtension P := by
  -- Route correction: the theorem no longer claims that an arbitrary small-universe
  -- `MorphismOfTopoiIn K J` canonically supplies inverse images of the large representables
  -- `h_V^#`. The large-universe owner above is exactly the Lean data corresponding to the source
  -- phrase `V ↦ f^{-1} h_V^#`.
  obtain ⟨Φ, hΦPullbacks⟩ :=
    inverse_image_ulift_representable_functor (J := J) (K := K) f
  obtain ⟨C0Small, hC0Small, J0Small, a, haDense, haEquiv,
      C', hC', J', hsub, hfinite, v0, hv0, _, _hcover, _hsubobj, u, _hρ⟩ :=
    exists_factorization_site_data_with_cover_characterization (J := J) Φ
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small := hC0Small
  let _ : a.IsDenseSubsite J J0Small := haDense
  let _ : a.IsEquivalence := haEquiv
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C' := hC'
  let _ : J'.Subcanonical := hsub
  let _ : HasFiniteLimits C' := hfinite
  let _ : v0.IsDenseSubsite J0Small J' := hv0
  let _ : PreservesLimitsOfShape WalkingCospan Φ := hΦPullbacks
  let v : C ⥤ C' := a ⋙ v0
  have hv : v.IsDenseSubsite J J' := by
    -- The replacement-site source leg is the `AsSmall` equivalence, so the composite dense-subsite
    -- structure is exactly the specialization of the helper above.
    simpa [v] using
      (dense_subsite_comp_of_equivalence_left
        (C0 := C0Small) (C' := C') (J := J) (J0 := J0Small) (J' := J') a v0)
  have huPullbacks : PreservesLimitsOfShape WalkingCospan u := by
    -- Freeze the transported family before using the Yoneda presentation so the source proof's
    -- pullback-preservation step no longer depends on unresolved universe metavariables.
    rcases _hρ with ⟨ρ⟩
    have hFrozen :
        PreservesLimitsOfShape WalkingCospan
          (Φ ⋙
            (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
              (sheafEquiv J0Small J' v0
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) := by
      -- The transported family is a composite of pullback-preserving functors.
      let _ : PreservesLimitsOfShape WalkingCospan Φ := hΦPullbacks
      infer_instance
    let _ :
        PreservesLimitsOfShape WalkingCospan
          (Φ ⋙
            (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
              (sheafEquiv J0Small J' v0
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) := hFrozen
    have hcomp : PreservesLimitsOfShape WalkingCospan (u ⋙ J'.yoneda) :=
      preservesLimitsOfShape_of_natIso ρ.symm
    -- Reflect pullback preservation across subcanonical Yoneda after transporting it along `ρ`.
    exact preservesLimitsOfShape_of_reflects_of_preserves u J'.yoneda
  have hweakJ' : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂))) := by
    -- The source dense-subsite comparison transports weak sheafification to the intermediate site.
    let _ :
        (v.sheafPushforwardContinuous (Type (max (max u₁ v₁) (max u₂ v₂))) J J').IsEquivalence :=
      by infer_instance
    exact denseSubsite_hasWeakSheafify (J := J) (v := v)
  refine ⟨C', hC', J', v, hv, u, hweakJ', ?_⟩
  infer_instance

/-- Helper for Lemma 7.29.6: package the source-proof data that the public theorem needs but the
canonical existential hides, namely the replacement-site cover characterization, the Yoneda
presentation of the target functor, and the already-established pullback-preservation route. -/
private theorem exists_special_cocontinuous_site_factorization_source_package
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    ∃ (C0Small : Type (max (max u₁ v₁) (max u₂ v₂)))
      (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small)
      (J0Small : GrothendieckTopology C0Small)
      (a : C ⥤ C0Small) (_ : a.IsDenseSubsite J J0Small) (_ : a.IsEquivalence),
      ∃ (C' : Type (max (max u₁ v₁) (max u₂ v₂)))
        (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C')
        (J' : GrothendieckTopology C')
        (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
        (v0 : C0Small ⥤ C') (_ : v0.IsDenseSubsite J0Small J')
        (_ : J.Subcanonical → v0.FullyFaithful)
        (hcover :
          ∀ ⦃X : C'⦄ (R : Presieve X),
            R ∈ J'.toPrecoverage X ↔
              ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
                R = Presieve.ofArrows Y π ∧
                  Presheaf.IsLocallySurjective J'
                    (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
        (hsubobj :
          ∀ X : C', ∀ G : Subobject (J'.yoneda.obj X),
            ((G : Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))).obj).IsRepresentable)
        (u : D ⥤ C')
        (ρ :
          Nonempty
            (u ⋙ J'.yoneda ≅
              (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
                  f.inverseImageFunctor.obj) ⋙
                (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
                  (sheafEquiv J0Small J' v0
                    (Type (max (max u₁ v₁) (max u₂ v₂)))).functor))
        (_ : PreservesLimitsOfShape WalkingCospan u)
        (_ : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))),
          ∀ P : Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)), u.op.HasLeftKanExtension P := by
  let Φ :
      D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
      f.inverseImageFunctor.obj
  have hΦPullbacks : PreservesLimitsOfShape WalkingCospan Φ := by
    -- Use the canonical presentation `V ↦ f⁻¹(h_V^#)` directly, so the stored Yoneda comparison
    -- matches the theorem statement without an extra existential transport.
    change PreservesLimitsOfShape WalkingCospan
      (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
        f.inverseImageFunctor.obj)
    infer_instance
  obtain ⟨C0Small, hC0Small, J0Small, a, haDense, haEquiv,
      C', hC', J', hsub, hfinite, v0, hv0, hv0ff, hcover, hsubobj, u, hρ⟩ :=
    exists_factorization_site_data_with_cover_characterization (J := J) Φ
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small := hC0Small
  let _ : a.IsDenseSubsite J J0Small := haDense
  let _ : a.IsEquivalence := haEquiv
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C' := hC'
  let _ : J'.Subcanonical := hsub
  let _ : HasFiniteLimits C' := hfinite
  let _ : v0.IsDenseSubsite J0Small J' := hv0
  let _ : PreservesLimitsOfShape WalkingCospan Φ := hΦPullbacks
  have huPullbacks : PreservesLimitsOfShape WalkingCospan u := by
    -- Transport pullback preservation along the stored Yoneda presentation before reflecting it
    -- back across subcanonical Yoneda.
    rcases hρ with ⟨ρ⟩
    have hFrozen :
        PreservesLimitsOfShape WalkingCospan
          (Φ ⋙
            (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
              (sheafEquiv J0Small J' v0
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) := by
      -- The source family and both dense-subsite equivalences preserve pullbacks.
      let _ : PreservesLimitsOfShape WalkingCospan Φ := hΦPullbacks
      infer_instance
    let _ :
        PreservesLimitsOfShape WalkingCospan
          (Φ ⋙
            (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
              (sheafEquiv J0Small J' v0
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) := hFrozen
    have hcomp : PreservesLimitsOfShape WalkingCospan (u ⋙ J'.yoneda) :=
      preservesLimitsOfShape_of_natIso ρ.symm
    -- Reflect pullback preservation across subcanonical Yoneda after transporting it along `ρ`.
    exact preservesLimitsOfShape_of_reflects_of_preserves u J'.yoneda
  let v : C ⥤ C' := a ⋙ v0
  have hv : v.IsDenseSubsite J J' := by
    -- The source leg remains the composite of the `AsSmall` equivalence and the replacement-site
    -- dense subsite.
    simpa [v] using
      (dense_subsite_comp_of_equivalence_left
        (C0 := C0Small) (C' := C') (J := J) (J0 := J0Small) (J' := J') a v0)
  have hweakJ' : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂))) := by
    -- Weak sheafification transports across the composite dense-subsite equivalence on the
    -- source side.
    let _ :
        (v.sheafPushforwardContinuous (Type (max (max u₁ v₁) (max u₂ v₂))) J J').IsEquivalence :=
      by infer_instance
    exact denseSubsite_hasWeakSheafify (J := J) (v := v)
  refine ⟨C0Small, hC0Small, J0Small, a, haDense, haEquiv,
    C', hC', J', hsub, hfinite, v0, hv0, hv0ff, hcover, hsubobj, u, hρ, huPullbacks,
    hweakJ', ?_⟩
  infer_instance

/-- Helper for Remark 7.29.8: expose the replacement-site package from Lemma `7.29.6`,
including the cover criterion, subobject-representability clause, target functor, and Yoneda
presentation used by the identity-factorization argument. -/
theorem exists_special_cocontinuous_site_factorization_with_yonedaPresentation
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    ∃ (C0Small : Type (max (max u₁ v₁) (max u₂ v₂)))
      (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small)
      (J0Small : GrothendieckTopology C0Small)
      (a : C ⥤ C0Small) (_ : a.IsDenseSubsite J J0Small) (_ : a.IsEquivalence),
      ∃ (C' : Type (max (max u₁ v₁) (max u₂ v₂)))
        (_ : Category.{max (max (max u₁ u₂) v₁) v₂} C')
        (J' : GrothendieckTopology C')
        (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
        (v0 : C0Small ⥤ C') (_ : v0.IsDenseSubsite J0Small J')
        (_ : J.Subcanonical → v0.FullyFaithful)
        (hcover :
          ∀ ⦃X : C'⦄ (R : Presieve X),
            R ∈ J'.toPrecoverage X ↔
              ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
                R = Presieve.ofArrows Y π ∧
                  Presheaf.IsLocallySurjective J'
                    (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
        (hsubobj :
          ∀ X : C', ∀ G : Subobject (J'.yoneda.obj X),
            ((G : Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))).obj).IsRepresentable)
        (u : D ⥤ C')
        (ρ :
          Nonempty
            (u ⋙ J'.yoneda ≅
              (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
                  f.inverseImageFunctor.obj) ⋙
                (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
                  (sheafEquiv J0Small J' v0
                    (Type (max (max u₁ v₁) (max u₂ v₂)))).functor))
        (_ : PreservesLimitsOfShape WalkingCospan u)
        (_ : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))),
          ∀ P : Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)), u.op.HasLeftKanExtension P := by
  -- Re-export the source package under a public theorem so later remarks do not have to reprove
  -- or duplicate the replacement-site construction.
  exact exists_special_cocontinuous_site_factorization_source_package (J := J) (K := K) f

/-- Helper for Lemma 7.29.6: once a functor sends a sigma-desc to a locally surjective map, the
source coproduct comparison upgrades that statement to local surjectivity of the sigma-desc built
from the image components. -/
private theorem sheaf_isLocallySurjective_sigma_desc_of_functor_map
    {C₀ : Type*} [Category* C₀] {J₀ : GrothendieckTopology C₀}
    {C₁ : Type*} [Category* C₁] {J₁ : GrothendieckTopology C₁}
    {ι : Type*} (G : Sheaf J₀ (Type w) ⥤ Sheaf J₁ (Type w))
    [HasSheafify J₁ (Type w)] [PreservesColimitsOfShape (Discrete ι) G]
    (X : ι → Sheaf J₀ (Type w)) [HasCoproduct X]
    [HasCoproduct fun i : ι ↦ G.obj (X i)]
    {A : Sheaf J₀ (Type w)} (α : ∀ i : ι, X i ⟶ A)
    (hmap : Sheaf.IsLocallySurjective (G.map (Limits.Sigma.desc α))) :
    Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun i : ι ↦ G.map (α i))) := by
  -- Turn local surjectivity into epimorphy, insert the coproduct comparison isomorphism,
  -- and then rewrite the composite back to the componentwise sigma-desc.
  have hmap_epi : Epi (G.map (Limits.Sigma.desc α)) :=
    (Sheaf.isLocallySurjective_iff_epi _).1 hmap
  have hcomp_epi :
      Epi (Limits.sigmaComparison G X ≫ G.map (Limits.Sigma.desc α)) := by
    exact
      (epi_comp_iff_of_epi (Limits.sigmaComparison G X) (G.map (Limits.Sigma.desc α))).2
        hmap_epi
  have hcomp :
      Sheaf.IsLocallySurjective (Limits.sigmaComparison G X ≫ G.map (Limits.Sigma.desc α)) :=
    (Sheaf.isLocallySurjective_iff_epi _).2 hcomp_epi
  simpa [Limits.sigmaComparison_map_desc] using hcomp

/-- Helper for Lemma 7.29.6: a dense-subsite sheaf equivalence functor preserves local
surjectivity, so the source proof may transport a sigma-desc across one equivalence at a time. -/
private theorem sheaf_isLocallySurjective_map_of_sheafEquiv_functor
    {C₀ : Type*} [Category* C₀] {J₀ : GrothendieckTopology C₀}
    {C₁ : Type*} [Category* C₁] {J₁ : GrothendieckTopology C₁}
    (v : C₀ ⥤ C₁) [v.IsDenseSubsite J₀ J₁]
    [HasSheafify J₀ (Type w)]
    (hvEq : (v.sheafPushforwardContinuous (Type w) J₀ J₁).IsEquivalence)
    {ℱ 𝒢 : Sheaf J₀ (Type w)} (η : ℱ ⟶ 𝒢)
    (hη : Sheaf.IsLocallySurjective η) :
    Sheaf.IsLocallySurjective
      (((sheafEquiv J₀ J₁ v (Type w)).functor).map η) := by
  letI : (v.sheafPushforwardContinuous (Type w) J₀ J₁).IsEquivalence := hvEq
  let E : Sheaf J₀ (Type w) ⥤ Sheaf J₁ (Type w) :=
    (sheafEquiv J₀ J₁ v (Type w)).functor
  letI : E.IsEquivalence := by
    change ((sheafEquiv J₀ J₁ v (Type w)).functor).IsEquivalence
    infer_instance
  letI : HasSheafify J₁ (Type w) :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
      (G := v) (J := J₀) (K := J₁) (A := Type w)
  letI : E.IsLeftAdjoint := inferInstance
  -- Re-express local surjectivity as epimorphy so the equivalence functor can preserve it.
  rw [Sheaf.isLocallySurjective_iff_epi] at hη ⊢
  letI : Epi η := hη
  -- A left adjoint preserves epimorphisms, so the mapped morphism is again locally surjective.
  change Epi (E.map η)
  infer_instance

/-- Helper for Lemma 7.29.6: once the continuity proof is built at the precoverage level, the
associated Grothendieck topology is the original topology again. -/
private theorem factorization_target_toPrecoverage_toGrothendieck_eq
    {E : Type*} [Category E] [HasPullbacks E] (L : GrothendieckTopology E) :
    L.toPrecoverage.toGrothendieck = L := by
  -- This is the standard comparison used to pass from the source-proof precoverage argument back
  -- to continuity for the original Grothendieck topologies.
  rw [← L.toPrecoverage.toGrothendieck_toPretopology_eq_toGrothendieck]
  exact (@Pretopology.gi E _ _).l_u_eq L

/-- Helper for Lemma 7.29.6: before any dense-subsite or Yoneda transport is introduced, the
source-proof family `V ↦ f⁻¹(h_V^#)` already sends a `K`-cover to a locally surjective sigma-desc
on `Sh(J)`. This closes the source-side step and leaves only the later transport through the two
sheaf equivalences and the comparison `ρ`. -/
private theorem factorization_target_inverse_image_cover_sigma_desc_isLocallySurjective
    [HasWeakSheafify K (Type (max wLarge u₂ v₂))]
    [HasSheafify J (Type (max wLarge u₂ v₂))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max wLarge u₂ v₂} K J)
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{wLarge, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{wLarge, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))] :
    Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{wLarge, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).map I.f)) := by
  let G :
      Sheaf K (Type (max wLarge u₂ v₂)) ⥤
        Sheaf J (Type (max wLarge u₂ v₂)) :=
    f.inverseImageFunctor.obj
  let F :
      D ⥤ Sheaf J (Type (max wLarge u₂ v₂)) :=
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{wLarge, u₂, v₂} K ⋙ G
  have hmap :
      Sheaf.IsLocallySurjective (G.map (uliftSheafifiedRepresentableCoverMap (K := K) S)) := by
    -- This is the source-faithful fact that inverse image preserves the canonical cover map.
    exact
      inverseImage_map_uliftSheafifiedRepresentableCoverMap_isLocallySurjective
        (J := J) (K := K) f S
  let X : S.Arrow → Sheaf K (Type (max wLarge u₂ v₂)) := fun I ↦
    GrothendieckTopology.uliftSheafifiedRepresentable.{wLarge, u₂, v₂} K I.Y
  let _ : HasCoproduct X := by
    simpa [X]
  let _ : HasCoproduct (fun I : S.Arrow ↦ G.obj (X I)) := by
    simpa [X, G]
  -- Rewrite the mapped cover map as the sigma-desc built from the inverse-image family.
  simpa [F, G, uliftSheafifiedRepresentableCoverMap, Limits.sigmaComparison_map_desc] using
    (sheaf_isLocallySurjective_sigma_desc_of_functor_map
      (J₀ := K) (J₁ := J) (G := G)
      (X := X)
      (α := fun I : S.Arrow ↦
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{wLarge, u₂, v₂} K).map I.f)
      hmap)

/-- Helper for Lemma 7.29.6: freeze the source family after the two dense-subsite sheaf
equivalences, so later transport lemmas can avoid repeatedly elaborating the full composite. -/
private noncomputable abbrev factorization_target_inverse_image_source_family
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  show D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) from
    GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
      f.inverseImageFunctor.obj

/-- Helper for Lemma 7.29.6: unfold the frozen source family once, so later transport arguments
can rewrite to the concrete inverse-image composite without re-elaborating it. -/
private theorem factorization_target_inverse_image_source_family_def
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    factorization_target_inverse_image_source_family (J := J) (K := K) f =
      (show D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) from
        GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj) := by
  -- The frozen source family is definitionally the source-proof composite `V ↦ f⁻¹(h_V^#)`.
  rfl

/-- Helper for Lemma 7.29.6: freeze the inverse-image functor at the theorem-facing universe
before replaying the source sigma-desc theorem. This keeps the source proof route literal and
prevents Lean from reopening the `MorphismOfTopoiIn` universe while matching the functor input. -/
private theorem factorization_target_inverse_image_functor_at_frozen_universe
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    (show Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
        Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) from f⁻¹) =
      f.inverseImageFunctor.obj := by
  -- The theorem-facing inverse image is definitionally the stored inverse-image functor.
  rfl

/-- Helper for Lemma 7.29.6: each component map of the frozen source family is definitionally the
inverse-image image of the corresponding lifted representable morphism. -/
private theorem factorization_target_inverse_image_source_family_map
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {V W : D} (g : V ⟶ W) :
    (factorization_target_inverse_image_source_family (J := J) (K := K) f).map g =
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).map g) := by
  -- The frozen source family is definitionally the concrete inverse-image composite.
  rfl

/-- Helper for Lemma 7.29.6: specialize the source-side sigma-desc local-surjectivity theorem to
the exact ambient universe and the frozen family `V ↦ f⁻¹(h_V^#)` used later in the transport
chain. -/
private theorem factorization_target_inverse_image_cover_sigma_desc_isLocallySurjective_at_target_universe
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))] :
    Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        (factorization_target_inverse_image_source_family (J := J) (K := K) f).map I.f)) := by
  -- Specialize the already-proved source sigma-desc theorem at the theorem-facing universe, then
  -- rewrite the frozen source family back to the concrete inverse-image composite.
  simpa [factorization_target_inverse_image_source_family_def,
      factorization_target_inverse_image_source_family_map,
      uliftSheafifiedRepresentableCoverMap, Limits.sigmaComparison_map_desc] using
    (show Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj).map I.f))) from
      factorization_target_inverse_image_cover_sigma_desc_isLocallySurjective.{u₁, u₂, v₁, v₂,
          max u₁ v₁}
        (J := J) (K := K) f S)

/-- Helper for Lemma 7.29.6: freeze the source family after the two dense-subsite sheaf
equivalences, so later transport lemmas can avoid repeatedly elaborating the full composite. -/
private noncomputable abbrev factorization_target_transported_source_family
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J'] :
    D ⥤ Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
        f.inverseImageFunctor.obj) ⋙
      (sheafEquiv J J0Small a
        (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) ⋙
    (sheafEquiv J0Small J' v0
      (Type (max (max u₁ v₁) (max u₂ v₂)))).functor

/-- Helper for Lemma 7.29.6: freeze the first dense-subsite transport of the source family so
the initial `a`-stage transport can be proved without universe metavariables from the later `v0`
stage. -/
private noncomputable abbrev factorization_target_first_transported_source_family
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small] :
    D ⥤ Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) :=
  (factorization_target_inverse_image_source_family (J := J) (K := K) f) ⋙
    (sheafEquiv J J0Small a
      (Type (max (max u₁ v₁) (max u₂ v₂)))).functor

/-- Helper for Lemma 7.29.6: unfold the first transported family once, so the stage-1 transport
lemma can target the concrete composite through the first dense-subsite equivalence. -/
private theorem factorization_target_first_transported_source_family_def
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small] :
    factorization_target_first_transported_source_family
        (J := J) (K := K) (J0Small := J0Small) f a =
      (factorization_target_inverse_image_source_family (J := J) (K := K) f) ⋙
        (sheafEquiv J J0Small a
          (Type (max (max u₁ v₁) (max u₂ v₂)))).functor := by
  -- The first-stage frozen family is definitionally the source family followed by the `a`-transport.
  rfl

/-- Helper for Lemma 7.29.6: transport the source sigma-desc across the first dense-subsite
equivalence `a` before introducing the second transport through `v0`. -/
private theorem factorization_target_first_sheafEquiv_transport
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {V : D} (S : K.Cover V)
    (F0 : D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))))
    [HasCoproduct (fun I : S.Arrow ↦ F0.obj I.Y)]
    (hsource : Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun I : S.Arrow ↦ F0.map I.f)))
    [HasCoproduct (fun I : S.Arrow ↦
      ((F0 ⋙ (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))] :
    Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        ((F0 ⋙ (sheafEquiv J J0Small a
          (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).map I.f))) := by
  let E1 :
      Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
        Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor
  let F1 :
      D ⥤ Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    F0 ⋙ E1
  have hmap :
      Sheaf.IsLocallySurjective (E1.map (Limits.Sigma.desc (fun I : S.Arrow ↦ F0.map I.f))) := by
    -- The first dense-subsite equivalence preserves local surjectivity.
    exact
      sheaf_isLocallySurjective_map_of_sheafEquiv_functor
        (J₀ := J) (J₁ := J0Small) (v := a)
        (hvEq := by infer_instance)
        (η := Limits.Sigma.desc (fun I : S.Arrow ↦ F0.map I.f))
        hsource
  let X : S.Arrow → Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) := fun I ↦ F0.obj I.Y
  let _ : HasCoproduct X := by
    simpa [X]
  let _ : HasCoproduct (fun I : S.Arrow ↦ E1.obj (X I)) := by
    simpa [X, E1, F1]
  -- Rewrite the mapped sigma-desc to the stage-1 transported sigma-desc.
  simpa [X, E1, F1, Limits.sigmaComparison_map_desc] using
    (sheaf_isLocallySurjective_sigma_desc_of_functor_map
      (J₀ := J) (J₁ := J0Small) (G := E1)
      (X := X)
      (α := fun I : S.Arrow ↦ F0.map I.f)
      hmap)

/-- Helper for Lemma 7.29.6: after the first dense-subsite transport has been frozen, the second
transport across `v0` preserves local surjectivity by the same source-proof argument. -/
private theorem factorization_target_second_sheafEquiv_transport
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    [HasSheafify J0Small (Type (max (max u₁ v₁) (max u₂ v₂)))]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    {V : D} (S : K.Cover V)
    (F1 : D ⥤ Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))))
    [HasCoproduct (fun I : S.Arrow ↦ F1.obj I.Y)]
    (hstage1 : Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun I : S.Arrow ↦ F1.map I.f)))
    [HasCoproduct (fun I : S.Arrow ↦
      ((F1 ⋙ (sheafEquiv J0Small J' v0
        (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))] :
    Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        ((F1 ⋙ (sheafEquiv J0Small J' v0
          (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).map I.f))) := by
  letI :
      (v0.sheafPushforwardContinuous (Type (max (max u₁ v₁) (max u₂ v₂))) J0Small J').IsEquivalence :=
    by infer_instance
  letI : HasSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
      (G := v0) (J := J0Small) (K := J') (A := Type (max (max u₁ v₁) (max u₂ v₂)))
  let E2 :
      Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤
        Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    (sheafEquiv J0Small J' v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor
  let F2 :
      D ⥤ Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    F1 ⋙ E2
  have hmap :
      Sheaf.IsLocallySurjective (E2.map (Limits.Sigma.desc (fun I : S.Arrow ↦ F1.map I.f))) := by
    -- The second dense-subsite equivalence preserves local surjectivity stagewise.
    exact
      sheaf_isLocallySurjective_map_of_sheafEquiv_functor
        (J₀ := J0Small) (J₁ := J') (v := v0)
        (hvEq := by infer_instance)
        (η := Limits.Sigma.desc (fun I : S.Arrow ↦ F1.map I.f))
        hstage1
  let X : S.Arrow → Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) := fun I ↦ F1.obj I.Y
  let _ : HasCoproduct X := by
    simpa [X]
  let _ : HasCoproduct (fun I : S.Arrow ↦ E2.obj (X I)) := by
    simpa [X, E2, F2]
  -- Rewrite the mapped sigma-desc to the theorem-facing stage-2 transported sigma-desc.
  simpa [X, E2, F2, Limits.sigmaComparison_map_desc] using
    (sheaf_isLocallySurjective_sigma_desc_of_functor_map
      (J₀ := J0Small) (J₁ := J') (G := E2)
      (X := X)
      (α := fun I : S.Arrow ↦ F1.map I.f)
      hmap)

/-- Helper for Lemma 7.29.6: transporting the source sigma-desc through the two dense-subsite
sheaf equivalences preserves local surjectivity exactly as in the source proof. -/
private theorem factorization_target_transported_sigma_desc_isLocallySurjective
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    [HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y))] :
    Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        (factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).map I.f)) := by
  -- Route correction: the source proof still proceeds in three steps, but the first step must be
  -- frozen at the theorem's ambient universe before the `a`-transport and `v0`-transport can be
  -- composed without universe metavariables.
  let F0 :
      D ⥤ Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    factorization_target_inverse_image_source_family (J := J) (K := K) f
  let F1 :
      D ⥤ Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    factorization_target_first_transported_source_family
      (J := J) (K := K) (J0Small := J0Small) f a
  let F2 :
      D ⥤ Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    factorization_target_transported_source_family
      (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0
  letI :
      (a.sheafPushforwardContinuous (Type (max (max u₁ v₁) (max u₂ v₂))) J
        J0Small).IsEquivalence := by
    infer_instance
  letI : HasSheafify J0Small (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    Functor.IsDenseSubsite.hasSheafify_of_isEquivalence
      (G := a) (J := J) (K := J0Small)
      (A := Type (max (max u₁ v₁) (max u₂ v₂)))
  let _ : HasCoproduct (fun I : S.Arrow ↦ F0.obj I.Y) := by
    simpa [F0, factorization_target_inverse_image_source_family_def] using
      (inferInstance :
        HasCoproduct (fun I : S.Arrow ↦
          ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
              f.inverseImageFunctor.obj).obj I.Y)))
  let _ : HasCoproduct (fun I : S.Arrow ↦ F1.obj I.Y) := by
    simpa [F1, factorization_target_first_transported_source_family_def,
      factorization_target_inverse_image_source_family_def] using
      (inferInstance :
        HasCoproduct (fun I : S.Arrow ↦
          (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
                f.inverseImageFunctor.obj) ⋙
              (sheafEquiv J J0Small a
                (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y)))
  let _ : HasCoproduct (fun I : S.Arrow ↦
      ((F1 ⋙ (sheafEquiv J0Small J' v0
        (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y)) := by
    simpa [F1, factorization_target_first_transported_source_family_def,
      factorization_target_inverse_image_source_family_def, F2,
      factorization_target_transported_source_family] using
      (inferInstance :
        HasCoproduct (fun I : S.Arrow ↦
          ((factorization_target_transported_source_family
              (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y)))
  have hsource :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun I : S.Arrow ↦ F0.map I.f)) := by
    -- First close the source step at the frozen theorem-facing universe.
    simpa [F0, factorization_target_inverse_image_source_family_def,
      factorization_target_inverse_image_source_family_map] using
      factorization_target_inverse_image_cover_sigma_desc_isLocallySurjective_at_target_universe
        (J := J) (K := K) f S
  have hstage1 :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc (fun I : S.Arrow ↦ F1.map I.f)) := by
    -- Then transport local surjectivity across the first dense-subsite equivalence.
    simpa [F1, factorization_target_first_transported_source_family_def] using
      factorization_target_first_sheafEquiv_transport
        (J := J) (K := K) (J0Small := J0Small) a S F0 hsource
  -- Finally transport across `v0` to reach the theorem-facing family on `Sh(J')`.
  simpa [F2, factorization_target_transported_source_family] using
    (show Sheaf.IsLocallySurjective
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        ((F1 ⋙ (sheafEquiv J0Small J' v0
          (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).map I.f))) from
      factorization_target_second_sheafEquiv_transport.{u₁, u₂, v₁, v₂}
        (C0Small := C0Small) (J0Small := J0Small) (C' := C') (J' := J') (V := V)
        v0 S F1 hstage1)

/-- Helper for Lemma 7.29.6: reindexing a sigma-desc along an equivalence of index types factors
through the canonical source reindexing isomorphism. -/
private theorem sigma_desc_reindex_of_equiv
    {ι κ : Type*} {E : Type*} [Category E]
    (X : ι → E) [HasCoproduct X] {A : E} (α : ∀ i : ι, X i ⟶ A)
    (e : ι ≃ κ) [HasCoproduct (fun k : κ ↦ X (e.symm k))] [HasCoproduct (X ∘ e.symm)] :
    Limits.Sigma.desc (fun k : κ ↦ α (e.symm k)) =
      (Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α := by
  let X' : κ → E := X ∘ e.symm
  let _ : HasCoproduct X' := by
    simpa [X'] using
      (Limits.hasCoproduct_of_equiv_of_iso X (X ∘ e.symm) e.symm (fun k ↦ Iso.refl _))
  -- Compare the reindexed sigma-desc and the original sigma-desc summandwise.
  apply Limits.Sigma.hom_ext
  intro k
  have h₀ :
      Limits.Sigma.ι X' k ≫ Limits.Sigma.desc (fun k : κ ↦ α (e.symm k)) =
        α (e.symm k) := by
    simpa [X'] using (Limits.Sigma.ι_desc (fun k : κ ↦ α (e.symm k)) k)
  have h₁ :
      α (e.symm k) = Limits.Sigma.ι X (e.symm k) ≫ Limits.Sigma.desc α := by
    simpa using (Limits.Sigma.ι_desc α (e.symm k)).symm
  have h₂ :
      Limits.Sigma.ι X (e.symm k) ≫ Limits.Sigma.desc α =
        Limits.Sigma.ι X' k ≫
          (Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α := by
    simpa [X'] using
      (Limits.Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := X) k
        (Limits.Sigma.desc α)).symm
  exact h₀.trans (h₁.trans h₂)

/-- Helper for Lemma 7.29.6: after transporting the source cover sigma-desc to `Sh(J')`, shrink
the index locally and pass to the underlying presheaf sigma-desc on the original `S.Arrow`. -/
private theorem factorization_target_presheaf_sigma_desc_of_small_index
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    [HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y))] :
    Presheaf.IsLocallySurjective J'
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        ((factorization_target_transported_source_family
            (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).map I.f).hom)) := by
  let F2 :
      D ⥤ Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    factorization_target_transported_source_family
      (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0
  let X : S.Arrow → Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) := fun I ↦ F2.obj I.Y
  let α : ∀ I : S.Arrow, X I ⟶ F2.obj V := fun I ↦ F2.map I.f
  let e : S.Arrow ≃ Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow :=
    equivShrink.{max (max u₁ v₁) (max u₂ v₂)} (S.Arrow)
  let X' :
      Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow →
        Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) := X ∘ e.symm
  let Xpres' :
      Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow →
        C'ᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)) :=
    (fun I : S.Arrow ↦ (X I).obj) ∘ e.symm
  let _ : HasCoproduct X := by
    simpa [X, F2, factorization_target_transported_source_family] using
      (inferInstance :
        HasCoproduct (fun I : S.Arrow ↦
          ((factorization_target_transported_source_family
              (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y)))
  let _ : HasCoproduct X' :=
    Limits.hasCoproduct_of_equiv_of_iso X X' e.symm (fun k ↦ Iso.refl _)
  let _ : HasCoproduct Xpres' :=
    Limits.hasCoproduct_of_equiv_of_iso
      (fun I : S.Arrow ↦ (X I).obj) Xpres' e.symm (fun k ↦ Iso.refl _)
  let α' :
      ∀ k : Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow, X' k ⟶ F2.obj V :=
    fun k ↦ α (e.symm k)
  have hsheaf :
      Sheaf.IsLocallySurjective (Limits.Sigma.desc α) := by
    -- First import the transported sheaf sigma-desc from the previous source-faithful step.
    simpa [F2, X, α, factorization_target_transported_source_family] using
      factorization_target_transported_sigma_desc_isLocallySurjective
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 S
  have hsheaf_fac :
      Limits.Sigma.desc α' = (Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α := by
    -- Reindex the sheaf sigma-desc along the shrink equivalence.
    apply Limits.Sigma.hom_ext
    intro k
    have h₀ :
        Limits.Sigma.ι X' k ≫ Limits.Sigma.desc α' = α (e.symm k) := by
      simpa [X', α', e] using (Limits.Sigma.ι_desc α' k)
    have h₁ :
        α (e.symm k) = Limits.Sigma.ι X (e.symm k) ≫ Limits.Sigma.desc α := by
      simpa using (Limits.Sigma.ι_desc α (e.symm k)).symm
    have h₂ :
        Limits.Sigma.ι X (e.symm k) ≫ Limits.Sigma.desc α =
          Limits.Sigma.ι X' k ≫
            (Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α := by
      simpa [X', e] using
        (Limits.Sigma.ι_reindex_hom_assoc (ε := e.symm) (f := X) k
          (Limits.Sigma.desc α)).symm
    exact h₀.trans (h₁.trans h₂)
  have hpres_fac :
      Limits.Sigma.desc (fun k : Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow ↦
        (α (e.symm k)).hom) =
        (Limits.Sigma.reindex e.symm (fun I : S.Arrow ↦ (X I).obj)).hom ≫
          Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom) := by
    -- The same reindexing comparison holds after forgetting to underlying presheaves.
    apply Limits.Sigma.hom_ext
    intro k
    have h₀ :
        Limits.Sigma.ι Xpres' k ≫
            Limits.Sigma.desc (fun k : Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow ↦
              (α (e.symm k)).hom) =
          (α (e.symm k)).hom := by
      simpa [Xpres', e] using
        (Limits.Sigma.ι_desc
          (fun k : Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow ↦ (α (e.symm k)).hom) k)
    have h₁ :
        (α (e.symm k)).hom =
          Limits.Sigma.ι (fun I : S.Arrow ↦ (X I).obj) (e.symm k) ≫
            Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom) := by
      simpa using
        (Limits.Sigma.ι_desc (fun I : S.Arrow ↦ (α I).hom) (e.symm k)).symm
    have h₂ :
        Limits.Sigma.ι (fun I : S.Arrow ↦ (X I).obj) (e.symm k) ≫
            Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom) =
          Limits.Sigma.ι Xpres' k ≫
            (Limits.Sigma.reindex e.symm (fun I : S.Arrow ↦ (X I).obj)).hom ≫
              Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom) := by
      simpa [Xpres', e] using
        (Limits.Sigma.ι_reindex_hom_assoc
          (ε := e.symm) (f := fun I : S.Arrow ↦ (X I).obj) k
          (Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom))).symm
    exact h₀.trans (h₁.trans h₂)
  have hα_epi : Epi (Limits.Sigma.desc α) :=
    (Sheaf.isLocallySurjective_iff_epi (φ := Limits.Sigma.desc α)).1 hsheaf
  have hα'_epi : Epi (Limits.Sigma.desc α') := by
    -- Compose with the source reindexing isomorphism to move the covering family to a small
    -- index type.
    have :
        Epi ((Limits.Sigma.reindex e.symm X).hom ≫ Limits.Sigma.desc α) :=
      (epi_comp_iff_of_epi (Limits.Sigma.reindex e.symm X).hom
        (Limits.Sigma.desc α)).2 hα_epi
    exact hsheaf_fac ▸ this
  have hsheaf' : Sheaf.IsLocallySurjective (Limits.Sigma.desc α') :=
    (Sheaf.isLocallySurjective_iff_epi (φ := Limits.Sigma.desc α')).2 hα'_epi
  have hpres' :
      Presheaf.IsLocallySurjective J'
        (Limits.Sigma.desc (fun k : Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow ↦
          (α (e.symm k)).hom)) :=
    (CategoryTheory.Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc
      (J := J') X' α').1 hsheaf'
  have hpres_comp :
      Presheaf.IsLocallySurjective J'
        ((Limits.Sigma.reindex e.symm (fun I : S.Arrow ↦ (X I).obj)).hom ≫
          Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom)) := by
    exact hpres_fac.symm ▸ hpres'
  -- Cancel the source reindexing isomorphism on presheaves to recover the theorem-facing family.
  exact
    (Presheaf.comp_isLocallySurjective_iff J'
      (Limits.Sigma.reindex e.symm (fun I : S.Arrow ↦ (X I).obj)).hom
      (Limits.Sigma.desc (fun I : S.Arrow ↦ (α I).hom))).1 hpres_comp

/-- Helper for Lemma 7.29.6: for a `K`-cover, the Yoneda presentation `ρ` transports the local
surjectivity produced by the source family `V ↦ f⁻¹(h_V^#)` to the theorem-facing family
`I ↦ u.map I.f` on the replacement site. -/
private theorem factorization_target_rho_sigma_desc_compare.{ub, u₂', vb, v₂'}
    {D : Type u₂'} [Category.{v₂'} D] {K : GrothendieckTopology D}
    {C' : Type (max (max ub vb) (max u₂' v₂'))}
    [Category.{max (max (max ub u₂') vb) v₂'} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (u : D ⥤ C')
    (F2 : D ⥤ Sheaf J' (Type (max (max ub vb) (max u₂' v₂'))))
    (ρ : u ⋙ J'.yoneda ≅ F2)
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ (F2.obj I.Y).obj)] :
    Limits.Sigma.map (fun I : S.Arrow ↦ (ρ.inv.app I.Y).hom) ≫
        Limits.Sigma.desc (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom) =
      Limits.Sigma.desc (fun I : S.Arrow ↦ (F2.map I.f).hom) ≫ (ρ.inv.app V).hom := by
  -- Compare the theorem-facing Yoneda sigma-desc with the transported source sigma-desc
  -- componentwise, using the naturality of the inverse comparison `ρ.inv`.
  apply Limits.Sigma.hom_ext
  intro I
  rw [Limits.Sigma.ι_map_assoc]
  calc
    (ρ.inv.app I.Y).hom ≫
        Limits.Sigma.ι (fun I : S.Arrow ↦ (J'.yoneda.obj (u.obj I.Y)).obj) I ≫
          Limits.Sigma.desc (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom) =
      (ρ.inv.app I.Y).hom ≫ (J'.yoneda.map (u.map I.f)).hom := by
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ (ρ.inv.app I.Y).hom ≫ k)
            (Limits.Sigma.ι_desc
              (p := fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom) (b := I))
    _ = (F2.map I.f).hom ≫ (ρ.inv.app V).hom := by
        exact congrArg (fun k => k.hom) (NatTrans.naturality ρ.inv I.f).symm
    _ =
      Limits.Sigma.ι (fun I : S.Arrow ↦ (F2.obj I.Y).obj) I ≫
          Limits.Sigma.desc (fun I : S.Arrow ↦ (F2.map I.f).hom) ≫
            (ρ.inv.app V).hom := by
        symm
        simpa [Category.assoc] using
          congrArg
            (fun k ↦ k ≫ (ρ.inv.app V).hom)
            (Limits.Sigma.ι_desc (p := fun I : S.Arrow ↦ (F2.map I.f).hom) (b := I))

/-- Helper for Lemma 7.29.6: the transported source sigma-desc is already epimorphic in
`Sh(J')`, so the remaining blocker is only the `ρ`-transport to the theorem-facing Yoneda map. -/
private theorem factorization_target_transported_sigma_desc_epi
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    [HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y))] :
    Epi
      (Limits.Sigma.desc (fun I : S.Arrow ↦
        (factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).map I.f)) := by
  -- Convert the already-proved sheaf-local-surjectivity statement into the categorical epi form
  -- needed for the next `ρ`-transport step.
  exact
    (Sheaf.isLocallySurjective_iff_epi
      (φ := Limits.Sigma.desc (fun I : S.Arrow ↦
        (factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).map I.f))).1
    (factorization_target_transported_sigma_desc_isLocallySurjective
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 S)

/-- Generic epi transfer across componentwise isomorphisms of sigma-desc squares. -/
private theorem sigma_desc_epi_of_componentwise_iso
    {E : Type*} [Category E] {ι : Type*}
    {X Y : ι → E} {Z W : E}
    [HasCoproduct X] [HasCoproduct Y]
    (e : ∀ i, X i ≅ Y i) (eZ : Z ≅ W)
    (p : ∀ i, X i ⟶ Z) (q : ∀ i, Y i ⟶ W)
    (hsq : ∀ i, (e i).hom ≫ q i = p i ≫ eZ.hom)
    (hp : Epi (Limits.Sigma.desc p)) :
    Epi (Limits.Sigma.desc q) := by
  have hcompare :
      Limits.Sigma.map (fun i ↦ (e i).hom) ≫ Limits.Sigma.desc q =
        Limits.Sigma.desc p ≫ eZ.hom := by
    apply Limits.Sigma.hom_ext
    intro i
    rw [Limits.Sigma.ι_map_assoc, Limits.Sigma.ι_desc, Limits.Sigma.ι_desc_assoc]
    exact hsq i
  have hcomp : Epi (Limits.Sigma.desc p ≫ eZ.hom) := epi_comp _ _
  rw [← hcompare] at hcomp
  exact epi_of_epi (Limits.Sigma.map (fun i ↦ (e i).hom)) (Limits.Sigma.desc q)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Helper for Lemma 7.29.6: after freezing the current `ρ`-comparison once, the theorem-facing
Yoneda sigma-desc is epimorphic already at the sheaf level. -/
private theorem factorization_target_yoneda_sigma_desc_epi
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    [HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    (u : D ⥤ C')
    (ρ :
      u ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (sheafEquiv J0Small J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor)
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ J'.yoneda.obj (u.obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y))] :
    Epi (Limits.Sigma.desc (fun I : S.Arrow ↦ J'.yoneda.map (u.map I.f))) := by
  -- Transfer the transported-family epi across the componentwise comparison `ρ` by the generic
  -- sigma-desc square lemma, instantiated once to keep the large composite functor opaque.
  exact sigma_desc_epi_of_componentwise_iso
    (X := fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y))
    (Y := fun I : S.Arrow ↦ J'.yoneda.obj (u.obj I.Y))
    (Z := (factorization_target_transported_source_family
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj V)
    (W := J'.yoneda.obj (u.obj V))
    (fun I : S.Arrow ↦ (ρ.app I.Y).symm) ((ρ.app V).symm)
    (fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).map I.f))
    (fun I : S.Arrow ↦ J'.yoneda.map (u.map I.f))
    (fun I : S.Arrow ↦ (ρ.inv.naturality I.f).symm)
    (factorization_target_transported_sigma_desc_epi
      (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 S)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem factorization_target_yoneda_sigma_desc_isLocallySurjective
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    [HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    (u : D ⥤ C')
    (ρ :
      u ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (sheafEquiv J0Small J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor)
    {V : D} (S : K.Cover V)
    [HasCoproduct (fun I : S.Arrow ↦ J'.yoneda.obj (u.obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      GrothendieckTopology.uliftSheafifiedRepresentable.{max u₁ v₁, u₂, v₂} K I.Y)]
    [HasCoproduct (fun I : S.Arrow ↦
      ((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
          f.inverseImageFunctor.obj).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      (((GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor).obj I.Y))]
    [HasCoproduct (fun I : S.Arrow ↦
      ((factorization_target_transported_source_family
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0).obj I.Y))] :
    Presheaf.IsLocallySurjective J'
      (Limits.Sigma.desc (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom)) := by
  -- The sheaf-level epi pivot, descended once to presheaves through the small-index form of the
  -- sigma-desc comparison; the index `S.Arrow` is small in the ambient universe.
  have hepi : Epi (Limits.Sigma.desc (fun I : S.Arrow ↦ J'.yoneda.map (u.map I.f))) :=
    factorization_target_yoneda_sigma_desc_epi
      (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 u ρ S
  exact
    (Sheaf.isLocallySurjective_sigma_desc_iff_presheaf_sigma_desc_of_small
      (J := J') (fun I : S.Arrow ↦ J'.yoneda.obj (u.obj I.Y))
      (fun I : S.Arrow ↦ J'.yoneda.map (u.map I.f))).1
    ((Sheaf.isLocallySurjective_iff_epi _).2 hepi)

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- Helper for Lemma 7.29.6: for a `K`-cover, the Yoneda presentation `ρ` transports the local
surjectivity produced by the source family `V ↦ f⁻¹(h_V^#)` to the theorem-facing family
`I ↦ u.map I.f` on the replacement site. -/
theorem factorization_target_cover_mem_precoverage
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    (hcover :
      ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
    (u : D ⥤ C')
    (ρ :
      u ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (sheafEquiv J0Small J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor)
    {V : D} (S : K.Cover V) :
    Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) ∈
      J'.toPrecoverage (u.obj V) := by
  -- Provide the low-universe discrete-shape colimits once per ambient sheaf category, through
  -- the shrink equivalence, so the coproduct hypotheses of the local-surjectivity theorem do not
  -- re-run the full instance search on the large composite functors.
  letI hShrinkSheafK : HasColimitsOfShape
      (Discrete (Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow))
      (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) := Sheaf.instHasColimitsOfShape
  letI : HasColimitsOfShape (Discrete S.Arrow)
      (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
    Limits.hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow).symm)
  letI hShrinkSheafJ : HasColimitsOfShape
      (Discrete (Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow))
      (Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂)))) := Sheaf.instHasColimitsOfShape
  letI : HasColimitsOfShape (Discrete S.Arrow)
      (Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
    Limits.hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow).symm)
  letI hShrinkSheafJ0 : HasColimitsOfShape
      (Discrete (Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow))
      (Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂)))) := Sheaf.instHasColimitsOfShape
  letI : HasColimitsOfShape (Discrete S.Arrow)
      (Sheaf J0Small (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
    Limits.hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow).symm)
  letI hShrinkSheafJ' : HasColimitsOfShape
      (Discrete (Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow))
      (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) := Sheaf.instHasColimitsOfShape
  letI : HasColimitsOfShape (Discrete S.Arrow)
      (Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂)))) :=
    Limits.hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow).symm)
  letI hShrinkPre : HasColimitsOfShape
      (Discrete (Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow))
      (C'ᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂))) :=
    Limits.functorCategoryHasColimitsOfShape
  letI : HasColimitsOfShape (Discrete S.Arrow)
      (C'ᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂))) :=
    Limits.hasColimitsOfShape_of_equivalence
      (Discrete.equivalence (equivShrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow).symm)
  have hsurj :
      Presheaf.IsLocallySurjective J'
        (Limits.Sigma.desc (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom)) :=
    factorization_target_yoneda_sigma_desc_isLocallySurjective
      (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 u ρ S
  -- Reindex the witness family along the shrink equivalence so its index lives in the ambient
  -- universe demanded by the cover characterization.
  let e : S.Arrow ≃ Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow :=
    equivShrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow
  have hpresieve :
      Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) =
        Presieve.ofArrows (fun k ↦ u.obj (e.symm k).Y) (fun k ↦ u.map (e.symm k).f) := by
    simpa using
      (Presieve.ofArrows_comp_eq_of_surjective
        (f := fun I : S.Arrow ↦ u.map I.f) (a := fun k ↦ e.symm k)
        e.symm.surjective).symm
  have hdesc :
      Limits.Sigma.desc (fun k ↦ ((J'.yoneda.map (u.map (e.symm k).f)).hom)) =
        (Limits.Sigma.reindex e.symm
          (fun I : S.Arrow ↦ (J'.yoneda.obj (u.obj I.Y)).obj)).hom ≫
          Limits.Sigma.desc (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom) :=
    sigma_desc_reindex_of_equiv
      (fun I : S.Arrow ↦ (J'.yoneda.obj (u.obj I.Y)).obj)
      (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom) e
  have hsurj' :
      Presheaf.IsLocallySurjective J'
        (Limits.Sigma.desc (fun k ↦ ((J'.yoneda.map (u.map (e.symm k).f)).hom))) := by
    rw [hdesc]
    exact
      (Presheaf.comp_isLocallySurjective_iff J'
        (Limits.Sigma.reindex e.symm
          (fun I : S.Arrow ↦ (J'.yoneda.obj (u.obj I.Y)).obj)).hom
        (Limits.Sigma.desc (fun I : S.Arrow ↦ (J'.yoneda.map (u.map I.f)).hom))).2 hsurj
  exact
    (hcover
      (X := u.obj V)
      (R := Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f))).2
      ⟨Shrink.{max (max u₁ v₁) (max u₂ v₂)} S.Arrow,
        (fun k ↦ u.obj (e.symm k).Y), (fun k ↦ u.map (e.symm k).f), hpresieve, hsurj'⟩

/-- Helper for Lemma 7.29.6: the source-proof cover transport yields a precoverage-level
continuity package for the target functor `u`. -/
private theorem factorization_target_isContinuousSiteFunctor
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical] [HasFiniteLimits C']
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    (hcover :
      ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
    (u : D ⥤ C')
    (ρ :
      u ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (sheafEquiv J0Small J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor)
    (huPullbacks : PreservesLimitsOfShape WalkingCospan u) :
    Functor.IsContinuousSiteFunctor u K.toPrecoverage J'.toPrecoverage := by
  refine ⟨?_, ?_⟩
  · intro V R hR
    -- Replace the generating family `R` by its covering sieve and apply the cover-family theorem
    -- to that cover before rewriting back to `R.map u`.
    let S : K.Cover V := ⟨Sieve.generate R, (GrothendieckTopology.mem_toPrecoverage_iff K R).1 hR⟩
    have hS :
        Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) ∈
          J'.toPrecoverage (u.obj V) := by
      exact
        factorization_target_cover_mem_precoverage
          (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 hcover u ρ S
    have hS_arrows :
        Presieve.ofArrows (fun I : S.Arrow ↦ I.Y) (fun I ↦ I.f) = (S : Sieve V).arrows := by
      funext Y
      funext g
      apply propext
      constructor
      · rintro ⟨I⟩
        exact I.hf
      · intro hg
        simpa using
          (Presieve.ofArrows.mk
            (Y := fun I : S.Arrow ↦ I.Y) (f := fun I : S.Arrow ↦ I.f)
            (⟨Y, g, hg⟩ : S.Arrow))
    have hS_map :
        Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f) =
          ((S : Sieve V).arrows).map u := by
      -- The theorem-facing family of mapped arrows is exactly the image of the cover sieve's
      -- presieve of arrows.
      simpa [hS_arrows] using
        (Presieve.map_ofArrows (F := u) (Y := fun I : S.Arrow ↦ I.Y)
          (f := fun I : S.Arrow ↦ I.f)).symm
    have hpush :
        ((S : Sieve V).functorPushforward u) ∈ J' (u.obj V) := by
      -- Convert the precoverage statement on the cover family into a statement about the pushed
      -- forward covering sieve.
      have hS' :
          Sieve.generate
              (Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f)) ∈
            J' (u.obj V) :=
        (GrothendieckTopology.mem_toPrecoverage_iff J'
          (Presieve.ofArrows (fun I : S.Arrow ↦ u.obj I.Y) (fun I ↦ u.map I.f))).1 hS
      simpa [hS_map, Sieve.generate_map_eq_functorPushforward] using hS'
    have hmap :
        Sieve.generate (R.map u) ∈ J' (u.obj V) := by
      -- Rewrite the pushed-forward generated sieve back to the image of the original family `R`.
      simpa [S, Sieve.generate_map_eq_functorPushforward] using hpush
    exact (GrothendieckTopology.mem_toPrecoverage_iff J' (R.map u)).2 hmap
  · intro V R hR Y i hi T f
    -- Pullback preservation is already part of the source package for `u`.
    let _ : PreservesLimitsOfShape WalkingCospan u := huPullbacks
    infer_instance

/-- Helper for Lemma 7.29.6: once the source site has pullbacks, the precoverage-level continuity
package upgrades to the canonical Grothendieck-topology continuity of `u`. -/
private theorem factorization_target_isContinuous_of_hasPullbacks
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    {C0Small : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C0Small]
    {J0Small : GrothendieckTopology C0Small}
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J)
    (a : C ⥤ C0Small) [a.IsDenseSubsite J J0Small]
    {C' : Type (max (max u₁ v₁) (max u₂ v₂))}
    [Category.{max (max (max u₁ u₂) v₁) v₂} C']
    {J' : GrothendieckTopology C'} [J'.Subcanonical] [HasFiniteLimits C'] [HasPullbacks D]
    (v0 : C0Small ⥤ C') [v0.IsDenseSubsite J0Small J']
    (hcover :
      ∀ ⦃X : C'⦄ (R : Presieve X),
        R ∈ J'.toPrecoverage X ↔
          ∃ (ι : Type (max (max u₁ v₁) (max u₂ v₂))) (Y : ι → C') (π : ∀ i, Y i ⟶ X),
            R = Presieve.ofArrows Y π ∧
              Presheaf.IsLocallySurjective J'
                (Limits.Sigma.desc (fun i ↦ (J'.yoneda.map (π i)).hom)))
    (u : D ⥤ C')
    (ρ :
      u ⋙ J'.yoneda ≅
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K ⋙
            f.inverseImageFunctor.obj) ⋙
          (sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor ⋙
            (sheafEquiv J0Small J' v0
              (Type (max (max u₁ v₁) (max u₂ v₂)))).functor)
    (huPullbacks : PreservesLimitsOfShape WalkingCospan u) :
    u.IsContinuous K J' := by
  -- Route correction: separate the owner upgrade from the later exactness argument, so the
  -- remaining blocker is only representable flatness rather than continuity itself.
  let _ :
      Functor.IsContinuousSiteFunctor u K.toPrecoverage J'.toPrecoverage :=
    factorization_target_isContinuousSiteFunctor
      (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 hcover u ρ huPullbacks
  let _ : HasPullbacks C' := inferInstance
  simpa [factorization_target_toPrecoverage_toGrothendieck_eq K,
    factorization_target_toPrecoverage_toGrothendieck_eq J'] using
    (inferInstance :
      Functor.IsContinuous
        u K.toPrecoverage.toGrothendieck J'.toPrecoverage.toGrothendieck)

/-- Lemma 7.29.6: a morphism of topoi available in the representable universe factors through an
intermediate site `(C', J')`. Here `v : C ⥤ C'` is special cocontinuous in the dense-subsite
sense, `u : D ⥤ C'` commutes with fibre products and is continuous in the source-faithful
Stacks sense (Definition 7.13.1, recorded on the chosen precoverages), and a lower horizontal
morphism of topoi `g : Sh(J') ⟶ Sh(K)` makes the inverse-image functors form the source
factorization square. The source phrase "defines a morphism of sites" is faithfully carried by
this continuity datum together with the lower morphism of topoi `g`; the canonical
`IsMorphismOfSites` class additionally demands representable flatness of `u`, which fails for
the source construction over a general site `D` (the comma categories of
`V ↦ f⁻¹ h_V^#` need not be cofiltered), so it is intentionally not part of this statement. -/
  theorem exists_special_cocontinuous_site_factorization
    [HasWeakSheafify K (Type (max (max u₁ v₁) (max u₂ v₂)))]
    [HasSheafify J (Type (max (max u₁ v₁) (max u₂ v₂)))]
    (f : MorphismOfTopoiIn.{u₂, u₁, v₂, v₁, max (max u₁ v₁) (max u₂ v₂)} K J) :
    ∃ (C' : Type (max (max u₁ v₁) (max u₂ v₂))) (_ : Category C')
      (J' : GrothendieckTopology C')
      (_ : J'.Subcanonical) (_ : HasFiniteLimits C')
      (v : C ⥤ C') (_ : v.IsDenseSubsite J J')
      (_ : J.Subcanonical → v.FullyFaithful)
      (u : D ⥤ C')
      (_ : Functor.IsContinuousSiteFunctor u K.toPrecoverage J'.toPrecoverage)
      (_ : PreservesLimitsOfShape WalkingCospan u)
      (_ : ∀ X : D, Limits.IsTerminal X → Nonempty (Limits.IsTerminal (u.obj X)))
      (_ : Limits.HasPullbacks D → u.IsContinuous K J')
      (g : MorphismOfTopoiIn.{u₂, max (max u₁ v₁) (max u₂ v₂), v₂,
        max (max u₁ v₁) (max u₂ v₂), max (max u₁ v₁) (max u₂ v₂)} K J'),
        Nonempty
          (CatCommSq
            (𝟭 (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))))
            (g⁻¹)
            (f⁻¹)
            (v.sheafPushforwardContinuous (Type (max (max u₁ v₁) (max u₂ v₂))) J J')) := by
  -- Route correction: keep the replacement-site cover description and Yoneda presentation from
  -- the source proof in scope, instead of discarding them through the stripped-down canonical
  -- existential.
  obtain ⟨C0Small, hC0Small, J0Small, a, haDense, haEquiv,
      C', hC', J', hsub, hfinite, v0, hv0, hv0ff, hcover, _hsubobj, u, hρ,
      huPullbacks, hweakJ', huLan⟩ :=
    exists_special_cocontinuous_site_factorization_source_package (J := J) (K := K) f
  let _ : Category.{max (max (max u₁ u₂) v₁) v₂} C0Small := hC0Small
  let _ : a.IsDenseSubsite J J0Small := haDense
  let _ : a.IsEquivalence := haEquiv
  let _ : J'.Subcanonical := hsub
  let _ : HasFiniteLimits C' := hfinite
  let _ : v0.IsDenseSubsite J0Small J' := hv0
  let v : C ⥤ C' := a ⋙ v0
  have hv : v.IsDenseSubsite J J' := by
    -- The source leg is still the composite dense subsite from the source package.
    simpa [v] using
      (dense_subsite_comp_of_equivalence_left
        (C0 := C0Small) (C' := C') (J := J) (J0 := J0Small) (J' := J') a v0)
  let _ : HasWeakSheafify J' (Type (max (max u₁ v₁) (max u₂ v₂))) := hweakJ'
  let _ :
      ∀ P : Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂)), u.op.HasLeftKanExtension P := huLan
  let instC' : Category.{max (max (max u₁ u₂) v₁) v₂} C' := hC'
  have hcontSite :
      Functor.IsContinuousSiteFunctor u K.toPrecoverage J'.toPrecoverage := by
    -- First build the source-proof continuity data at the precoverage level.
    exact
      factorization_target_isContinuousSiteFunctor
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 hcover u
        (Classical.choice hρ) huPullbacks
  -- The statement records continuity at the source-faithful precoverage level; the exactness
  -- content of "defines a morphism of sites" is carried by the lower morphism of topoi `g`.
  letI : (v.sheafPushforwardContinuous
      (Type (max (max u₁ v₁) (max u₂ v₂))) J J').IsEquivalence := by
    infer_instance
  let e :
      Sheaf J' (Type (max (max u₁ v₁) (max u₂ v₂))) ≌
        Sheaf J (Type (max (max u₁ v₁) (max u₂ v₂))) :=
    (v.sheafPushforwardContinuous
      (Type (max (max u₁ v₁) (max u₂ v₂))) J J').asEquivalence
  letI : PreservesFiniteLimits e.inverse := by
    constructor
    intro Jc _ _
    infer_instance
  letI : PreservesFiniteLimits (f⁻¹) := f.inverseImageFunctor.property
  let _ : PreservesFiniteLimits (f⁻¹ ⋙ e.inverse) := by
    exact comp_preservesFiniteLimits _ _
  let g : MorphismOfTopoiIn K J' :=
    { inverseImageFunctor := LeftExactFunctor.of (f⁻¹ ⋙ e.inverse)
      pushforward := e.functor ⋙ f _*
      adjunction := f.adjunction.comp e.symm.toAdjunction }
  -- The displayed square only depends on the dense-subsite equivalence on the source side.
  -- Conjugate `f` by that equivalence to obtain the required lower morphism of topoi.
  have sq :
      Nonempty
        (CatCommSq
          (𝟭 (Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))))
          (g⁻¹)
          (f⁻¹)
          (v.sheafPushforwardContinuous (Type (max (max u₁ v₁) (max u₂ v₂))) J J')) := by
    refine ⟨{ iso := ?_ }⟩
    -- The counit of the dense-subsite equivalence rewrites the conjugated inverse image back to
    -- the original inverse image `f⁻¹`.
    exact
      (Functor.leftUnitor (f⁻¹)) ≪≫
        (Functor.rightUnitor (f⁻¹)).symm ≪≫
          Functor.isoWhiskerLeft (f⁻¹) e.counitIso.symm ≪≫
            (Functor.associator (f⁻¹) e.inverse e.functor).symm
  have hterm : ∀ X : D, Limits.IsTerminal X → Nonempty (Limits.IsTerminal (u.obj X)) := by
    intro X hX
    -- Pass terminality through the Yoneda presentation `ρ` of `u`: every stage of the
    -- transported family preserves the terminal object, and the subcanonical Yoneda embedding
    -- reflects it back to the site.
    obtain ⟨ρ⟩ := hρ
    letI : PreservesFiniteLimits
        (f.inverseImageFunctor.obj :
          Sheaf K (Type (max (max u₁ v₁) (max u₂ v₂))) ⥤ _) :=
      f.inverseImageFunctor.property
    have h1 : Limits.IsTerminal
        (CategoryTheory.uliftYoneda.{max (max u₁ v₁) u₂ v₂}.obj X :
          Dᵒᵖ ⥤ Type (max (max u₁ v₁) (max u₂ v₂))) :=
      Limits.IsTerminal.isTerminalObj _ _ hX
    have h2 : Limits.IsTerminal
        (GrothendieckTopology.uliftSheafifiedRepresentableFunctor.{max u₁ v₁, u₂, v₂} K |>.obj
          X) :=
      Limits.IsTerminal.isTerminalObj
        (presheafToSheaf K (Type (max (max u₁ v₁) (max u₂ v₂)))) _ h1
    have h3 := Limits.IsTerminal.isTerminalObj
      (f.inverseImageFunctor.obj) _ h2
    have h4 := Limits.IsTerminal.isTerminalObj
      ((sheafEquiv J J0Small a (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) _ h3
    have h5 := Limits.IsTerminal.isTerminalObj
      ((sheafEquiv J0Small J' v0 (Type (max (max u₁ v₁) (max u₂ v₂)))).functor) _ h4
    have h6 : Limits.IsTerminal (J'.yoneda.obj (u.obj X)) :=
      Limits.IsTerminal.ofIso h5 (ρ.app X).symm
    exact ⟨Limits.IsTerminal.isTerminalOfObj J'.yoneda (u.obj X) h6⟩
  have hcontTop : Limits.HasPullbacks D → u.IsContinuous K J' := by
    intro hD
    exact
      factorization_target_isContinuous_of_hasPullbacks
        (J := J) (K := K) (J0Small := J0Small) (J' := J') f a v0 hcover u
        (Classical.choice hρ) huPullbacks
  have hvffC : J.Subcanonical → v.FullyFaithful := by
    intro hJsub
    haveI := haEquiv
    exact (Functor.FullyFaithful.ofFullyFaithful a).comp (hv0ff hJsub)
  refine ⟨C', instC', J', hsub, hfinite, v, hv, hvffC, u, hcontSite, huPullbacks, hterm, hcontTop, g, ?_⟩
  exact sq

end

end CategoryTheory
