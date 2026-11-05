module

public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Monad.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.CategoryTheory.Limits.Constructions.ZeroObjects
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Topology.Sheaves.Sheafify
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Geometry.RingedSpace.SheafedSpace
public import Mathlib.Geometry.RingedSpace.Basic
public import stacks_project.Chap06.Definition_6_26_1
public import stacks_project.Chap06.Definition_6_31_2
public import stacks_project.Chap06.Extension_by_zero_by_the_initial_object
public import stacks_project.Chap06.Lemma_6_20_3
public import stacks_project.Chap06.Lemma_6_21_5
public import stacks_project.Chap06.Lemma_6_31_7
public import stacks_project.Chap06.Pushforward_pushforward_adjunction
public import stacks_project.Chap06.Restriction_and_extension_by_zero_for_module_valued_sheaves

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open TopCat
open TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

/- Domain-style sampling for Lemma 6.31.8:
- primary domain: extension by zero and restriction for sheaves of modules along the open
  immersion `j : U ↪ X` of a ringed space;
- sampled owner declarations:
  `openSubsetModulePresheafExtensionByZero`,
  `openSubsetModuleSheafExtensionByZero`,
  `moduleSheafRestrictionToOpen`,
  `moduleSheafExtensionByZeroAdjunction`;
- source/core/bridge triage:
  `source-facing`: the explicit open-immersion extension-by-zero functors on module presheaves and
  sheaves, together with the textbook unit and stalk statements;
  `core/canonical`: the restriction owner `moduleSheafRestrictionToOpen` and its chosen left
  adjoint `moduleSheafExtensionByZeroFromOpen`, packaged by
  `moduleSheafExtensionByZeroAdjunction`;
  `bridge/view`: the identification of the explicit source-facing extension-by-zero functors with
  the canonical adjoint owners, plus the resulting unit and stalk isomorphisms.

Primitive data are the open subset `U`, the ambient ringed space `X`, and the canonical module
extension/restriction functors already defined upstream. The only new public content here should be
the bridge from the explicit `j_!` construction to those owners and the source-facing stalk
consequences; one-off aliases for canonical owner expressions should be eliminated. -/

section

variable {X : RingedSpace.{u}} (U : Opens X.carrier)

public abbrev ambientModuleRingSheaf : X.carrier.Sheaf RingCat.{u} :=
  RingedSpace.ringCatSheaf X

public abbrev openSubspaceModuleRingSheaf : (extensionByZeroOpenSubsetSpace U).Sheaf RingCat.{u} :=
  (Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj ambientModuleRingSheaf

/-- Helper for Lemma 6.31.8: the source ring sheaf on the open subspace is the canonical
open-embedding pullback of the ambient ring sheaf. -/
public noncomputable abbrev openSubspaceModuleRingSheafIsoConcretePullback :
    openSubspaceModuleRingSheaf U ≅
      (Topology.IsOpenEmbedding.sheafPullback RingCat.{u} U.isOpenEmbedding).obj
        ambientModuleRingSheaf :=
  -- The abstract sheaf pullback and the concrete open-embedding pullback are identified by the
  -- standard open-embedding comparison.
  (Topology.IsOpenEmbedding.sheafPullbackIso RingCat.{u} U.isOpenEmbedding).app
    ambientModuleRingSheaf

/-- Helper for Lemma 6.31.8: the concrete open-embedding pullback of the ambient ring sheaf has
the expected underlying presheaf on opens of `U`. -/
public theorem openSubspaceModuleRingSheafConcretePullback_obj_eq :
    ((Topology.IsOpenEmbedding.sheafPullback RingCat.{u} U.isOpenEmbedding).obj
        ambientModuleRingSheaf).obj =
      U.isOpenEmbedding.functor.op ⋙ ambientModuleRingSheaf.obj := by
  -- The concrete open-embedding pullback is defined by pulling back the underlying presheaf
  -- along the functor on opens.
  rfl

/-- Helper for Lemma 6.31.8: the source ring sheaf on `U` has the same underlying presheaf of
rings as the public pullback owner along `U.inclusion'`. -/
public noncomputable abbrev openSubspaceModuleRingSheafObjIsoConcretePullback :
    (openSubspaceModuleRingSheaf U).obj ≅
      (TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf := by
  let e₁ :=
    (TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
      (openSubspaceModuleRingSheafIsoConcretePullback (U := U))
  let e₂ :
      ((Topology.IsOpenEmbedding.sheafPullback RingCat.{u} U.isOpenEmbedding).obj
          ambientModuleRingSheaf).obj ≅
        U.isOpenEmbedding.functor.op ⋙ ambientModuleRingSheaf.obj :=
    eqToIso (openSubspaceModuleRingSheafConcretePullback_obj_eq (U := U))
  -- Normalize the concrete open-embedding owner once, then pass to the public pullback owner.
  exact
    e₁ ≪≫ e₂ ≪≫
      (((U.isOpenEmbedding.isOpenMap.pullbackIso :
          TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).app
        ambientModuleRingSheaf.presheaf).symm)

/-- Helper for Lemma 6.31.8: the source-side module sheafification adjunction can be read in the
public pullback spelling of the ring presheaf on `U`. -/
public noncomputable abbrev openSubspaceModuleSourceSheafificationHomEquiv
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (𝒢 : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    (((PresheafOfModules.sheafification
        (α := (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).inv)).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶
        ((SheafOfModules.forget (openSubspaceModuleRingSheaf U)) ⋙
          PresheafOfModules.restrictScalars
            ((openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).inv)).obj
          𝒢) :=
  -- This is exactly the generic sheafification adjunction specialized to the normalized source
  -- ring-presheaf owner on the open subspace.
  (PresheafOfModules.sheafificationAdjunction
    (α := (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).inv)).homEquiv ℱ 𝒢

/-- Helper for Lemma 6.31.8: on an ambient open contained in `U`, the underlying additive
presheaf of module extension by zero is just the original presheaf on the corresponding open of
the open subspace. -/
public theorem openSubsetModulePresheafExtensionByZero_obj_eq_of_le
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf.presheaf))
    {V : (Opens X.carrier)ᵒᵖ} (hV : V.unop ≤ U) :
    (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf).obj
        V =
      ℱ.presheaf.obj (Opposite.op (openSubsetPreimageOpen U V.unop)) := by
  -- Forgetting modules turns the explicit module extension into the imported additive
  -- extension-by-initial-object owner.
  simpa [ambientModuleRingSheaf, openSubsetModulePresheafExtensionByZero] using
    (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le
      (C := AddCommGrpCat.{u}) U ℱ.presheaf hV)

/-- Helper for Lemma 6.31.8: on an ambient open not contained in `U`, the underlying additive
presheaf of module extension by zero is the initial additive group. -/
public theorem openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf.presheaf))
    {V : (Opens X.carrier)ᵒᵖ} (hV : ¬ V.unop ≤ U) :
    (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf).obj
        V =
      ⊥_ AddCommGrpCat.{u} := by
  -- Outside `U`, the underlying additive presheaf is exactly the generic initial-object
  -- extension.
  simpa [ambientModuleRingSheaf, openSubsetModulePresheafExtensionByZero] using
    (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le
      (C := AddCommGrpCat.{u}) U ℱ.presheaf hV)

/-- Helper for Lemma 6.31.8: outside `U`, the restriction maps of the underlying additive
presheaf of module extension by zero are the unique maps out of the initial object. -/
public theorem openSubsetModulePresheafExtensionByZero_map_eq_of_not_le
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf.presheaf))
    {V W : (Opens X.carrier)ᵒᵖ} (i : V ⟶ W) (hV : ¬ V.unop ≤ U) :
    (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf).map i =
      eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le (U := U) ℱ hV) ≫
        (show (⊥_ AddCommGrpCat.{u}) ⟶
            (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
              ℱ).presheaf).obj W from
          @initial.to AddCommGrpCat.{u} _ _
            ((((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
              ℱ).presheaf).obj W)) := by
  -- The outside-`U` restriction map is inherited from the additive extension-by-initial-object
  -- owner.
  simpa [ambientModuleRingSheaf, openSubsetModulePresheafExtensionByZero] using
    (openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le
      (C := AddCommGrpCat.{u}) U ℱ.presheaf i hV)

/-- Helper for Lemma 6.31.8: on opens contained in `U`, the restriction maps of the underlying
additive presheaf of module extension by zero are the original restriction maps of `ℱ`, up to the
canonical identifications of the section objects. -/
public theorem openSubsetModulePresheafExtensionByZero_map_eq_of_le
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf.presheaf))
    {V W : (Opens X.carrier)ᵒᵖ} (i : V ⟶ W) (hV : V.unop ≤ U) (hW : W.unop ≤ U) :
    (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf).map
        i =
      eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hV) ≫
        ℱ.presheaf.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
          eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hW).symm := by
  -- Inside `U`, the module-valued extension inherits the same additive restriction formula as the
  -- imported extension-by-initial-object owner.
  simpa [ambientModuleRingSheaf, openSubsetModulePresheafExtensionByZero] using
    (openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le
      (C := AddCommGrpCat.{u}) U ℱ.presheaf i hV hW)

/-- Helper for Lemma 6.31.8: the image of an open of the open subspace still lies inside `U`. -/
public theorem openSubsetImageOpen_le
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (U.isOpenEmbedding.functor.obj V) ≤ U := by
  -- Unfold the image-open description and check that every point comes from the subtype `U`.
  intro x hx
  change x ∈ (((U.isOpenEmbedding.functor.obj V : Opens X.carrier) : Set X.carrier)) at hx
  change x ∈ (U : Set X.carrier)
  simp only [SetLike.mem_coe] at hx ⊢
  rcases hx with ⟨y, hy, rfl⟩
  exact y.2

/-- Helper for Lemma 6.31.8: pulling back the image open of an open in the open subspace
recovers the original open. -/
public theorem openSubsetPreimageImageOpen_eq
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V) = V := by
  -- Membership in the pulled-back image open is exactly membership in the original open.
  ext x
  simp [openSubsetPreimageOpen, Topology.IsOpenEmbedding.functor, IsOpenMap.functor]

/-- Helper for Lemma 6.31.8: if an ambient open already lies in `U`, then taking its pullback to
the open subspace and then its image returns the original ambient open. -/
public theorem openSubsetImagePreimageOpen_eq_of_le
    {W : Opens X.carrier} (hW : W ≤ U) :
    U.isOpenEmbedding.functor.obj (openSubsetPreimageOpen U W) = W := by
  -- The forward inclusion is tautological; the reverse inclusion uses the given containment
  -- `W ≤ U` to lift points of `W` back to the open subspace.
  ext x
  constructor
  · intro hx
    change x ∈ (((U.isOpenEmbedding.functor.obj (openSubsetPreimageOpen U W) : Opens X.carrier) :
      Set X.carrier)) at hx
    simp only [SetLike.mem_coe] at hx
    rcases hx with ⟨y, hy, rfl⟩
    simpa using hy
  · intro hx
    change x ∈ (((U.isOpenEmbedding.functor.obj (openSubsetPreimageOpen U W) : Opens X.carrier) :
      Set X.carrier))
    refine ⟨⟨x, hW hx⟩, ?_, rfl⟩
    simpa [openSubsetPreimageOpen]

/-- Helper for Lemma 6.31.8: containment of the image open in an ambient open is equivalent to
containment of the original open in the corresponding preimage open. -/
public theorem openSubsetImageOpen_le_iff
    {V : Opens (extensionByZeroOpenSubsetSpace U)} {W : Opens X.carrier} :
    U.isOpenEmbedding.functor.obj V ≤ W ↔ V ≤ openSubsetPreimageOpen U W := by
  constructor
  · intro h x hx
    -- View `x` as a point of the ambient image open and apply the assumed containment there.
    change x.1 ∈ (W : Set X.carrier)
    have hxImage : x.1 ∈
        (((U.isOpenEmbedding.functor.obj V : Opens X.carrier) : Set X.carrier)) := by
      exact ⟨x, hx, rfl⟩
    exact h hxImage
  · intro h x hx
    -- Any point of the image open comes from a point of `V`, which the preimage containment sends
    -- into `W`.
    rcases hx with ⟨y, hy, rfl⟩
    have hyW : y ∈ openSubsetPreimageOpen U W := h hy
    simpa [openSubsetPreimageOpen] using hyW

/-- Helper for Lemma 6.31.8: the unit morphism of the opens adjunction is an isomorphism on every
open of the open subspace. -/
public theorem openSubsetAdjunction_unit_app_isIso
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    IsIso (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V) := by
  -- In the thin category of opens, the unit is the identity after rewriting the codomain with
  -- `preimage (image V) = V`.
  have hEq : V = openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V) := by
    simpa using (openSubsetPreimageImageOpen_eq (U := U) V).symm
  have hUnit :
      U.isOpenEmbedding.isOpenMap.adjunction.unit.app V = eqToHom hEq := by
    apply Subsingleton.elim
  rw [hUnit]
  simpa using (show IsIso (eqToIso hEq).hom from inferInstance)

/-- Helper for Lemma 6.31.8: the counit morphism of the opens adjunction is an isomorphism on an
ambient open already contained in `U`. -/
public theorem openSubsetAdjunction_counit_app_isIso_of_le
    {W : Opens X.carrier} (hW : W ≤ U) :
    IsIso (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W) := by
  -- On opens inside `U`, the counit is the identity after rewriting `image (preimage W) = W`.
  have hEq : U.isOpenEmbedding.functor.obj (openSubsetPreimageOpen U W) = W :=
    openSubsetImagePreimageOpen_eq_of_le (U := U) hW
  have hCounit :
      U.isOpenEmbedding.isOpenMap.adjunction.counit.app W = eqToHom hEq := by
    apply Subsingleton.elim
  rw [hCounit]
  simpa using (show IsIso (eqToIso hEq).hom from inferInstance)

/-- Helper for Lemma 6.31.8: any additive presheaf sends the opens-adjunction unit on an open of
the open subspace to an isomorphism on sections. -/
public theorem openSubsetPresheaf_map_unit_app_isIso
    (F : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    IsIso (F.map (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op) := by
  -- Presheaf restriction maps preserve the isomorphism of the underlying open inclusion.
  letI := openSubsetAdjunction_unit_app_isIso (U := U) V
  infer_instance

/-- Helper for Lemma 6.31.8: any additive presheaf sends the opens-adjunction counit on an
ambient open contained in `U` to an isomorphism on sections. -/
public theorem openSubsetPresheaf_map_counit_app_isIso_of_le
    (F : X.carrier.Presheaf AddCommGrpCat.{u})
    {W : Opens X.carrier} (hW : W ≤ U) :
    IsIso (F.map (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op) := by
  -- Again, functoriality sends the thin-category isomorphism of opens to a section isomorphism.
  letI := openSubsetAdjunction_counit_app_isIso_of_le (U := U) hW
  infer_instance

/-- Helper for Lemma 6.31.8: on an open of the open subspace, the raw additive pullback along the
open inclusion is identified with sections on the corresponding image open of `X`. -/
public noncomputable abbrev openSubsetAdditivePullback_objIso
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    ((TopCat.Presheaf.pullback AddCommGrpCat.{u} U.inclusion').obj 𝒢.presheaf).obj
        (Opposite.op V) ≅
      𝒢.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)) := by
  -- The generic open-map pullback comparison already computes the raw additive pullback on image
  -- opens, so we record that component explicitly for later transport to module-valued data.
  simpa using (U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒢.presheaf).app (Opposite.op V)

/-- Helper for Lemma 6.31.8: under the image-open identification, the restriction maps of the raw
additive pullback are the original restriction maps of `𝒢.presheaf`. -/
public theorem openSubsetAdditivePullback_map_eq
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    ((TopCat.Presheaf.pullback AddCommGrpCat.{u} U.inclusion').obj 𝒢.presheaf).map i =
      (openSubsetAdditivePullback_objIso (U := U) 𝒢 V.unop).hom ≫
        𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op ≫
          (openSubsetAdditivePullback_objIso (U := U) 𝒢 W.unop).inv := by
  -- Rewrite the raw pullback map through the open-map pullback comparison, then cancel the target
  -- comparison isomorphism to expose the expected restriction map on the image opens.
  let e := U.isOpenEmbedding.isOpenMap.pullbackObjIso 𝒢.presheaf
  rw [← cancel_mono (e.hom.app W)]
  simpa [e, openSubsetAdditivePullback_objIso, Category.assoc] using e.hom.naturality i

/-- Helper for Lemma 6.31.8: on an open of the open subspace, the public pullback of the ambient
ring presheaf is identified with the ambient ring presheaf on the corresponding image open. -/
public noncomputable abbrev openSubsetRingPullbackImageObjIso
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf).obj
        (Opposite.op V) ≅
      ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)) := by
  -- The public ring-valued pullback owner is already computed on image opens by the generic
  -- open-map pullback comparison.
  simpa using (U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).app
    (Opposite.op V)

/-- Helper for Lemma 6.31.8: under the image-open identification, the restriction maps of the
public pullback of the ambient ring presheaf are the original restriction maps on the image opens.
-/
public theorem openSubsetRingPullbackMap_eq
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf).map i =
      (openSubsetRingPullbackImageObjIso (U := U) V.unop).hom ≫
        ambientModuleRingSheaf.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op ≫
          (openSubsetRingPullbackImageObjIso (U := U) W.unop).inv := by
  let e := U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf
  -- This is the ring-valued analogue of the additive image-open formula above.
  rw [← cancel_mono (e.hom.app W)]
  simpa [e, openSubsetRingPullbackImageObjIso, Category.assoc] using e.hom.naturality i

/-- Helper for Lemma 6.31.8: on an ambient open, the open-map pullback comparison sends the
pullback/pushforward adjunction unit of the ambient ring presheaf to restriction along the
opens-adjunction counit. This is the ring-level core of the open-immersion triangle identity. -/
public theorem openSubsetRing_pullbackObjIso_hom_unit_app
    (W : Opens X.carrier)
    (s : ambientModuleRingSheaf.presheaf.obj (Opposite.op W)) :
    ((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
        (Opposite.op ((Opens.map U.inclusion').obj W)))
      (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf).app (Opposite.op W) s) =
      (ambientModuleRingSheaf.presheaf.map
        (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op) s := by
  let W' : Opens ((Opens.toTopCat X.carrier).obj U) := (Opens.map U.inclusion').obj W
  let Wimage : Opens X.carrier := ⟨_, U.isOpenEmbedding.isOpenMap _ W'.2⟩
  let x : CostructuredArrow (Opens.map U.inclusion').op (Opposite.op W') :=
    CostructuredArrow.mk (@homOfLE _ _ _ ((Opens.map U.inclusion').obj Wimage)
      (Set.image_preimage.le_u_l _)).op
  have hx : Limits.IsTerminal x := by
    -- The image-open object is terminal in the costructured-arrow fiber over `W ∩ U`.
    refine
      { lift := fun s ↦ by
          fapply CostructuredArrow.homMk
          · change Opposite.op (Opposite.unop s.pt.left) ⟶ Opposite.op Wimage
            refine (homOfLE ?_).op
            apply (Set.image_mono s.pt.hom.unop.le).trans
            exact Set.image_preimage.l_u_le (SetLike.coe s.pt.left.unop)
          · simp [eq_iff_true_of_subsingleton] }
  -- Evaluate the pointwise left-Kan cocone at the identity object, then transport to the terminal
  -- cocone that defines `pullbackObjObjOfImageOpen`.
  dsimp [W', Wimage, x, IsOpenMap.pullbackObjIso,
    TopCat.Presheaf.pullbackObjObjOfImageOpen]
  have h := Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
    ((Opens.map U.inclusion').op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      ambientModuleRingSheaf.presheaf
      (Opposite.op ((Opens.map U.inclusion').obj W)))
    (Limits.colimitOfDiagramTerminal hx
      (CostructuredArrow.proj (Opens.map U.inclusion').op
        (Opposite.op ((Opens.map U.inclusion').obj W)) ⋙ ambientModuleRingSheaf.presheaf))
    (CostructuredArrow.mk (𝟙 (Opposite.op ((Opens.map U.inclusion').obj W))))
  rw [Limits.coconeOfDiagramTerminal_ι_app] at h
  simpa using congrArg (fun f ↦ RingCat.Hom.hom f s) h

/-- Helper for Lemma 6.31.8: naturality of the open-map pullback comparison moves restriction along
the opens-adjunction unit from the pullback side to the explicit open-embedding side. -/
public theorem openSubsetRing_pullbackObjIso_hom_unit_move
    (V : Opens (extensionByZeroOpenSubsetSpace U))
    (s : (U.isOpenEmbedding.functor.op ⋙ ambientModuleRingSheaf.presheaf).obj (Opposite.op V)) :
    ((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
        (Opposite.op V))
      ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
            ambientModuleRingSheaf.presheaf).app
            (Opposite.op (U.isOpenEmbedding.functor.obj V)) s)) =
      ((U.isOpenEmbedding.functor.op ⋙ ambientModuleRingSheaf.presheaf).map
          (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
        (((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
            (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))))
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf).app
              (Opposite.op (U.isOpenEmbedding.functor.obj V)) s)) := by
  have hnat :=
    (U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.naturality
      (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op
  have happ := congrArg
    (fun k ↦ k (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
        ambientModuleRingSheaf.presheaf).app
        (Opposite.op (U.isOpenEmbedding.functor.obj V)) s)) hnat
  simpa [Function.comp_apply] using happ

/-- Helper for Lemma 6.31.8: the open-immersion presheaf triangle for the ambient ring presheaf —
restriction of the adjunction unit along the opens-adjunction unit equals the inverse open-map
pullback comparison on the original open of `U`. -/
public theorem openSubsetRing_pullback_unit_triangle
    (V : Opens (extensionByZeroOpenSubsetSpace U))
    (s : (U.isOpenEmbedding.functor.op ⋙ ambientModuleRingSheaf.presheaf).obj (Opposite.op V)) :
    (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf).map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
      (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf).app
          (Opposite.op (U.isOpenEmbedding.functor.obj V)) s) =
      (((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).inv.app
          (Opposite.op V)) s) := by
  let pIso := U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf
  have hhom :
      ((pIso.hom.app (Opposite.op V))
          ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
              ambientModuleRingSheaf.presheaf).map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
            (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
                ambientModuleRingSheaf.presheaf).app
                (Opposite.op (U.isOpenEmbedding.functor.obj V)) s))) = s := by
    rw [openSubsetRing_pullbackObjIso_hom_unit_move (U := U) V s]
    -- Replace the inner comparison with the explicit counit formula on the image open.
    have hcounit :
        ((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
            (Opposite.op ((Opens.map U.inclusion').obj (U.isOpenEmbedding.functor.obj V))))
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf).app
              (Opposite.op (U.isOpenEmbedding.functor.obj V)) s) =
          (ambientModuleRingSheaf.presheaf.map
            (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
              (U.isOpenEmbedding.functor.obj V)).op) s :=
      openSubsetRing_pullbackObjIso_hom_unit_app (U := U) (U.isOpenEmbedding.functor.obj V) s
    rw [hcounit]
    -- The open-subset adjunction triangle identifies the resulting composite restriction with the
    -- identity on the section over `V`.
    change
      ((ambientModuleRingSheaf.presheaf.map
          (U.isOpenEmbedding.isOpenMap.adjunction.counit.app
            (U.isOpenEmbedding.functor.obj V)).op) ≫
        (ambientModuleRingSheaf.presheaf.map
          ((U.isOpenEmbedding.functor.map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V)).op))) s = s
    rw [← Functor.map_comp]
    have htriangle := U.isOpenEmbedding.isOpenMap.adjunction.left_triangle_components V
    simpa [CategoryTheory.comp_apply] using
      congrArg (fun k ↦ (ambientModuleRingSheaf.presheaf.map k.op) s) htriangle
  -- Cancel the forward comparison using the `pullbackObjIso` inverse at `V`.
  have hinv := congrArg (fun t ↦ (pIso.inv.app (Opposite.op V)) t) hhom
  have hleft :
      (pIso.inv.app (Opposite.op V))
        ((pIso.hom.app (Opposite.op V))
          ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
              ambientModuleRingSheaf.presheaf).map
              (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
            (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
                ambientModuleRingSheaf.presheaf).app
                (Opposite.op (U.isOpenEmbedding.functor.obj V)) s))) =
        (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
            ambientModuleRingSheaf.presheaf).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf).app
              (Opposite.op (U.isOpenEmbedding.functor.obj V)) s) := by
    simpa using congrArg
      (fun k ↦ k
        ((((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
            ambientModuleRingSheaf.presheaf).map
            (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf).app
              (Opposite.op (U.isOpenEmbedding.functor.obj V)) s)))
      (Iso.hom_inv_id_app pIso (Opposite.op V))
  rw [← hleft]
  exact hinv

/-- Helper for Lemma 6.31.8: the ring-level cancellation `α ∘ ringIso = id` (up to the canonical
`preimage (image V) = V` transport). Concretely, applying the adjunction unit on the image open to
the image-open comparison of a section, then restricting back along the opens-adjunction unit,
recovers the original section. This is what makes the extension/restriction unit `O|_U`-linear. -/
public theorem openSubsetRingPullbackImage_unit_cancel
    (V : Opens (extensionByZeroOpenSubsetSpace U))
    (r : ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
            ambientModuleRingSheaf.presheaf).obj (Opposite.op V)) :
    (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf).map
        (U.isOpenEmbedding.isOpenMap.adjunction.unit.app V).op)
      (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf).app
          (Opposite.op (U.isOpenEmbedding.functor.obj V))
        ((openSubsetRingPullbackImageObjIso (U := U) V).hom r)) = r := by
  rw [openSubsetRing_pullback_unit_triangle (U := U) V
    ((openSubsetRingPullbackImageObjIso (U := U) V).hom r)]
  -- The remaining `pullbackObjIso.inv ∘ ringIso.hom` is the hom-then-inverse of the same image-open
  -- comparison iso, hence the identity on the section.
  exact Iso.hom_inv_id_apply (openSubsetRingPullbackImageObjIso (U := U) V) r


/-- Helper for Lemma 6.31.8: cancel a pair of opposite `eqToHom` transports in the middle of a
composite. -/
public theorem comp_eqToHom_symm_eqToHom_assoc
    {C : Type*} [Category C] {A B X Y : C} (h : A = B)
    (f : X ⟶ B) (g : B ⟶ Y) :
    ((f ≫ eqToHom h.symm) ≫ eqToHom h) ≫ g = f ≫ g := by
  cases h
  simp

/-- Helper for Lemma 6.31.8: right-associated variant of
`comp_eqToHom_symm_eqToHom_assoc`. -/
public theorem comp_eqToHom_symm_eqToHom_assoc_right
    {C : Type*} [Category C] {A B X Y : C} (h : A = B)
    (f : X ⟶ B) (g : B ⟶ Y) :
    (f ≫ eqToHom h.symm) ≫ (eqToHom h ≫ g) = f ≫ g := by
  cases h
  simp [Category.assoc]

/-- Helper for Lemma 6.31.8: cancel a middle pair of opposite `eqToHom` transports
with two trailing morphisms. -/
public theorem comp_eqToHom_symm_eqToHom_assoc_right₂
    {C : Type*} [Category C] {A B X Y Z : C} (h : A = B)
    (f : X ⟶ B) (g : B ⟶ Y) (k : Y ⟶ Z) :
    ((f ≫ eqToHom h.symm) ≫ eqToHom h ≫ g) ≫ k = (f ≫ g) ≫ k := by
  cases h
  simp [Category.assoc]

/-- Helper for Lemma 6.31.8: printed-shape variant for canceling a middle pair of
opposite `eqToHom` transports. -/
public theorem comp_eqToHom_symm_eqToHom_assoc_printed
    {C : Type*} [Category C] {A B X Y Z : C} (h : A = B)
    (f : X ⟶ B) (g : B ⟶ Y) (k : Y ⟶ Z) :
    (f ≫ eqToHom h.symm) ≫ eqToHom h ≫ g ≫ k = f ≫ g ≫ k := by
  cases h
  simp [Category.assoc]

/-- Helper for Lemma 6.31.8: nested printed-shape variant for canceling a middle
pair of opposite `eqToHom` transports. -/
public theorem comp_eqToHom_symm_eqToHom_assoc_nested
    {C : Type*} [Category C] {A B X T Y Z : C} (h : A = B)
    (a : X ⟶ T) (f : T ⟶ B) (g : B ⟶ Y) (k : Y ⟶ Z) :
    (a ≫ (f ≫ eqToHom h.symm)) ≫ eqToHom h ≫ g ≫ k = a ≫ f ≫ g ≫ k := by
  cases h
  simp [Category.assoc]

/-- Helper for Lemma 6.31.8: forgetting the module pushforward along the open-inclusion unit is
the same as the additive presheaf pushforward along `U.inclusion'`. -/
public noncomputable abbrev openSubsetModulePushforwardToPresheafIso :
    PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf) ⋙
      PresheafOfModules.toPresheaf ambientModuleRingSheaf.presheaf ≅
    PresheafOfModules.toPresheaf
        ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf) ⋙
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{u}).obj (Opens.map U.inclusion').op := by
  -- This is the generic `pushforwardCompToPresheaf` comparison specialized to the open
  -- inclusion.
  exact
    (PresheafOfModules.pushforwardCompToPresheaf
      (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
        ambientModuleRingSheaf.presheaf)))

/-- Helper for Lemma 6.31.8: on an ambient open, forgetting the concrete module pushforward owner
identifies its sections with sections of the source presheaf on the corresponding preimage open in
`U`. -/
public noncomputable abbrev openSubsetModulePushforwardPreimageSectionIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (W : Opens X.carrier) :
    (((PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf)).obj ℱ).presheaf).obj
        (Opposite.op W) ≅
      ℱ.presheaf.obj (Opposite.op (openSubsetPreimageOpen U W)) := by
  -- The forgetful comparison already lands in the additive presheaf obtained by precomposing with
  -- `Opens.map U.inclusion'`, whose value on `W` is exactly the preimage open of `W` in `U`.
  simpa [openSubsetPreimageOpen] using
    (((openSubsetModulePushforwardToPresheafIso (U := U)).app ℱ).app (Opposite.op W))

/-- Helper for Lemma 6.31.8: on an ambient open, the concrete module pushforward owner is
literally restriction of scalars of the source section module on the corresponding preimage open.
-/
public theorem openSubsetModulePushforwardPreimageObj_eq
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (W : Opens X.carrier) :
    (((PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf)).obj ℱ).obj
        (Opposite.op W)) =
      ((ModuleCat.restrictScalars
        (RingCat.Hom.hom
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
            ambientModuleRingSheaf.presheaf).app (Opposite.op W)))).obj
        (ℱ.obj (Opposite.op (openSubsetPreimageOpen U W)))) := by
  -- The module-valued pushforward owner already computes sections by restricting scalars along
  -- the adjunction unit on each open.
  simpa [openSubsetPreimageOpen] using
    (PresheafOfModules.pushforward_obj_obj
      (φ := ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
        ambientModuleRingSheaf.presheaf))
      ℱ (Opposite.op W))

/-- Helper for Lemma 6.31.8: the concrete module pushforward owner on an ambient open is packaged
as the corresponding restriction-of-scalars module isomorphism. -/
public noncomputable abbrev openSubsetModulePushforwardPreimageObjIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (W : Opens X.carrier) :
    (((PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf)).obj ℱ).obj
        (Opposite.op W)) ≅
      ((ModuleCat.restrictScalars
        (RingCat.Hom.hom
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
            ambientModuleRingSheaf.presheaf).app (Opposite.op W)))).obj
        (ℱ.obj (Opposite.op (openSubsetPreimageOpen U W)))) :=
  -- Repackage the object formula as an isomorphism so later section comparisons can compose at
  -- the `Iso` level instead of reopening `eqToIso` transports.
  eqToIso (openSubsetModulePushforwardPreimageObj_eq (U := U) ℱ W)

/-- Helper for Lemma 6.31.8: under the preimage-open identification, the restriction maps of the
forgotten concrete module pushforward are the original restriction maps of `ℱ.presheaf`. -/
public theorem openSubsetModulePushforwardPreimageMap_eq
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    {V W : (Opens X.carrier)ᵒᵖ} (i : V ⟶ W) :
    (((PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf)).obj ℱ).presheaf).map i =
      (openSubsetModulePushforwardPreimageSectionIso (U := U) ℱ V.unop).hom ≫
        ℱ.presheaf.map ((Opens.map U.inclusion').map i.unop).op ≫
          (openSubsetModulePushforwardPreimageSectionIso (U := U) ℱ W.unop).inv := by
  let e := (openSubsetModulePushforwardToPresheafIso (U := U)).app ℱ
  -- Naturality of the forgetful comparison is already the desired restriction formula, once the
  -- target functor is rewritten as evaluation on preimage opens.
  simpa [openSubsetModulePushforwardPreimageSectionIso, openSubsetPreimageOpen, Category.assoc] using
    e.hom.naturality i

/-- Helper for Lemma 6.31.8: the concrete restriction owner on module presheaves over `U`,
obtained by transporting the ambient presheaf along the open-embedding pullback comparison. -/
public noncomputable abbrev openSubsetModuleConcreteRestriction :
    PresheafOfModules (RingedSpace.ringCatSheaf X).presheaf ⥤
      PresheafOfModules
        ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
          (RingedSpace.ringCatSheaf X).presheaf) :=
  -- Route correction: keep the restriction owner concrete by using the open-embedding pullback
  -- comparison, so later arguments can work on image opens of `U` instead of reopening the opaque
  -- `PresheafOfModules.pullback` owner.
  PresheafOfModules.pushforward
    (((U.isOpenEmbedding.isOpenMap.pullbackIso :
        TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
      ambientModuleRingSheaf.presheaf))

/-- Helper for Lemma 6.31.8: on an open of the open subspace, the underlying additive presheaf of
the concrete restriction owner is just the ambient presheaf evaluated on the corresponding image
open of `X`. -/
public noncomputable abbrev openSubsetModuleConcreteRestrictionToPresheafIso
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).presheaf).obj
        (Opposite.op V) ≅
      𝒢.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)) := by
  -- Forgetting the concrete restriction owner gives literal precomposition with the
  -- open-embedding functor on opens.
  simpa [openSubsetModuleConcreteRestriction] using
    (((PresheafOfModules.pushforwardCompToPresheaf
      (((U.isOpenEmbedding.isOpenMap.pullbackIso :
          TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
        ambientModuleRingSheaf.presheaf))).app 𝒢).app (Opposite.op V))

/-- Helper for Lemma 6.31.8: on each open of the open subspace, the concrete restriction owner is
literally restriction of scalars of the ambient section module on the corresponding image open.
-/
public theorem openSubsetModuleConcreteRestriction_obj_eq
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).obj (Opposite.op V)) =
      ((ModuleCat.restrictScalars
          (RingCat.Hom.hom
            (((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
              (Opposite.op V))))).obj
        (𝒢.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)))) := by
  -- The concrete restriction owner is built by module pushforward along the open-embedding
  -- pullback comparison, so its object formula is the literal restriction-of-scalars one.
  simpa [openSubsetModuleConcreteRestriction] using
    (PresheafOfModules.pushforward_obj_obj
      (φ := (((U.isOpenEmbedding.isOpenMap.pullbackIso :
          TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
        ambientModuleRingSheaf.presheaf)))
      𝒢 (Opposite.op V))

/-- Helper for Lemma 6.31.8: the concrete restriction owner on an open of `U` is packaged as the
corresponding restriction-of-scalars module isomorphism on the image open. -/
public noncomputable abbrev openSubsetModuleConcreteRestrictionImageObjIso
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).obj (Opposite.op V)) ≅
      ((ModuleCat.restrictScalars
          (RingCat.Hom.hom
            (((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
              (Opposite.op V))))).obj
        (𝒢.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)))) :=
  -- Repackage the object formula as an isomorphism so the later direct Hom-equivalence can reuse
  -- the concrete owner without inserting fresh `eqToIso` casts at every component.
  eqToIso (openSubsetModuleConcreteRestriction_obj_eq (U := U) 𝒢 V)

/-- Helper for Lemma 6.31.8: under the image-open identification, the restriction maps of the
concrete restriction owner are the original restriction maps of the ambient module presheaf. -/
public theorem openSubsetModuleConcreteRestrictionMap_eq
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).presheaf).map i =
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
        𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op ≫
          (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 W.unop).inv := by
  let e := (PresheafOfModules.pushforwardCompToPresheaf
    (((U.isOpenEmbedding.isOpenMap.pullbackIso :
        TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
      ambientModuleRingSheaf.presheaf))).app 𝒢
  -- Naturality of the forgetful comparison already gives the image-open restriction formula.
  simpa [openSubsetModuleConcreteRestriction, openSubsetModuleConcreteRestrictionToPresheafIso,
    Category.assoc] using e.hom.naturality i

/-- Helper for Lemma 6.31.8: the concrete restriction owner is the right-adjoint side of the
generic module pullback/pushforward adjunction attached to the open-embedding pullback
comparison. -/
public noncomputable abbrev openSubsetModuleConcreteRestrictionPullbackAdjunction :
    PresheafOfModules.pullback
        (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf)) ⊣
      openSubsetModuleConcreteRestriction (U := U) := by
  -- This is the generic module pullback/pushforward adjunction specialized to the concrete
  -- open-embedding pullback comparison used to define `openSubsetModuleConcreteRestriction`.
  simpa [openSubsetModuleConcreteRestriction] using
    (PresheafOfModules.pullbackPushforwardAdjunction
      (((U.isOpenEmbedding.isOpenMap.pullbackIso :
          TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
        ambientModuleRingSheaf.presheaf)))

/-- Helper for Lemma 6.31.8: on an image open of `X`, the forgotten concrete module pushforward
owner recovers the original presheaf section object on the corresponding open of `U`. -/
public noncomputable abbrev openSubsetModulePushforwardImageSectionIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (((PresheafOfModules.pushforward
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf)).obj ℱ).presheaf).obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V)) ≅
      ℱ.presheaf.obj (Opposite.op V) := by
  -- Specialize the preimage-open formula to an image open and rewrite `preimage (image V) = V`.
  simpa [openSubsetPreimageImageOpen_eq (U := U) V] using
    (openSubsetModulePushforwardPreimageSectionIso (U := U) ℱ
      (U.isOpenEmbedding.functor.obj V))

/-- Helper for Lemma 6.31.8: after forgetting the module structure, the concrete restriction owner
is exactly the additive pullback owner on opens of `U`. -/
public noncomputable abbrev openSubsetModuleConcreteRestrictionIsoAdditivePullback
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf) :
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).presheaf) ≅
      ((TopCat.Presheaf.pullback AddCommGrpCat.{u} U.inclusion').obj 𝒢.presheaf) := by
  refine NatIso.ofComponents
    (fun V =>
      -- Normalize both owners to the same ambient section object on the image open.
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop) ≪≫
        (openSubsetAdditivePullback_objIso (U := U) 𝒢 V.unop).symm)
    (fun {V W} i => ?_)
  -- Rewrite both owners to the same ambient restriction map on image opens.
  calc
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).presheaf).map i ≫
        ((openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 W.unop) ≪≫
          (openSubsetAdditivePullback_objIso (U := U) 𝒢 W.unop).symm).hom
      =
        (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
          𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op ≫
            (openSubsetAdditivePullback_objIso (U := U) 𝒢 W.unop).inv := by
              rw [openSubsetModuleConcreteRestrictionMap_eq (U := U) 𝒢 i]
              change
                (((openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
                      𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op) ≫
                    (openSubsetModuleConcreteRestrictionToPresheafIso
                      (U := U) 𝒢 W.unop).inv ≫
                  (openSubsetModuleConcreteRestrictionToPresheafIso
                    (U := U) 𝒢 W.unop).hom ≫
                (openSubsetAdditivePullback_objIso (U := U) 𝒢 W.unop).inv) =
                  (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
                    𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op ≫
                      (openSubsetAdditivePullback_objIso (U := U) 𝒢 W.unop).inv
              rw [CategoryTheory.Iso.inv_hom_id_assoc]
              simp [Category.assoc]
    _ =
        ((openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop) ≪≫
          (openSubsetAdditivePullback_objIso (U := U) 𝒢 V.unop).symm).hom ≫
            ((TopCat.Presheaf.pullback AddCommGrpCat.{u} U.inclusion').obj 𝒢.presheaf).map i := by
              rw [openSubsetAdditivePullback_map_eq (U := U) 𝒢 i]
              simp [Category.assoc]

/-- Helper for Lemma 6.31.8: after evaluating the concrete restriction owner on image opens,
its section comparison is natural with respect to the original ambient restriction maps. -/
public theorem openSubsetModuleConcreteRestrictionToPresheafIso_hom_naturality
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf)
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    (((openSubsetModuleConcreteRestriction (U := U)).obj 𝒢).presheaf).map i ≫
        (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 W.unop).hom =
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
        𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op := by
  -- This is the image-open restriction formula with the terminal comparison isomorphism canceled.
  rw [openSubsetModuleConcreteRestrictionMap_eq (U := U) 𝒢 i]
  change
    (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
        𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op ≫
          (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 W.unop).inv ≫
            (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 W.unop).hom =
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V.unop).hom ≫
        𝒢.presheaf.map (U.isOpenEmbedding.functor.map i.unop).op
  rw [← Category.assoc, Iso.inv_hom_id, Category.comp_id]


/-- Helper for Lemma 6.31.8: the concrete restriction section comparison is natural in the
ambient module presheaf argument. -/
public theorem openSubsetModuleConcreteRestrictionToPresheafIso_hom_naturality_module
    {𝒢 ℋ : PresheafOfModules ambientModuleRingSheaf.presheaf} (η : 𝒢 ⟶ ℋ)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    ((PresheafOfModules.toPresheaf _).map
          ((openSubsetModuleConcreteRestriction (U := U)).map η)).app (Opposite.op V) ≫
        (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) ℋ V).hom =
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V).hom ≫
        ((PresheafOfModules.toPresheaf _).map η).app
          (Opposite.op (U.isOpenEmbedding.functor.obj V)) := by
  let e := (PresheafOfModules.pushforwardCompToPresheaf
    (((U.isOpenEmbedding.isOpenMap.pullbackIso :
        TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
      ambientModuleRingSheaf.presheaf))).hom.naturality η
  simpa [openSubsetModuleConcreteRestriction, openSubsetModuleConcreteRestrictionToPresheafIso,
    Category.assoc] using congrArg (fun α => α.app (Opposite.op V)) e

/-- Helper for Lemma 6.31.8: inverse form of naturality of the concrete restriction section
comparison in the ambient module presheaf argument. -/
public theorem openSubsetModuleConcreteRestrictionToPresheafIso_inv_naturality_module
    {𝒢 ℋ : PresheafOfModules ambientModuleRingSheaf.presheaf} (η : 𝒢 ⟶ ℋ)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V).inv ≫
        ((PresheafOfModules.toPresheaf _).map
          ((openSubsetModuleConcreteRestriction (U := U)).map η)).app (Opposite.op V) =
      ((PresheafOfModules.toPresheaf _).map η).app
          (Opposite.op (U.isOpenEmbedding.functor.obj V)) ≫
        (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) ℋ V).inv := by
  rw [Iso.inv_comp_eq]
  let cG := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) 𝒢 V
  let cH := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) ℋ V
  let C := openSubsetModuleConcreteRestriction (U := U)
  let ηV := ((PresheafOfModules.toPresheaf _).map η).app
    (Opposite.op (U.isOpenEmbedding.functor.obj V))
  have hHom :=
    openSubsetModuleConcreteRestrictionToPresheafIso_hom_naturality_module (U := U) η V
  change ((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) =
    (cG.hom ≫ ηV) ≫ cH.inv
  rw [← hHom]
  let e := (PresheafOfModules.pushforwardCompToPresheaf
    (((U.isOpenEmbedding.isOpenMap.pullbackIso :
        TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
      ambientModuleRingSheaf.presheaf))).app ℋ
  change ((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) =
    (((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) ≫
      e.hom.app (Opposite.op V)) ≫ e.inv.app (Opposite.op V)
  have hright :
      (((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) ≫
          e.hom.app (Opposite.op V)) ≫ e.inv.app (Opposite.op V) =
        ((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) := by
    have hnat := congrArg
      (fun α => ((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) ≫
        α.app (Opposite.op V)) e.hom_inv_id
    change ((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) ≫
        ((e.hom ≫ e.inv).app (Opposite.op V)) =
      ((PresheafOfModules.toPresheaf _).map (C.map η)).app (Opposite.op V) ≫
        𝟙 _ at hnat
    rw [NatTrans.comp_app] at hnat
    simpa [Category.assoc] using hnat
  exact hright.symm

/-- Helper for Lemma 6.31.8: the concrete-restriction comparison cancels after replacing
`preimage (image V)` by `V`. -/
public theorem openSubsetModuleConcreteRestrictionToPresheafIso_preimageImage_cancel
    (M : PresheafOfModules ambientModuleRingSheaf.presheaf)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    eqToHom (by
        simpa [openSubsetPreimageImageOpen_eq (U := U) V] :
          ((openSubsetModuleConcreteRestriction (U := U)).obj M).presheaf.obj
              (Opposite.op V) =
            ((openSubsetModuleConcreteRestriction (U := U)).obj M).presheaf.obj
              (Opposite.op (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V)))) ≫
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M
          (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V))).hom ≫
        M.presheaf.map (eqToHom (congrArg Opposite.op
          (openSubsetImagePreimageOpen_eq_of_le (U := U)
            (openSubsetImageOpen_le (U := U) V)))) ≫
          (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M V).inv =
    𝟙 _ := by
  let C := openSubsetModuleConcreteRestriction (U := U)
  let V' := openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V)
  let i : (Opposite.op V' : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) ⟶
      Opposite.op V :=
    eqToHom (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) V))
  have himage :
      (U.isOpenEmbedding.functor.map i.unop).op =
        eqToHom (congrArg Opposite.op
          (openSubsetImagePreimageOpen_eq_of_le (U := U)
            (openSubsetImageOpen_le (U := U) V))) := by
    apply Subsingleton.elim
  have hmap := openSubsetModuleConcreteRestrictionMap_eq (U := U) M i
  rw [himage] at hmap
  have hi :
      ((C.obj M).presheaf).map i =
        eqToHom (by
          simpa [C, V', openSubsetPreimageImageOpen_eq (U := U) V] :
            ((C.obj M).presheaf.obj (Opposite.op V')) =
              ((C.obj M).presheaf.obj (Opposite.op V))) := by
    dsimp [i]
    rw [CategoryTheory.eqToHom_map]
  change eqToHom (by
        simpa [C, V', openSubsetPreimageImageOpen_eq (U := U) V] :
          ((C.obj M).presheaf.obj (Opposite.op V)) =
            ((C.obj M).presheaf.obj (Opposite.op V')) ) ≫
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M V').hom ≫
        M.presheaf.map (eqToHom (congrArg Opposite.op
          (openSubsetImagePreimageOpen_eq_of_le (U := U)
            (openSubsetImageOpen_le (U := U) V)))) ≫
          (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M V).inv = 𝟙 _
  rw [← hmap, hi]
  simp

/-- Helper for Lemma 6.31.8: on the image of an open of the open subspace, the underlying additive
presheaf of module extension by zero identifies with the original presheaf section object. -/
public noncomputable abbrev openSubsetModulePresheafExtensionByZeroImageSectionIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf).obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V)) ≅
      ℱ.presheaf.obj (Opposite.op V) := by
  let hV : U.isOpenEmbedding.functor.obj V ≤ U := openSubsetImageOpen_le (U := U) V
  -- First identify sections on the image open with sections on its pullback to `U`, then rewrite
  -- `preimage (image V) = V`.
  exact
    (eqToIso (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hV)) ≪≫
      eqToIso (by simpa [openSubsetPreimageImageOpen_eq (U := U) V])


/-- Helper for Lemma 6.31.8: on an ambient open contained in `U`, the inverse image-section
comparison followed by restriction back along `image (preimage W) = W` cancels the defining
inside-`U` object identification. -/
public theorem openSubsetModulePresheafExtensionByZeroImageSectionIso_left_triangle_component
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    {W : (Opens X.carrier)ᵒᵖ} (hW : W.unop ≤ U) :
    eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hW) ≫
      (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ
        (openSubsetPreimageOpen U W.unop)).inv ≫
      (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
          ℱ).presheaf).map
        (eqToHom (congrArg Opposite.op
          (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))) = 𝟙 _ := by
  let V := openSubsetPreimageOpen U W.unop
  let iW := eqToHom (congrArg Opposite.op
    (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))
  have hV : (Opposite.op (U.isOpenEmbedding.functor.obj V) : (Opens X.carrier)ᵒᵖ).unop ≤ U :=
    openSubsetImageOpen_le (U := U) V
  rw [openSubsetModulePresheafExtensionByZero_map_eq_of_le (U := U) ℱ iW hV hW]
  have hpre :
      ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map iW.unop).op =
        eqToHom (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) V)) := by
    apply Subsingleton.elim
  rw [hpre, CategoryTheory.eqToHom_map]
  simp [openSubsetModulePresheafExtensionByZeroImageSectionIso,
    openSubsetPreimageImageOpen_eq, V, iW, Category.assoc]

/-- Helper for Lemma 6.31.8: after passing to image opens, the section comparison for the
explicit module presheaf extension-by-zero is natural in the module argument. -/
public theorem openSubsetModulePresheafExtensionByZeroImageSectionIso_inv_naturality_module
    {ℱ 𝒢 : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)}
    (η : ℱ ⟶ 𝒢) (V : Opens (extensionByZeroOpenSubsetSpace U)) :
    ((PresheafOfModules.toPresheaf _).map η).app (Opposite.op V) ≫
        (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) 𝒢 V).inv =
      (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V).inv ≫
        ((PresheafOfModules.toPresheaf _).map
          ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).map η)).app (Opposite.op (U.isOpenEmbedding.functor.obj V)) := by
  let hV : U.isOpenEmbedding.functor.obj V ≤ U := openSubsetImageOpen_le (U := U) V
  change ((PresheafOfModules.toPresheaf _).map η).app (Opposite.op V) ≫
        (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) 𝒢 V).inv =
      (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V).inv ≫
        ((PresheafOfModules.toPresheaf ambientModuleRingSheaf.presheaf).map
          (openSubsetModuleExtensionByZeroHom U
            ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
              (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf)
            η)).app (Opposite.op (U.isOpenEmbedding.functor.obj V))
  have hmap :
      ((PresheafOfModules.toPresheaf ambientModuleRingSheaf.presheaf).map
          (openSubsetModuleExtensionByZeroHom U
            ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
              (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf)
            η)).app (Opposite.op (U.isOpenEmbedding.functor.obj V)) =
        (openSubsetPresheafExtensionByInitialObjectHom U
          ((PresheafOfModules.toPresheaf _).map η)).app
            (Opposite.op (U.isOpenEmbedding.functor.obj V)) := by
    simpa using congrArg (fun F => F.app (Opposite.op (U.isOpenEmbedding.functor.obj V)))
      (openSubsetModuleExtensionByZeroHom_toPresheaf_eq U
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf) η)
  rw [hmap]
  change ((PresheafOfModules.toPresheaf _).map η).app (Opposite.op V) ≫
        (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) 𝒢 V).inv =
      (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V).inv ≫
        openSubsetPresheafExtensionByInitialObjectHomApp U
          ((PresheafOfModules.toPresheaf _).map η)
          (Opposite.op (U.isOpenEmbedding.functor.obj V))
  rw [openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le U
    ((PresheafOfModules.toPresheaf _).map η)
    (Opposite.op (U.isOpenEmbedding.functor.obj V)) hV]
  let eF₁ := eqToIso
    (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hV)
  let eG₁ := eqToIso
    (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) 𝒢 hV)
  let hF₂ : ℱ.presheaf.obj (Opposite.op (openSubsetPreimageOpen U
      (U.isOpenEmbedding.functor.obj V))) = ℱ.presheaf.obj (Opposite.op V) := by
    simpa [openSubsetPreimageImageOpen_eq (U := U) V]
  let hG₂ : 𝒢.presheaf.obj (Opposite.op (openSubsetPreimageOpen U
      (U.isOpenEmbedding.functor.obj V))) = 𝒢.presheaf.obj (Opposite.op V) := by
    simpa [openSubsetPreimageImageOpen_eq (U := U) V]
  let eF₂ := eqToIso hF₂
  let eG₂ := eqToIso hG₂
  change ((PresheafOfModules.toPresheaf _).map η).app (Opposite.op V) ≫
      (eG₁ ≪≫ eG₂).inv =
    (eF₁ ≪≫ eF₂).inv ≫
      (eF₁.hom ≫ ((PresheafOfModules.toPresheaf _).map η).app
        (Opposite.op (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V))) ≫ eG₁.inv)
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc]
  change (((PresheafOfModules.toPresheaf _).map η).app (Opposite.op V) ≫ eG₂.inv) ≫
      eG₁.inv =
    (eF₂.inv ≫ ((PresheafOfModules.toPresheaf _).map η).app
      (Opposite.op (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V)))) ≫ eG₁.inv
  have hnat' :
      ((PresheafOfModules.toPresheaf _).map η).app (Opposite.op V) ≫ eG₂.inv =
        eF₂.inv ≫ ((PresheafOfModules.toPresheaf _).map η).app
          (Opposite.op (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V))) := by
    have hnat := ((PresheafOfModules.toPresheaf _).map η).naturality
      (eqToHom (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) V).symm))
    dsimp [eF₂, eG₂]
    rw [← CategoryTheory.eqToHom_map, ← CategoryTheory.eqToHom_map]
    exact hnat.symm
  rw [hnat']
  rfl


/-- Helper for Lemma 6.31.8: after passing to image opens, the section comparison for the
explicit presheaf extension-by-zero is natural with respect to restriction maps on `U`. -/
public theorem openSubsetModulePresheafExtensionByZeroImageSectionIso_inv_naturality
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop).inv ≫
        (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
            ℱ).presheaf).map (U.isOpenEmbedding.functor.map i.unop).op =
      ℱ.presheaf.map i ≫
        (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ W.unop).inv := by
  let hV : U.isOpenEmbedding.functor.obj V.unop ≤ U := openSubsetImageOpen_le (U := U) V.unop
  let hW : U.isOpenEmbedding.functor.obj W.unop ≤ U := openSubsetImageOpen_le (U := U) W.unop
  have hpre :
      ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
          (U.isOpenEmbedding.functor.map i.unop).op.unop).op =
        eqToHom (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) V.unop)) ≫
          i ≫
            eqToHom
              (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) W.unop)).symm := by
    -- The category of opens is thin, so the transported preimage/image map is uniquely forced.
    apply Subsingleton.elim
  -- Rewrite the ambient restriction map on image opens back to the original restriction map on
  -- `U`, then cancel the transport isomorphisms introduced by the image-open identifications.
  rw [openSubsetModulePresheafExtensionByZero_map_eq_of_le
    (U := U) ℱ (i := (U.isOpenEmbedding.functor.map i.unop).op) hV hW]
  rw [hpre, Functor.map_comp, Functor.map_comp, Category.assoc]
  rw [CategoryTheory.eqToHom_map, CategoryTheory.eqToHom_map]
  simp [openSubsetModulePresheafExtensionByZeroImageSectionIso, Category.assoc]

/-- Helper for Lemma 6.31.8: on opposite opens of `U`, the morphism obtained by taking an image
open in `X` and then pulling it back to `U` is the original morphism up to the canonical
`preimage (image V) = V` transports. -/
public theorem openSubsetPreimageImageOpen_op_map_eq
    {V W : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ} (i : V ⟶ W) :
    ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map
        (U.isOpenEmbedding.functor.map i.unop).op.unop).op =
      eqToHom (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) V.unop)) ≫
        i ≫
          eqToHom
            (congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) W.unop)).symm := by
  -- The category of opens is thin, so once the source and target objects are identified there is
  -- only one morphism to compare.
  apply Subsingleton.elim

/-- Helper for Lemma 6.31.8: the underlying additive natural transformation of the unit of the
explicit presheaf extension-by-zero ⊣ concrete restriction adjunction, assembled from the
source-facing image-section identifications. -/
public noncomputable def presheafModuleExtensionUnit_toPresheaf
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)) :
    ℱ.presheaf ⟶
      ((openSubsetModuleConcreteRestriction (U := U)).obj
        ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
          ℱ)).presheaf where
  app V :=
    (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop).inv ≫
      (openSubsetModuleConcreteRestrictionToPresheafIso (U := U)
        ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ)
        V.unop).inv
  naturality := by
    intro V W i
    -- Naturality of the unit is naturality of each section identification, glued by the inverse of
    -- the concrete-restriction identification.
    rw [← Category.assoc,
      ← openSubsetModulePresheafExtensionByZeroImageSectionIso_inv_naturality (U := U) ℱ i,
      Category.assoc, Category.assoc]
    congr 1

/-- Helper for Lemma 6.31.8: the unit component (as a morphism of presheaves of modules) of the
explicit presheaf extension-by-zero ⊣ concrete restriction adjunction. -/
public noncomputable def presheafModuleExtensionUnitApp
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)) :
    ℱ ⟶ (openSubsetModuleConcreteRestriction (U := U)).obj
          ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ) :=
  PresheafOfModules.homMk (presheafModuleExtensionUnit_toPresheaf (U := U) ℱ) (by
    intro V r m
    -- The unit component factors through the image-section identification and the concrete
    -- restriction identification; linearity follows from the ring-level cancellation plus the
    -- semilinearity of each identification (one along `α`, the other along the image-open ring
    -- comparison `ringIso`).
    let G := (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ
    -- (B) image-section iso is `ringIso`-semilinear in the source `O|_U`-scalar.
    have hB :
        (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop).inv (r • m) =
          (openSubsetRingPullbackImageObjIso (U := U) V.unop).hom r •
            (openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop).inv m := by
      have hVeq' :
          (Opposite.op V.unop : (Opens ((Opens.toTopCat X.carrier).obj U))ᵒᵖ) =
            Opposite.op (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V.unop)) :=
        congrArg Opposite.op (openSubsetPreimageImageOpen_eq (U := U) V.unop).symm
      -- Bridge: the source scalar transported to the preimage open equals `α (ringIso r)`.
      have hbridge :
          (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
              ambientModuleRingSheaf.presheaf).map (eqToHom hVeq')) r =
            ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
                ambientModuleRingSheaf.presheaf).app
                (Opposite.op (U.isOpenEmbedding.functor.obj V.unop))
              ((openSubsetRingPullbackImageObjIso (U := U) V.unop).hom r) := by
        have hkey :
            ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
                ambientModuleRingSheaf.presheaf).map
              ((U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop).op) ≫
            ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
                ambientModuleRingSheaf.presheaf).map (eqToHom hVeq') = 𝟙 _ := by
          rw [← CategoryTheory.Functor.map_comp,
            Subsingleton.elim
              ((U.isOpenEmbedding.isOpenMap.adjunction.unit.app V.unop).op ≫ eqToHom hVeq')
              (𝟙 _)]
          exact CategoryTheory.Functor.map_id _ _
        have happ := congrArg
          (fun φ => (ConcreteCategory.hom φ)
            (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
                ambientModuleRingSheaf.presheaf).app
                (Opposite.op (U.isOpenEmbedding.functor.obj V.unop))
              ((openSubsetRingPullbackImageObjIso (U := U) V.unop).hom r))) hkey
        simp only [CategoryTheory.comp_apply, CategoryTheory.id_apply] at happ
        rw [openSubsetRingPullbackImage_unit_cancel (U := U) V.unop r] at happ
        exact happ
      -- The preimage transport (second factor of the section iso) is a restriction map of `ℱ`.
      have hpre :
          (eqToIso (by
            simpa [openSubsetPreimageImageOpen_eq (U := U) V.unop] :
              ℱ.presheaf.obj
                  (Opposite.op (openSubsetPreimageOpen U (U.isOpenEmbedding.functor.obj V.unop))) =
                ℱ.presheaf.obj (Opposite.op V.unop))).inv =
            ℱ.presheaf.map (eqToHom hVeq') := by
        rw [eqToIso.inv, eqToHom_map]
      have hconv :
          ∀ z, (ConcreteCategory.hom (ℱ.presheaf.map (eqToHom hVeq'))) z =
            ℱ.map (eqToHom hVeq') z := fun _ => rfl
      dsimp only [openSubsetModulePresheafExtensionByZeroImageSectionIso]
      rw [Iso.trans_inv, CategoryTheory.comp_apply, CategoryTheory.comp_apply, hpre, hconv, hconv,
        PresheafOfModules.map_smul, hbridge, eqToIso.inv]
      exact openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_smul_of_le U
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf) ℱ (openSubsetImageOpen_le (U := U) V.unop)
        ((openSubsetRingPullbackImageObjIso (U := U) V.unop).hom r)
        (ℱ.map (eqToHom hVeq') m)
    -- (A) concrete restriction iso is `ringIso`-semilinear in the same source scalar.
    have hA :
        ∀ y : (G.presheaf).obj (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)),
          (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) G V.unop).inv
              ((openSubsetRingPullbackImageObjIso (U := U) V.unop).hom r • y) =
            r • (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) G V.unop).inv y := by
      intro y
      -- The additive section identification is the underlying map of the module-level
      -- restriction-of-scalars identification, which is `(pullback𝒪)`-linear; on the
      -- restriction-of-scalars source the `(pullback𝒪)`-action is `ringIso`-twisted.
      have hfun :
          ∀ z, (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) G V.unop).inv z =
            (openSubsetModuleConcreteRestrictionImageObjIso (U := U) G V.unop).inv z := fun _ => rfl
      rw [hfun, hfun]
      exact (openSubsetModuleConcreteRestrictionImageObjIso (U := U) G V.unop).inv.hom.map_smul r y
    show (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) G V.unop).inv
          ((openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop).inv (r • m)) =
        r • (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) G V.unop).inv
          ((openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop).inv m)
    rw [hB, hA])

public noncomputable def probe_presheafModuleExtensionUnitAppComponentIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (V : (Opens (extensionByZeroOpenSubsetSpace U))ᵒᵖ) :
    ℱ.obj V ≅
      ((openSubsetModuleConcreteRestriction (U := U)).obj
        ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ)).obj V := by
  let E := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
  let C := openSubsetModuleConcreteRestriction (U := U)
  let e := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop
  let c := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj ℱ) V.unop
  let unitAdd : ℱ.presheaf.obj V ≅ ((C.obj (E.obj ℱ)).presheaf).obj V := e.symm ≪≫ c.symm
  let unitV := (presheafModuleExtensionUnitApp (U := U) ℱ).app V
  refine
    { hom := unitV
      inv := ModuleCat.ofHom
        (X := ((C.obj (E.obj ℱ)).obj V)) (Y := ℱ.obj V)
        { toFun := fun y => unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)
          map_add' := by
            intro y z
            change unitAdd.inv
                ((show ((C.obj (E.obj ℱ)).presheaf.obj V) from y) +
                  (show ((C.obj (E.obj ℱ)).presheaf.obj V) from z)) =
              unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y) +
                unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from z)
            exact unitAdd.inv.hom.map_add y z
          map_smul' := ?_ }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro r y
    change unitAdd.inv (r • (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)) =
      r • unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)
    have hunit_apply : ∀ x : ℱ.obj V,
        unitV x = unitAdd.hom (show ℱ.presheaf.obj V from x) := by
      intro x
      rfl
    have hunit_injective : Function.Injective (fun x : ℱ.obj V => unitV x) := by
      intro a b h
      apply (CategoryTheory.Iso.addCommGroupIsoToAddEquiv unitAdd).injective
      change unitAdd.hom (show ℱ.presheaf.obj V from a) =
        unitAdd.hom (show ℱ.presheaf.obj V from b)
      simpa [hunit_apply] using h
    apply_fun (fun z : ℱ.obj V => unitV z) using hunit_injective
    have hleft :
        unitV (unitAdd.inv (r • (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y))) =
          r • (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y) := by
      rw [hunit_apply]
      exact ConcreteCategory.congr_hom unitAdd.inv_hom_id
        (r • (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y))
    have hright :
        unitV (r • unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)) =
          r • (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y) := by
      calc
        unitV (r • unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)) =
            r • unitV (unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)) := by
          exact unitV.hom.map_smul r (unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y))
        _ = r • unitAdd.hom (unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)) := by
          exact congrArg (fun z => r • z)
            (hunit_apply (unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)))
        _ = r • (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y) := by
          exact congrArg (fun z => r • z)
            (ConcreteCategory.congr_hom unitAdd.inv_hom_id
              (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y))
    exact hleft.trans hright.symm
  · ext y
    change unitAdd.inv (unitAdd.hom (show ℱ.presheaf.obj V from y)) = y
    exact ConcreteCategory.congr_hom unitAdd.hom_inv_id (show ℱ.presheaf.obj V from y)
  · ext y
    change unitAdd.hom (unitAdd.inv (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)) = y
    exact ConcreteCategory.congr_hom unitAdd.inv_hom_id
      (show ((C.obj (E.obj ℱ)).presheaf.obj V) from y)

public noncomputable def probe_presheafModuleExtensionUnitAppIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)) :
    ℱ ≅ (openSubsetModuleConcreteRestriction (U := U)).obj
          ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ) :=
  PresheafOfModules.isoMk
    (fun V => probe_presheafModuleExtensionUnitAppComponentIso (U := U) ℱ V)
    (fun {V W} i => by
      exact (presheafModuleExtensionUnitApp (U := U) ℱ).naturality i)

public instance probe_presheafModuleExtensionUnitApp_isIso
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)) :
    IsIso (presheafModuleExtensionUnitApp (U := U) ℱ) := by
  change IsIso (probe_presheafModuleExtensionUnitAppIso (U := U) ℱ).hom
  infer_instance

public theorem probe_presheafModuleExtensionUnit_naturality
    {ℱ 𝒢 : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)}
    (f : ℱ ⟶ 𝒢) :
    f ≫ presheafModuleExtensionUnitApp (U := U) 𝒢 =
      presheafModuleExtensionUnitApp (U := U) ℱ ≫
        (openSubsetModuleConcreteRestriction (U := U)).map
          ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).map f) := by
  apply (PresheafOfModules.toPresheaf _).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply NatTrans.ext
  funext V
  let E := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
  let C := openSubsetModuleConcreteRestriction (U := U)
  let eF := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop
  let eG := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) 𝒢 V.unop
  let cF := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj ℱ) V.unop
  let cG := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj 𝒢) V.unop
  let η := E.map f
  have hE :=
    openSubsetModulePresheafExtensionByZeroImageSectionIso_inv_naturality_module
      (U := U) f V.unop
  have hC :=
    openSubsetModuleConcreteRestrictionToPresheafIso_inv_naturality_module
      (U := U) η V.unop
  change (((PresheafOfModules.toPresheaf _).map f).app V ≫ eG.inv) ≫ cG.inv =
    (eF.inv ≫ cF.inv) ≫
      ((PresheafOfModules.toPresheaf _).map (C.map η)).app V
  rw [hE]
  change eF.inv ≫ (((PresheafOfModules.toPresheaf _).map η).app
        (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)) ≫ cG.inv) =
    eF.inv ≫ cF.inv ≫
      ((PresheafOfModules.toPresheaf _).map (C.map η)).app V
  have hC' :
      eF.inv ≫ (((PresheafOfModules.toPresheaf _).map η).app
          (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)) ≫ cG.inv) =
        eF.inv ≫ (cF.inv ≫
          ((PresheafOfModules.toPresheaf _).map (C.map η)).app V) := by
    exact congrArg (fun k => eF.inv ≫ k) hC.symm
  simpa [Category.assoc] using hC'

public noncomputable def probe_presheafModuleExtensionUnitNatIso :
    𝟭 (PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)) ≅
      openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf ⋙
        openSubsetModuleConcreteRestriction (U := U) :=
  NatIso.ofComponents
    (fun ℱ => probe_presheafModuleExtensionUnitAppIso (U := U) ℱ)
    (fun {ℱ 𝒢} f => by
      exact probe_presheafModuleExtensionUnit_naturality (U := U) f)

/-- Helper for Lemma 6.31.8: the counit-direction cancellation — transporting `α (= the ring
adjunction unit) followed by the open-map pullback comparison back along the image identification
recovers the original section.  This is the inverse-direction companion of the unit cancellation,
and the ring core of the counit linearity. -/
public theorem openSubsetRing_counit_cancel
    {W : Opens X.carrier} (hW : W ≤ U)
    (r : ambientModuleRingSheaf.presheaf.obj (Opposite.op W)) :
    (ambientModuleRingSheaf.presheaf.map
        (eqToHom (congrArg Opposite.op (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))))
      ((openSubsetRingPullbackImageObjIso (U := U) (openSubsetPreimageOpen U W)).hom
        (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
            ambientModuleRingSheaf.presheaf).app (Opposite.op W) r)) = r := by
  -- Replace the image comparison with the open-map pullback comparison, then use the counit
  -- relation `pullbackObjIso.hom ∘ α = restriction along the opens counit`.
  have hringIso :
      (openSubsetRingPullbackImageObjIso (U := U) (openSubsetPreimageOpen U W)).hom
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf).app (Opposite.op W) r) =
        ((U.isOpenEmbedding.isOpenMap.pullbackObjIso ambientModuleRingSheaf.presheaf).hom.app
            (Opposite.op ((Opens.map U.inclusion').obj W)))
          (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf).app (Opposite.op W) r) := by
    rfl
  rw [hringIso, openSubsetRing_pullbackObjIso_hom_unit_app (U := U) W]
  -- The remaining transport is `𝒪.map ((counit.app W).op ≫ eqToHom)`, identity in the thin opens.
  have hcounit : U.isOpenEmbedding.isOpenMap.adjunction.counit.app W =
      eqToHom (openSubsetImagePreimageOpen_eq_of_le (U := U) hW) := Subsingleton.elim _ _
  rw [hcounit]
  change (ambientModuleRingSheaf.presheaf.map
      (eqToHom (openSubsetImagePreimageOpen_eq_of_le (U := U) hW)).op ≫
      ambientModuleRingSheaf.presheaf.map
        (eqToHom (congrArg Opposite.op (openSubsetImagePreimageOpen_eq_of_le (U := U) hW)))) r = r
  rw [← ambientModuleRingSheaf.presheaf.map_comp,
    show (eqToHom (openSubsetImagePreimageOpen_eq_of_le (U := U) hW)).op ≫
        eqToHom (congrArg Opposite.op (openSubsetImagePreimageOpen_eq_of_le (U := U) hW)) =
        𝟙 (Opposite.op W) from Subsingleton.elim _ _,
    ambientModuleRingSheaf.presheaf.map_id]
  rfl

open Classical in

/-- Helper for Lemma 6.31.8: on an ambient open contained in `U`, the underlying additive
component of a module extension-by-zero morphism is the original component on the pulled-back
open, up to the defining object identifications. -/
public theorem openSubsetModulePresheafExtensionByZero_map_app_eq_of_le
    {ℱ 𝒢 : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf)}
    (η : ℱ ⟶ 𝒢) {W : (Opens X.carrier)ᵒᵖ} (hW : W.unop ≤ U) :
    ((PresheafOfModules.toPresheaf ambientModuleRingSheaf.presheaf).map
        ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).map η)).app W =
      eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hW) ≫
        ((PresheafOfModules.toPresheaf _).map η).app
          (Opposite.op (openSubsetPreimageOpen U W.unop)) ≫
        eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) 𝒢 hW).symm := by
  have hmap := congrArg (fun τ => τ.app W)
    (openSubsetModuleExtensionByZeroHom_toPresheaf_eq U
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
        (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf) η)
  have hle := openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le U
    ((PresheafOfModules.toPresheaf _).map η) W hW
  simpa [ambientModuleRingSheaf, openSubsetModulePresheafExtensionByZero,
    extensionByZeroOpenSubsetInclusion] using hmap.trans hle

/-- Helper for Lemma 6.31.8: the underlying additive natural transformation of the counit of the
explicit presheaf extension-by-zero ⊣ concrete restriction adjunction.  Inside `U` it is the
image-section / concrete-restriction identification; outside `U` the extension vanishes, so the
component is the unique map out of the initial object. -/
public noncomputable def presheafModuleExtensionCounit_toPresheaf
    (M : PresheafOfModules ambientModuleRingSheaf.presheaf) :
    ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
        ((openSubsetModuleConcreteRestriction (U := U)).obj M)).presheaf ⟶ M.presheaf where
  app W :=
    if h : W.unop ≤ U then
      eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U)
          ((openSubsetModuleConcreteRestriction (U := U)).obj M) h) ≫
        (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M
          (openSubsetPreimageOpen U W.unop)).hom ≫
        M.presheaf.map (eqToHom (congrArg Opposite.op
          (openSubsetImagePreimageOpen_eq_of_le (U := U) h)))
    else
      eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le (U := U)
          ((openSubsetModuleConcreteRestriction (U := U)).obj M) h) ≫
        (@initial.to AddCommGrpCat.{u} _ _ (M.presheaf.obj W))
  naturality := by
    intro V W i
    by_cases hV : V.unop ≤ U
    · have hW : W.unop ≤ U := le_trans (leOfHom i.unop) hV
      show (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
            ((openSubsetModuleConcreteRestriction (U := U)).obj M)).presheaf).map i ≫ _ = _ ≫ _
      rw [dif_pos hV, dif_pos hW,
        openSubsetModulePresheafExtensionByZero_map_eq_of_le (U := U) _ i hV hW]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      congr 1
      rw [← Category.assoc, openSubsetModuleConcreteRestrictionToPresheafIso_hom_naturality,
        Category.assoc]
      congr 1
      rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
      congr 1
    · -- Outside `U` the source object is the initial object, so both composites agree.
      have hsub : Subsingleton
          ((((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
              ((openSubsetModuleConcreteRestriction (U := U)).obj M)).presheaf).obj V ⟶
            M.presheaf.obj W) := by
        rw [openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le (U := U)
          ((openSubsetModuleConcreteRestriction (U := U)).obj M) hV]
        exact ⟨fun _ _ => initialIsInitial.hom_ext _ _⟩
      exact hsub.elim _ _

/-- Helper for Lemma 6.31.8: the inside-`U` component of the counit additive nat-trans. -/
public theorem presheafModuleExtensionCounit_toPresheaf_app_of_le
    (M : PresheafOfModules ambientModuleRingSheaf.presheaf) {W : (Opens X.carrier)ᵒᵖ}
    (hW : W.unop ≤ U) :
    (presheafModuleExtensionCounit_toPresheaf (U := U) M).app W =
      eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U)
          ((openSubsetModuleConcreteRestriction (U := U)).obj M) hW) ≫
        (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M
          (openSubsetPreimageOpen U W.unop)).hom ≫
        M.presheaf.map (eqToHom (congrArg Opposite.op
          (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))) :=
  dif_pos hW

/-- Helper for Lemma 6.31.8: the counit component (as a morphism of presheaves of modules) of the
explicit presheaf extension-by-zero ⊣ concrete restriction adjunction. -/
public noncomputable def presheafModuleExtensionCounitApp
    (M : PresheafOfModules ambientModuleRingSheaf.presheaf) :
    (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
        ((openSubsetModuleConcreteRestriction (U := U)).obj M) ⟶ M :=
  PresheafOfModules.homMk (presheafModuleExtensionCounit_toPresheaf (U := U) M) (by
    intro W r m
    by_cases hW : W.unop ≤ U
    · -- Inside `U`: the section-iso composite is linear via the counit cancellation.
      -- `.hom` semilinearity of the concrete-restriction identification.
      have hA_hom : ∀ (s : (((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
            ambientModuleRingSheaf.presheaf).obj (Opposite.op (openSubsetPreimageOpen U W.unop))))
          (x : (((openSubsetModuleConcreteRestriction (U := U)).obj M).obj
            (Opposite.op (openSubsetPreimageOpen U W.unop)))),
          (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M
              (openSubsetPreimageOpen U W.unop)).hom (s • x) =
            (openSubsetRingPullbackImageObjIso (U := U) (openSubsetPreimageOpen U W.unop)).hom s •
              (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M
                (openSubsetPreimageOpen U W.unop)).hom x := by
        intro s x
        have hfun : ∀ z, (openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M
              (openSubsetPreimageOpen U W.unop)).hom z =
            (openSubsetModuleConcreteRestrictionImageObjIso (U := U) M
              (openSubsetPreimageOpen U W.unop)).hom z := fun _ => rfl
        rw [hfun, hfun]
        exact (openSubsetModuleConcreteRestrictionImageObjIso (U := U) M
          (openSubsetPreimageOpen U W.unop)).hom.hom.map_smul s x
      have hconv : ∀ (z : ↑(M.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj
            (openSubsetPreimageOpen U W.unop))))),
          (ConcreteCategory.hom (M.presheaf.map (eqToHom (congrArg Opposite.op
            (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))))) z =
          M.map (eqToHom (congrArg Opposite.op
            (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))) z := fun _ => rfl
      rw [presheafModuleExtensionCounit_toPresheaf_app_of_le (U := U) M hW]
      simp only [CategoryTheory.comp_apply]
      rw [show (ConcreteCategory.hom (eqToHom (openSubsetModulePresheafExtensionByZero_obj_eq_of_le
              (U := U) ((openSubsetModuleConcreteRestriction (U := U)).obj M) hW))) (r • m) = _
          from openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U
            ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
              ambientModuleRingSheaf.presheaf) ((openSubsetModuleConcreteRestriction (U := U)).obj M)
            hW r m]
      erw [hA_hom]
      rw [hconv, hconv]
      erw [PresheafOfModules.map_smul, openSubsetRing_counit_cancel (U := U) hW]
      rfl
    · -- Outside `U` the source object is the zero module, so both sides vanish.
      have hsub : Subsingleton
          ((((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
              ((openSubsetModuleConcreteRestriction (U := U)).obj M)).presheaf).obj W) := by
        rw [openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le (U := U)
          ((openSubsetModuleConcreteRestriction (U := U)).obj M) hW]
        infer_instance
      rw [hsub.elim (r • m) 0, hsub.elim m 0, map_zero, smul_zero])

/-- Helper for Lemma 6.31.8: package the explicit presheaf extension-by-zero owner as the
canonical left-adjoint `PresheafOfModules.pullback` attached to the concrete restriction owner.

Closes via `Adjunction.leftAdjointUniq (openSubsetModuleConcreteRestrictionPullbackAdjunction)
(presheafExt ⊣ openSubsetModuleConcreteRestriction)`, the latter assembled by
`Adjunction.mkOfUnitCounit` from the proven unit `presheafModuleExtensionUnitApp` and counit
`presheafModuleExtensionCounitApp` (retained above, with full linearity), together with their
naturality in the module argument and the two triangle identities (section-iso bookkeeping). -/
public noncomputable abbrev openSubsetModulePresheafExtensionByZeroIsoPullbackLeft :
    PresheafOfModules.pullback
        (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf)) ≅
      openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf := by
  classical
  let adjExplicit :
      openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf ⊣
        openSubsetModuleConcreteRestriction (U := U) :=
    Adjunction.mkOfUnitCounit
      { unit :=
          { app := fun ℱ => presheafModuleExtensionUnitApp (U := U) ℱ
            naturality := by
              intro ℱ 𝒢 f
              apply (PresheafOfModules.toPresheaf _).map_injective
              rw [Functor.map_comp, Functor.map_comp]
              apply NatTrans.ext
              funext V
              let E := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
              let C := openSubsetModuleConcreteRestriction (U := U)
              let eF := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V.unop
              let eG := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) 𝒢 V.unop
              let cF := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj ℱ) V.unop
              let cG := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj 𝒢) V.unop
              let η := E.map f
              have hE :=
                openSubsetModulePresheafExtensionByZeroImageSectionIso_inv_naturality_module
                  (U := U) f V.unop
              have hC :=
                openSubsetModuleConcreteRestrictionToPresheafIso_inv_naturality_module
                  (U := U) η V.unop
              change (((PresheafOfModules.toPresheaf _).map f).app V ≫ eG.inv) ≫ cG.inv =
                (eF.inv ≫ cF.inv) ≫
                  ((PresheafOfModules.toPresheaf _).map (C.map η)).app V
              rw [hE]
              change eF.inv ≫ (((PresheafOfModules.toPresheaf _).map η).app
                    (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)) ≫ cG.inv) =
                eF.inv ≫ cF.inv ≫
                  ((PresheafOfModules.toPresheaf _).map (C.map η)).app V
              have hC' :
                  eF.inv ≫ (((PresheafOfModules.toPresheaf _).map η).app
                      (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)) ≫ cG.inv) =
                    eF.inv ≫ (cF.inv ≫
                      ((PresheafOfModules.toPresheaf _).map (C.map η)).app V) := by
                exact congrArg (fun k => eF.inv ≫ k) hC.symm
              simpa [Category.assoc] using hC' }
        counit :=
          { app := fun M => presheafModuleExtensionCounitApp (U := U) M
            naturality := by
              intro M N f
              apply (PresheafOfModules.toPresheaf _).map_injective
              rw [Functor.map_comp, Functor.map_comp]
              apply NatTrans.ext
              funext W
              let E := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
              let C := openSubsetModuleConcreteRestriction (U := U)
              by_cases hW : W.unop ≤ U
              · let V := openSubsetPreimageOpen U W.unop
                let iW := eqToHom (congrArg Opposite.op
                  (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))
                have hnat := ((PresheafOfModules.toPresheaf _).map f).naturality iW
                change ((PresheafOfModules.toPresheaf _).map (E.map (C.map f))).app W ≫
                    (presheafModuleExtensionCounit_toPresheaf (U := U) N).app W =
                  (presheafModuleExtensionCounit_toPresheaf (U := U) M).app W ≫
                    ((PresheafOfModules.toPresheaf _).map f).app W
                rw [openSubsetModulePresheafExtensionByZero_map_app_eq_of_le (U := U)
                    ((C.map f)) hW,
                  presheafModuleExtensionCounit_toPresheaf_app_of_le (U := U) N hW,
                  presheafModuleExtensionCounit_toPresheaf_app_of_le (U := U) M hW]
                let hM := openSubsetModulePresheafExtensionByZero_obj_eq_of_le
                    (U := U) (C.obj M) hW
                let hN := openSubsetModulePresheafExtensionByZero_obj_eq_of_le
                    (U := U) (C.obj N) hW
                let cM := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M V
                let cN := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) N V
                have hstep :
                    ((PresheafOfModules.toPresheaf _).map (C.map f)).app (Opposite.op V) ≫
                        cN.hom ≫ N.presheaf.map iW =
                      cM.hom ≫ M.presheaf.map iW ≫
                        ((PresheafOfModules.toPresheaf _).map f).app W := by
                  dsimp [V] at hnat ⊢
                  change (((PresheafOfModules.toPresheaf _).map (C.map f)).app
                      (Opposite.op (openSubsetPreimageOpen U W.unop)) ≫
                      cN.hom) ≫ N.presheaf.map iW =
                    (cM.hom ≫ M.presheaf.map iW) ≫
                      ((PresheafOfModules.toPresheaf _).map f).app W
                  rw [openSubsetModuleConcreteRestrictionToPresheafIso_hom_naturality_module
                      (U := U) f V]
                  have hnat' :
                      cM.hom ≫ (((PresheafOfModules.toPresheaf _).map f).app
                          (Opposite.op (U.isOpenEmbedding.functor.obj
                            (openSubsetPreimageOpen U W.unop))) ≫ N.presheaf.map iW) =
                        cM.hom ≫ (M.presheaf.map iW ≫
                          ((PresheafOfModules.toPresheaf _).map f).app W) := by
                    exact congrArg (fun k => cM.hom ≫ k) hnat.symm
                  simpa [Category.assoc] using hnat'
                have hwrap :
                    (eqToHom hM ≫
                        (((PresheafOfModules.toPresheaf _).map (C.map f)).app (Opposite.op V) ≫
                          eqToHom hN.symm)) ≫ eqToHom hN ≫ cN.hom ≫ N.presheaf.map iW =
                      eqToHom hM ≫
                        (((PresheafOfModules.toPresheaf _).map (C.map f)).app (Opposite.op V) ≫
                          cN.hom ≫ N.presheaf.map iW) := by
                  exact comp_eqToHom_symm_eqToHom_assoc_nested (h := hN)
                    (a := eqToHom hM)
                    (f := ((PresheafOfModules.toPresheaf _).map (C.map f)).app (Opposite.op V))
                    (g := cN.hom) (k := N.presheaf.map iW)
                have hmain := congrArg (fun k => eqToHom hM ≫ k) hstep
                calc
                  (eqToHom hM ≫
                        (((PresheafOfModules.toPresheaf _).map (C.map f)).app (Opposite.op V) ≫
                          eqToHom hN.symm)) ≫ eqToHom hN ≫ cN.hom ≫ N.presheaf.map iW =
                    eqToHom hM ≫
                        (((PresheafOfModules.toPresheaf _).map (C.map f)).app (Opposite.op V) ≫
                          cN.hom ≫ N.presheaf.map iW) := hwrap
                  _ = eqToHom hM ≫
                        (cM.hom ≫ M.presheaf.map iW ≫
                          ((PresheafOfModules.toPresheaf _).map f).app W) := by
                    simpa [Category.assoc] using hmain
              · have hsub : Subsingleton
                    ((((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj
                        ((openSubsetModuleConcreteRestriction (U := U)).obj M)).presheaf).obj W ⟶
                      N.presheaf.obj W) := by
                  rw [openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le (U := U)
                    ((openSubsetModuleConcreteRestriction (U := U)).obj M) hW]
                  exact ⟨fun _ _ => initialIsInitial.hom_ext _ _⟩
                exact hsub.elim _ _ }
        left_triangle := by
          apply NatTrans.ext
          funext ℱ
          change (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).map
              (presheafModuleExtensionUnitApp (U := U) ℱ) ≫
            presheafModuleExtensionCounitApp (U := U)
              ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ) = 𝟙 _
          apply (PresheafOfModules.toPresheaf _).map_injective
          rw [Functor.map_comp]
          apply NatTrans.ext
          funext W
          by_cases hW : W.unop ≤ U
          · let E := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
            let V := openSubsetPreimageOpen U W.unop
            let iW := eqToHom (congrArg Opposite.op
              (openSubsetImagePreimageOpen_eq_of_le (U := U) hW))
            change ((PresheafOfModules.toPresheaf _).map
                (E.map (presheafModuleExtensionUnitApp (U := U) ℱ))).app W ≫
              (presheafModuleExtensionCounit_toPresheaf (U := U) (E.obj ℱ)).app W =
                𝟙 _
            rw [openSubsetModulePresheafExtensionByZero_map_app_eq_of_le (U := U)
                (presheafModuleExtensionUnitApp (U := U) ℱ) hW,
              presheafModuleExtensionCounit_toPresheaf_app_of_le (U := U) (E.obj ℱ) hW]
            let hF := openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U) ℱ hW
            let hEC := openSubsetModulePresheafExtensionByZero_obj_eq_of_le (U := U)
              ((openSubsetModuleConcreteRestriction (U := U)).obj (E.obj ℱ)) hW
            let e := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) ℱ V
            let c := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj ℱ) V
            change (eqToHom hF ≫ ((e.inv ≫ c.inv) ≫ eqToHom hEC.symm)) ≫
                eqToHom hEC ≫ c.hom ≫ (E.obj ℱ).presheaf.map iW = 𝟙 _
            rw [comp_eqToHom_symm_eqToHom_assoc_nested (h := hEC)
              (a := eqToHom hF) (f := e.inv ≫ c.inv) (g := c.hom)
              (k := (E.obj ℱ).presheaf.map iW)]
            have hcancel_c :
                eqToHom hF ≫ (e.inv ≫ c.inv) ≫ c.hom ≫ (E.obj ℱ).presheaf.map iW =
                  eqToHom hF ≫ e.inv ≫ (E.obj ℱ).presheaf.map iW := by
              simp only [Category.assoc, Iso.inv_hom_id_assoc]
            rw [hcancel_c]
            exact openSubsetModulePresheafExtensionByZeroImageSectionIso_left_triangle_component
              (U := U) ℱ hW
          · have hsub : Subsingleton
                (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf.obj W ⟶
                  ((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ).presheaf.obj W) := by
              rw [openSubsetModulePresheafExtensionByZero_obj_eq_of_not_le (U := U) ℱ hW]
              exact ⟨fun _ _ => initialIsInitial.hom_ext _ _⟩
            exact hsub.elim _ _
        right_triangle := by
          apply NatTrans.ext
          funext M
          change presheafModuleExtensionUnitApp (U := U)
              ((openSubsetModuleConcreteRestriction (U := U)).obj M) ≫
            (openSubsetModuleConcreteRestriction (U := U)).map
              (presheafModuleExtensionCounitApp (U := U) M) = 𝟙 _
          apply (PresheafOfModules.toPresheaf _).map_injective
          rw [Functor.map_comp]
          apply NatTrans.ext
          funext V
          let E := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
          let C := openSubsetModuleConcreteRestriction (U := U)
          let η := presheafModuleExtensionCounitApp (U := U) M
          have hC := openSubsetModuleConcreteRestrictionToPresheafIso_inv_naturality_module
            (U := U) η V.unop
          change (presheafModuleExtensionUnit_toPresheaf (U := U) (C.obj M)).app V ≫
              ((PresheafOfModules.toPresheaf _).map (C.map η)).app V = 𝟙 _
          rw [presheafModuleExtensionUnit_toPresheaf]
          let e := openSubsetModulePresheafExtensionByZeroImageSectionIso (U := U) (C.obj M) V.unop
          let c := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) (E.obj (C.obj M)) V.unop
          let cM := openSubsetModuleConcreteRestrictionToPresheafIso (U := U) M V.unop
          change e.inv ≫ (c.inv ≫
              ((PresheafOfModules.toPresheaf _).map (C.map η)).app V) = 𝟙 _
          have hC' :
              e.inv ≫ (c.inv ≫
                  ((PresheafOfModules.toPresheaf _).map (C.map η)).app V) =
                e.inv ≫ (((PresheafOfModules.toPresheaf _).map η).app
                  (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)) ≫ cM.inv) := by
            exact congrArg (fun k => e.inv ≫ k) hC
          rw [hC']
          change e.inv ≫ (presheafModuleExtensionCounit_toPresheaf (U := U) M).app
              (Opposite.op (U.isOpenEmbedding.functor.obj V.unop)) ≫ cM.inv = 𝟙 _
          rw [presheafModuleExtensionCounit_toPresheaf_app_of_le (U := U) M
            (openSubsetImageOpen_le (U := U) V.unop)]
          simpa [presheafModuleExtensionCounitApp,
            presheafModuleExtensionCounit_toPresheaf,
            openSubsetModulePresheafExtensionByZeroImageSectionIso,
            openSubsetPreimageImageOpen_eq, openSubsetImagePreimageOpen_eq_of_le,
            E, C, η, e, c, cM, Category.assoc] using
            openSubsetModuleConcreteRestrictionToPresheafIso_preimageImage_cancel
              (U := U) M V.unop }
  exact Adjunction.leftAdjointUniq
    (openSubsetModuleConcreteRestrictionPullbackAdjunction (U := U)) adjExplicit

/-- Helper for Lemma 6.31.8: package the concrete restriction owner as the public pullback owner
for presheaves of modules along the open inclusion `U ↪ X`. -/
public noncomputable abbrev openSubsetModuleConcreteRestrictionIsoPublicPullback :
    openSubsetModuleConcreteRestriction (U := U) ≅
      PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf) :=
  -- Both the concrete restriction owner `pushforward (pullbackIso.hom)` and the public
  -- `pullback (unit)` owner are left adjoints to `pushforward (unit)`, so they agree by the
  -- uniqueness of left adjoints.
  Adjunction.leftAdjointUniq
    (PresheafOfModules.pushforwardPushforwardAdj
      U.isOpenEmbedding.isOpenMap.adjunction
      ((U.isOpenEmbedding.isOpenMap.pullbackIso :
          TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
        ambientModuleRingSheaf.presheaf)
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
        ambientModuleRingSheaf.presheaf)
      (by
        ext W s
        exact (openSubsetRing_pullbackObjIso_hom_unit_app (U := U) W.unop s).symm)
      (by
        ext V t
        refine (openSubsetRing_pullback_unit_triangle (U := U) V.unop
          ((U.isOpenEmbedding.isOpenMap.pullbackObjIso
            ambientModuleRingSheaf.presheaf).hom.app V t)).trans ?_
        exact congr($((U.isOpenEmbedding.isOpenMap.pullbackObjIso
          ambientModuleRingSheaf.presheaf).hom_inv_id_app V) t)))
    (PresheafOfModules.pullbackPushforwardAdjunction _)

/-- Helper for Lemma 6.31.8: the explicit presheaf extension-by-zero functor has the expected
Hom-set equivalence against restriction to `U`, obtained by lifting the additive adjunction on
underlying presheaves. -/
public noncomputable def openSubsetModulePresheafExtensionByZero_homEquiv_direct
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj ambientModuleRingSheaf.presheaf))
    (𝒢 : PresheafOfModules ambientModuleRingSheaf.presheaf) :
    (((openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ) ⟶ 𝒢) ≃
      (ℱ ⟶
        (PresheafOfModules.pullback
          ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
            ambientModuleRingSheaf.presheaf)).obj 𝒢) := by
  let hAdj :
      openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf ⊣
        PresheafOfModules.pullback
          ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
            (RingedSpace.ringCatSheaf X).presheaf) := by
    -- This is the source-facing adjunction established just below.
    simpa using
      Adjunction.ofNatIsoRight
        ((openSubsetModuleConcreteRestrictionPullbackAdjunction (U := U)).ofNatIsoLeft
          (openSubsetModulePresheafExtensionByZeroIsoPullbackLeft (X := X) U))
        (openSubsetModuleConcreteRestrictionIsoPublicPullback (X := X) U)
  simpa [ambientModuleRingSheaf] using hAdj.homEquiv ℱ 𝒢

/-- Lemma 6.31.8 (1): the explicit extension-by-zero functor on presheaves of modules is left
adjoint to restriction to the open subset `U`. -/
noncomputable abbrev openSubsetModulePresheafExtensionByZeroAdjunction :
    openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf ⊣
      PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          (RingedSpace.ringCatSheaf X).presheaf) := by
  -- After unfolding the source-facing extension-by-zero owner, this is exactly the imported
  -- concrete pullback/pushforward adjunction.
  simpa using
    Adjunction.ofNatIsoRight
      ((openSubsetModuleConcreteRestrictionPullbackAdjunction (U := U)).ofNatIsoLeft
        (openSubsetModulePresheafExtensionByZeroIsoPullbackLeft (X := X) U))
      (openSubsetModuleConcreteRestrictionIsoPublicPullback (X := X) U)

-- Proof sketch: extract the left-adjoint structure carried by the explicit adjunction.
/-- The presheaf extension-by-zero functor inherits its left-adjoint structure from the canonical
adjunction. -/
theorem openSubsetModulePresheafExtensionByZeroAdjunction_isLeftAdjoint :
    (openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf).IsLeftAdjoint
    := by
  -- The adjunction above immediately packages the left-adjoint structure.
  exact (openSubsetModulePresheafExtensionByZeroAdjunction U).isLeftAdjoint

/-- The canonical extension-by-zero functor on presheaves of modules is a left adjoint. -/
instance :
    (openSubsetModulePresheafExtensionByZero U (RingedSpace.ringCatSheaf X).presheaf).IsLeftAdjoint :=
  openSubsetModulePresheafExtensionByZeroAdjunction_isLeftAdjoint U

public noncomputable def probe_presheafExtensionPublicPullbackCompIso :
    openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf ⋙
      PresheafOfModules.pullback
        ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} U.inclusion').unit.app
          ambientModuleRingSheaf.presheaf) ≅
      𝟭 (PresheafOfModules
        ((TopCat.Presheaf.pullback RingCat.{u} U.inclusion').obj
          ambientModuleRingSheaf.presheaf)) := by
  exact
    (CategoryTheory.Functor.isoWhiskerLeft
      (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf)
      (openSubsetModuleConcreteRestrictionIsoPublicPullback (X := X) U)).symm ≪≫
      (probe_presheafModuleExtensionUnitNatIso (U := U)).symm

/-- Helper for Lemma 6.31.8: after forgetting the module structure, restricting a module sheaf to
the open subset `U` agrees with pulling back the underlying additive sheaf along the open
inclusion. -/
public noncomputable abbrev moduleSheafRestrictionToOpen_toSheafIso
    (𝒢 : SheafOfModules ambientModuleRingSheaf) :
    (SheafOfModules.toSheaf
        ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf)).obj
      ((moduleSheafRestrictionToOpen U ambientModuleRingSheaf).obj 𝒢) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ((SheafOfModules.toSheaf ambientModuleRingSheaf).obj 𝒢) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let e₁ :=
    (SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U)).mapIso
      ((moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U
        ambientModuleRingSheaf).symm.app 𝒢)
  let e₂ :=
    ((Topology.IsOpenEmbedding.sheafPullbackIso AddCommGrpCat U.isOpenEmbedding).app
      ((SheafOfModules.toSheaf ambientModuleRingSheaf).obj 𝒢)).symm
  -- First rewrite restriction via the concrete open-embedding pushforward owner, then replace
  -- the naive pullback by the canonical sheaf pullback.
  simpa [SheafOfModules.toSheaf, SheafOfModules.pushforward, ambientModuleRingSheaf,
    openSubspaceModuleRingSheaf] using e₁ ≪≫ e₂

/-- Helper for Lemma 6.31.8: the comparison from module-sheaf restriction to the underlying
additive sheaf pullback is natural in the ambient module sheaf. -/
public noncomputable abbrev moduleSheafRestrictionToOpen_toSheafNatIso :
    moduleSheafRestrictionToOpen U ambientModuleRingSheaf ⋙
        SheafOfModules.toSheaf
          ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            ambientModuleRingSheaf) ≅
      SheafOfModules.toSheaf ambientModuleRingSheaf ⋙
        TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let e₁ := CategoryTheory.Functor.isoWhiskerRight
    (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U ambientModuleRingSheaf).symm
    (SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U))
  let e₂ := CategoryTheory.Functor.isoWhiskerLeft
    (SheafOfModules.toSheaf ambientModuleRingSheaf)
    ((Topology.IsOpenEmbedding.sheafPullbackIso AddCommGrpCat U.isOpenEmbedding).symm)
  -- The functor comparison is the objectwise version above, promoted to a natural isomorphism.
  exact e₁ ≪≫ e₂

/-- Helper for Lemma 6.31.8: after forgetting module structure, the explicit module-valued
extension-by-zero sheaf is literally the additive extension-by-initial-object sheaf on the
underlying additive sheaf over `U`. -/
public noncomputable abbrev openSubsetModuleSheafExtensionByZeroToAdditiveExtensionIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    (SheafOfModules.toSheaf ambientModuleRingSheaf).obj
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ) ≅
      (j! U).obj ((SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U)).obj ℱ) :=
  -- Route correction: the explicit module sheaf `j_!` is built by module presheaf extension
  -- followed by module sheafification, and both forgetful comparisons are definitionally the
  -- additive `j!` construction.
  eqToIso rfl

public theorem probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_comp_pullbackIso_hom :
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom =
      (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).hom ≫
        (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf)) := by
  let e := ((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).app
          ambientModuleRingSheaf.presheaf)
  let h := openSubspaceModuleRingSheafConcretePullback_obj_eq (U := U)
  let a := (Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map
        ((Topology.IsOpenEmbedding.sheafPullbackIso RingCat.{u} U.isOpenEmbedding).hom.app ambientModuleRingSheaf)
  dsimp [openSubspaceModuleRingSheafObjIsoConcretePullback,
    openSubspaceModuleRingSheafIsoConcretePullback]
  have hcancel :
      (eqToHom h ≫ e.inv) ≫ e.hom = eqToHom h := by
    have hc := congrArg (fun k => eqToHom h ≫ k) e.inv_hom_id
    change eqToHom h ≫ (e.inv ≫ e.hom) = eqToHom h ≫ 𝟙 _ at hc
    simpa [Category.assoc] using hc
  have hright : a ≫ (eqToHom h ≫ e.inv) ≫ e.hom = a ≫ eqToHom h := by
    simpa [a, Category.assoc] using congrArg (fun k => a ≫ k) hcancel
  change (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom =
    a ≫ (eqToHom h ≫ e.inv) ≫ e.hom
  rw [hright]
  rfl

public theorem probe_openSubsetRing_publicUnit_comp_pullbackIso_hom :
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
        (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf) ≫
      (TopCat.Presheaf.pushforward RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
        (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf)) =
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
      ambientModuleRingSheaf.obj := by
  ext W s
  simpa [TopCat.Presheaf.pushforward_obj_obj, TopCat.Presheaf.pushforward_map_app] using
    (openSubsetRing_pullbackObjIso_hom_unit_app (U := U) W s)

public theorem probe_hleft :
    let E := (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf))
    let P := TopCat.Presheaf.pushforward RingCat.{u} (extensionByZeroOpenSubsetInclusion U)
    (((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
        (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom ≫
      P.map (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).hom) ≫ P.map E =
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
      ambientModuleRingSheaf.obj := by
  dsimp
  let E := (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf))
  let P := TopCat.Presheaf.pushforward RingCat.{u} (extensionByZeroOpenSubsetInclusion U)
  have hmap :
      P.map (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).hom ≫ P.map E =
        P.map ((openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).hom ≫ E) := by
    exact (P.map_comp (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).hom E).symm
  rw [Category.assoc]
  erw [hmap]
  erw [← probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_comp_pullbackIso_hom (U := U)]
  change ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
        (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom ≫
      (Opens.map (extensionByZeroOpenSubsetInclusion U)).op.whiskerLeft
        ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom) =
    Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
      ambientModuleRingSheaf.obj
  rw [← open_embedding_pushforward_adjunction_counit_eq U ambientModuleRingSheaf]

/-- Helper for Lemma 6.31.8: package the explicit sheaf extension-by-zero owner as the canonical
left adjoint chosen for `moduleSheafRestrictionToOpen`. -/



public theorem probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_sheafUnit_eq_publicUnit :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
        (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom ≫
      (TopCat.Presheaf.pushforward RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).map
        (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U)).hom =
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
        (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf) := by
  let E := (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf))
  let P := TopCat.Presheaf.pushforward RingCat.{u} (extensionByZeroOpenSubsetInclusion U)
  let γ := P.map E
  apply (cancel_mono γ).mp
  have hright :
      ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf) ≫ γ =
        Functor.whiskerRight (NatTrans.op U.isOpenEmbedding.isOpenMap.adjunction.counit)
          ambientModuleRingSheaf.obj := by
    simpa [γ, E, P, ambientModuleRingSheaf] using
      (probe_openSubsetRing_publicUnit_comp_pullbackIso_hom (U := U))
  exact (probe_hleft (U := U)).trans hright.symm

public noncomputable abbrev probeSourceIso :
    ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf)) ≅
      (TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf.presheaf := by
  simpa [openSubspaceModuleRingSheaf] using
    (openSubspaceModuleRingSheafObjIsoConcretePullback (U := U))

public theorem probe_smul_congr_of_module_eq
    {R M : Type u} [Semiring R] [AddCommMonoid M]
    (inst₁ inst₂ : Module R M) (hmod : inst₁ = inst₂) (r : R) (m : M) :
    @SMul.smul R M inst₁.toSMul r m = @SMul.smul R M inst₂.toSMul r m := by
  cases hmod
  rfl

public theorem probe_cast_eq_of_proof_irrel_eq
    {α β : Sort u} (p q : α = β) (x : α) :
    cast p x = cast q x := by
  cases Subsingleton.elim p q
  rfl


public noncomputable def probeRestrictScalarsInvHomUnitApp
    (ℱ : PresheafOfModules
      ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf))) :
    ℱ ≅
      ((PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv ⋙
        PresheafOfModules.restrictScalars (probeSourceIso (U := U)).hom).obj ℱ) := by
  let σ := probeSourceIso (U := U)
  refine PresheafOfModules.isoMk (fun V => ?_) (fun {V W} i => ?_)
  · have hgf : RingHom.id _ =
        (σ.inv.app V).hom.comp (σ.hom.app V).hom := by
      ext r
      have hcancel : σ.hom.app V ≫ σ.inv.app V = 𝟙 _ := by
        simpa using congrArg (fun η => η.app V) σ.hom_inv_id
      have h := congrArg (fun k => (ConcreteCategory.hom k) r) hcancel
      change (ConcreteCategory.hom (σ.inv.app V))
        ((ConcreteCategory.hom (σ.hom.app V)) r) = r at h
      exact h.symm
    exact (ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (ℱ.obj V)).symm ≪≫
      ModuleCat.restrictScalarsComp'App (σ.hom.app V).hom (σ.inv.app V).hom
        (RingHom.id _) hgf (ℱ.obj V)
  · ext x
    rfl

public noncomputable def probeRestrictScalarsInvHomUnitIso :
    𝟭 (PresheafOfModules
      ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf))) ≅
      PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv ⋙
        PresheafOfModules.restrictScalars (probeSourceIso (U := U)).hom :=
  NatIso.ofComponents
    (fun ℱ => probeRestrictScalarsInvHomUnitApp (U := U) ℱ)
    (fun {ℱ 𝒢} η => by
      apply (PresheafOfModules.toPresheaf _).map_injective
      apply NatTrans.ext
      funext V
      rfl)

public noncomputable def probeRestrictScalarsHomInvCounitApp
    (ℱ : PresheafOfModules
      ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf.presheaf)) :
    ((PresheafOfModules.restrictScalars (probeSourceIso (U := U)).hom ⋙
        PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv).obj ℱ) ≅ ℱ := by
  let σ := probeSourceIso (U := U)
  refine PresheafOfModules.isoMk (fun V => ?_) (fun {V W} i => ?_)
  · have hgf : RingHom.id _ =
        (σ.hom.app V).hom.comp (σ.inv.app V).hom := by
      ext r
      have hcancel : σ.inv.app V ≫ σ.hom.app V = 𝟙 _ := by
        simpa using congrArg (fun η => η.app V) σ.inv_hom_id
      have h := congrArg (fun k => (ConcreteCategory.hom k) r) hcancel
      change (ConcreteCategory.hom (σ.hom.app V))
        ((ConcreteCategory.hom (σ.inv.app V)) r) = r at h
      exact h.symm
    exact (ModuleCat.restrictScalarsComp'App (σ.inv.app V).hom (σ.hom.app V).hom
        (RingHom.id _) hgf (ℱ.obj V)).symm ≪≫
      ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (ℱ.obj V)
  · ext x
    rfl

public noncomputable def probeRestrictScalarsHomInvCounitIso :
    PresheafOfModules.restrictScalars (probeSourceIso (U := U)).hom ⋙
        PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv ≅
      𝟭 (PresheafOfModules
        ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf.presheaf)) :=
  NatIso.ofComponents
    (fun ℱ => probeRestrictScalarsHomInvCounitApp (U := U) ℱ)
    (fun {ℱ 𝒢} η => by
      apply (PresheafOfModules.toPresheaf _).map_injective
      apply NatTrans.ext
      funext V
      rfl)


public noncomputable def probeRestrictScalarsAdjunction :
    PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv ⊣
      PresheafOfModules.restrictScalars (probeSourceIso (U := U)).hom := by
  refine Adjunction.mkOfUnitCounit
    { unit := (probeRestrictScalarsInvHomUnitIso (U := U)).hom
      counit := (probeRestrictScalarsHomInvCounitIso (U := U)).hom
      left_triangle := ?_
      right_triangle := ?_ }
  · apply NatTrans.ext
    funext ℱ
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply NatTrans.ext
    funext V
    rfl
  · apply NatTrans.ext
    funext ℱ
    apply (PresheafOfModules.toPresheaf _).map_injective
    apply NatTrans.ext
    funext V
    rfl

public noncomputable def probePullbackSigmaIso :
    PresheafOfModules.pullback (F := 𝟭 _) (probeSourceIso (U := U)).hom ≅
      PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv := by
  exact Adjunction.leftAdjointUniq
    (PresheafOfModules.pullbackPushforwardAdjunction (F := 𝟭 _) (probeSourceIso (U := U)).hom)
    (by
      simpa [PresheafOfModules.pushforward] using
        (probeRestrictScalarsAdjunction (U := U)))


public noncomputable def probeRestrictSourceChangeApp
    (ℱ : PresheafOfModules
      ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf))) :
    ((PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv ⋙
        openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf).obj ℱ) ≅
      (openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom).obj ℱ := by
  refine
    { hom := ?hom
      inv := ?inv
      hom_inv_id := ?hi
      inv_hom_id := ?ih }
  · refine PresheafOfModules.homMk (𝟙 _) ?_
    intro V r m
    by_cases hV : V.unop ≤ U
    · let αsheaf := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom
      let αpublic := ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf)
      let σ := probeSourceIso (U := U)
      have hunit := probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_sheafUnit_eq_publicUnit (U := U)
      let W := Opposite.op (openSubsetPreimageOpen U V.unop)
      have hunit_app_mor := congrArg (fun η => η.app V) hunit
      have hunit_app' :
          αsheaf.app V ≫ σ.hom.app W = αpublic.app V := by
        simpa [σ, αsheaf, αpublic, W, TopCat.Presheaf.pushforward_obj_obj,
          TopCat.Presheaf.pushforward_map_app, openSubsetPreimageOpen] using hunit_app_mor
      have hscalar_mor : αpublic.app V ≫ σ.inv.app W = αsheaf.app V := by
        have hcancel_mor : σ.hom.app W ≫ σ.inv.app W = 𝟙 _ := by
          simpa using congrArg (fun η => η.app W) σ.hom_inv_id
        rw [← hunit_app']
        calc
          (αsheaf.app V ≫ σ.hom.app W) ≫ σ.inv.app W =
              αsheaf.app V ≫ (σ.hom.app W ≫ σ.inv.app W) := by
            exact Category.assoc _ _ _
          _ = αsheaf.app V ≫ 𝟙 _ := by
            exact congrArg (fun k => αsheaf.app V ≫ k) hcancel_mor
          _ = αsheaf.app V := by simp
      change
        @SMul.smul _ _
          (openSubsetModuleExtensionByZeroObj_module U αpublic
            ((PresheafOfModules.restrictScalars σ.inv).obj ℱ) V).toSMul r m =
        @SMul.smul _ _
          (openSubsetModuleExtensionByZeroObj_module U αsheaf ℱ V).toSMul r m
      let hobj₁ := openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U
        ((PresheafOfModules.restrictScalars σ.inv).obj ℱ).presheaf hV
      let hobj₂ := openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV
      apply_fun (fun z => (eqToHom hobj₁) z) using by
        exact (CategoryTheory.Iso.addCommGroupIsoToAddEquiv (eqToIso hobj₁)).injective
      calc
          (eqToHom hobj₁)
              (@SMul.smul _ _
                (openSubsetModuleExtensionByZeroObj_module U αpublic
                  ((PresheafOfModules.restrictScalars σ.inv).obj ℱ) V).toSMul r m)
              = (show ℱ.obj W from
                  (show ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                    ambientModuleRingSheaf.presheaf).obj W from αpublic.app V r) •
                (eqToHom hobj₁ m)) := by
                  simpa using openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U
                    αpublic ((PresheafOfModules.restrictScalars σ.inv).obj ℱ) hV r m
          _ = (show ℱ.obj W from
                (show (((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
                    ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                      ambientModuleRingSheaf)).obj W) from αsheaf.app V r) •
                (eqToHom hobj₂ m)) := by
                  have hscalar_apply :
                      (σ.inv.app W) (αpublic.app V r) =
                        (show (((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
                    ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                      ambientModuleRingSheaf)).obj W) from αsheaf.app V r) := by
                    simpa using congrArg (fun k => (ConcreteCategory.hom k) r) hscalar_mor
                  have hm :
                      (show ℱ.obj W from (eqToHom hobj₁) m) =
                        (show ℱ.obj W from (eqToHom hobj₂) m) := by
                    rfl
                  change
                    (σ.inv.app W (αpublic.app V r)) •
                        (show ℱ.obj W from (eqToHom hobj₁) m) =
                      (show (((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
                    ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                      ambientModuleRingSheaf)).obj W) from αsheaf.app V r) •
                        (show ℱ.obj W from (eqToHom hobj₂) m)
                  rw [hscalar_apply, hm]
          _ = (show ℱ.obj W from (eqToHom hobj₂)
              (@SMul.smul _ _
                (openSubsetModuleExtensionByZeroObj_module U αsheaf ℱ V).toSMul r m)) := by
                  simpa using (openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U
                    αsheaf ℱ hV r m).symm
          _ = (show ℱ.obj W from (eqToHom hobj₁)
              (@SMul.smul _ _
                (openSubsetModuleExtensionByZeroObj_module U αsheaf ℱ V).toSMul r m)) := by
                  rfl
    · have hsub : Subsingleton (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) := by
        rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ.presheaf hV]
        infer_instance
      exact hsub.elim _ _
  · refine PresheafOfModules.homMk (𝟙 _) ?_
    intro V r m
    by_cases hV : V.unop ≤ U
    · let αsheaf := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom
      let αpublic := ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf)
      let σ := probeSourceIso (U := U)
      have hunit := probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_sheafUnit_eq_publicUnit (U := U)
      let W := Opposite.op (openSubsetPreimageOpen U V.unop)
      have hunit_app_mor := congrArg (fun η => η.app V) hunit
      have hunit_app' :
          αsheaf.app V ≫ σ.hom.app W = αpublic.app V := by
        simpa [σ, αsheaf, αpublic, W, TopCat.Presheaf.pushforward_obj_obj,
          TopCat.Presheaf.pushforward_map_app, openSubsetPreimageOpen] using hunit_app_mor
      have hscalar_mor : αpublic.app V ≫ σ.inv.app W = αsheaf.app V := by
        have hcancel_mor : σ.hom.app W ≫ σ.inv.app W = 𝟙 _ := by
          simpa using congrArg (fun η => η.app W) σ.hom_inv_id
        rw [← hunit_app']
        calc
          (αsheaf.app V ≫ σ.hom.app W) ≫ σ.inv.app W =
              αsheaf.app V ≫ (σ.hom.app W ≫ σ.inv.app W) := by
            exact Category.assoc _ _ _
          _ = αsheaf.app V ≫ 𝟙 _ := by
            exact congrArg (fun k => αsheaf.app V ≫ k) hcancel_mor
          _ = αsheaf.app V := by simp
      change
        @SMul.smul _ _
          (openSubsetModuleExtensionByZeroObj_module U αsheaf ℱ V).toSMul r m =
        @SMul.smul _ _
          (openSubsetModuleExtensionByZeroObj_module U αpublic
            ((PresheafOfModules.restrictScalars σ.inv).obj ℱ) V).toSMul r m
      let hobj₁ := openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U
        ((PresheafOfModules.restrictScalars σ.inv).obj ℱ).presheaf hV
      let hobj₂ := openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV
      apply_fun (fun z => (eqToHom hobj₁) z) using by
        exact (CategoryTheory.Iso.addCommGroupIsoToAddEquiv (eqToIso hobj₁)).injective
      calc
          (show ℱ.obj W from (eqToHom hobj₁)
              (@SMul.smul _ _
                (openSubsetModuleExtensionByZeroObj_module U αsheaf ℱ V).toSMul r m))
              = (show ℱ.obj W from (eqToHom hobj₂)
                  (@SMul.smul _ _
                    (openSubsetModuleExtensionByZeroObj_module U αsheaf ℱ V).toSMul r m)) := by
                    rfl
          _ = (show ℱ.obj W from
                (show (((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
                    ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                      ambientModuleRingSheaf)).obj W) from αsheaf.app V r) •
                (eqToHom hobj₂ m)) := by
                  exact openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U
                    αsheaf ℱ hV r m
          _ = (show ℱ.obj W from
                (show ((TopCat.Presheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                    ambientModuleRingSheaf.presheaf).obj W from αpublic.app V r) •
                (eqToHom hobj₁ m)) := by
                  have hscalar_apply :
                      (σ.inv.app W) (αpublic.app V r) =
                        (show (((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
                    ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                      ambientModuleRingSheaf)).obj W) from αsheaf.app V r) := by
                    simpa using congrArg (fun k => (ConcreteCategory.hom k) r) hscalar_mor
                  have hm :
                      (show ℱ.obj W from (eqToHom hobj₁) m) =
                        (show ℱ.obj W from (eqToHom hobj₂) m) := by
                    rfl
                  change
                    (show (((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
                    ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
                      ambientModuleRingSheaf)).obj W) from αsheaf.app V r) •
                        (show ℱ.obj W from (eqToHom hobj₂) m) =
                      (σ.inv.app W (αpublic.app V r)) •
                        (show ℱ.obj W from (eqToHom hobj₁) m)
                  rw [← hscalar_apply, ← hm]
          _ = (show ℱ.obj W from (eqToHom hobj₁)
              (@SMul.smul _ _
                (openSubsetModuleExtensionByZeroObj_module U αpublic
                  ((PresheafOfModules.restrictScalars σ.inv).obj ℱ) V).toSMul r m)) := by
                  symm
                  exact openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U
                    αpublic ((PresheafOfModules.restrictScalars σ.inv).obj ℱ) hV r m
    · have hsub : Subsingleton (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) := by
        rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ.presheaf hV]
        infer_instance
      exact hsub.elim _ _
  · apply (PresheafOfModules.toPresheaf _).map_injective
    apply NatTrans.ext
    funext V
    rfl
  · apply (PresheafOfModules.toPresheaf _).map_injective
    apply NatTrans.ext
    funext V
    rfl


public noncomputable def probeRestrictSourceChangeIso :
    PresheafOfModules.restrictScalars (probeSourceIso (U := U)).inv ⋙
        openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf ≅
      openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom :=
  NatIso.ofComponents
    (fun ℱ => probeRestrictSourceChangeApp (U := U) ℱ)
    (fun {ℱ 𝒢} η => by
      apply (PresheafOfModules.toPresheaf _).map_injective
      apply NatTrans.ext
      funext V
      rfl)


public noncomputable def probePresheafPullbackSheafUnitIso :
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    PresheafOfModules.pullback
        (((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom)) ≅
      openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let σ := probeSourceIso (U := U)
  let E := (((U.isOpenEmbedding.isOpenMap.pullbackIso :
            TopCat.Presheaf.pullback RingCat.{u} U.inclusion' ≅ _).hom.app
          ambientModuleRingSheaf.presheaf))
  have hβ := probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_comp_pullbackIso_hom (U := U)
  change PresheafOfModules.pullback
        (((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom)) ≅
      openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom
  rw [hβ]
  refine ?_ ≪≫ probeRestrictSourceChangeIso (U := U)
  refine ?_ ≪≫ CategoryTheory.Functor.isoWhiskerRight
    (probePullbackSigmaIso (U := U))
    (openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf) ≪≫ ?_
  · refine (PresheafOfModules.pullbackComp (F := 𝟭 _) σ.hom E).symm ≪≫ ?_
    exact CategoryTheory.Functor.isoWhiskerLeft
      (PresheafOfModules.pullback (F := 𝟭 _) σ.hom)
      (openSubsetModulePresheafExtensionByZeroIsoPullbackLeft (U := U))
  · exact Iso.refl _

public noncomputable def probeCanonicalToOpenEmbeddingPullback :
    moduleSheafExtensionByZeroFromOpen U ambientModuleRingSheaf ≅
      (letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
       SheafOfModules.pullback.{u} (F := U.isOpenEmbedding.functor)
         (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact Adjunction.leftAdjointUniq
    (moduleSheafExtensionByZeroAdjunction U ambientModuleRingSheaf)
    ((SheafOfModules.pullbackPushforwardAdjunction
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)).ofNatIsoRight
        (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U ambientModuleRingSheaf))


public noncomputable def probeOpenEmbeddingPullbackToExplicit :
    (letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
     SheafOfModules.pullback.{u} (F := U.isOpenEmbedding.functor)
       (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)) ≅
      openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let β := (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)
  let S := ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf)
  refine (SheafOfModules.pullbackIso β) ≪≫ ?_
  exact CategoryTheory.Functor.isoWhiskerRight
    (CategoryTheory.Functor.isoWhiskerLeft (SheafOfModules.forget S)
      (probePresheafPullbackSheafUnitIso (U := U)))
    (PresheafOfModules.sheafification (R := ambientModuleRingSheaf)
      (R₀ := ambientModuleRingSheaf.obj) (α := 𝟙 ambientModuleRingSheaf.obj))

/-- Helper for Lemma 6.31.8: package the explicit sheaf extension-by-zero owner as the canonical
left adjoint chosen for `moduleSheafRestrictionToOpen`. -/
public noncomputable def openSubsetModuleSheafExtensionByZeroIsoCanonical :
    moduleSheafExtensionByZeroFromOpen U ambientModuleRingSheaf ≅
      openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf :=
  probeCanonicalToOpenEmbeddingPullback (U := U) ≪≫
    probeOpenEmbeddingPullbackToExplicit (U := U)


/-- Lemma 6.31.8 (2): the explicit extension-by-zero functor on sheaves of modules is left
adjoint to restriction to the open subset `U`. -/
noncomputable abbrev openSubsetModuleSheafExtensionByZeroAdjunction :
    openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X) ⊣
      moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X) := by
  -- The source-facing sheaf functor is the imported canonical left adjoint after unfolding the
  -- chosen owner on the left-adjoint side.
  simpa using
    (moduleSheafExtensionByZeroAdjunction U (RingedSpace.ringCatSheaf X)).ofNatIsoLeft
      (openSubsetModuleSheafExtensionByZeroIsoCanonical (X := X) U)

-- Proof sketch: extract the left-adjoint structure carried by the explicit sheaf adjunction.
/-- The sheaf extension-by-zero functor inherits its left-adjoint structure from the canonical
adjunction. -/
theorem openSubsetModuleSheafExtensionByZeroAdjunction_isLeftAdjoint :
    (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).IsLeftAdjoint := by
  -- The sheaf adjunction above immediately packages the left-adjoint structure.
  exact (openSubsetModuleSheafExtensionByZeroAdjunction U).isLeftAdjoint

/-- The canonical extension-by-zero functor on sheaves of modules is a left adjoint. -/
instance :
    (openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).IsLeftAdjoint :=
  openSubsetModuleSheafExtensionByZeroAdjunction_isLeftAdjoint U

-- Proof sketch: as on the counit side in `Lemma_6_31_12`, forgetting the module structure to the
-- underlying additive sheaf preserves isomorphisms and reflects them back to module sheaves.
public noncomputable def probeSourceSheafificationCounitIso :
    SheafOfModules.forget (openSubspaceModuleRingSheaf U) ⋙
      PresheafOfModules.sheafification (R := openSubspaceModuleRingSheaf U)
        (R₀ := (openSubspaceModuleRingSheaf U).obj)
        (α := 𝟙 (openSubspaceModuleRingSheaf U).obj) ≅
      𝟭 (SheafOfModules (openSubspaceModuleRingSheaf U)) := by
  simpa using
    (asIso (PresheafOfModules.sheafificationAdjunction
      (α := 𝟙 (openSubspaceModuleRingSheaf U).obj)).counit)

public noncomputable def probeSheafUnitPresheafPullbackIsoPublic :
    PresheafOfModules.pullback
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom ≅
      PresheafOfModules.pullback
          ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
            (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf) ⋙
        PresheafOfModules.restrictScalars (probeSourceIso (U := U)).hom := by
  let σ := probeSourceIso (U := U)
  let αsheaf := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom
  let αpublic := ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
    (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf)
  let Praw := PresheafOfModules.pullback αsheaf
  let Rσinv := PresheafOfModules.restrictScalars σ.inv
  let Rσhom := PresheafOfModules.restrictScalars σ.hom
  let σhom :
      ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
        ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
          ambientModuleRingSheaf)) ⟶
        (𝟭 (Opens (extensionByZeroOpenSubsetSpace U))).op ⋙
          ((TopCat.Presheaf.pullback RingCat.{u}
            (extensionByZeroOpenSubsetInclusion U)).obj ambientModuleRingSheaf.presheaf) := by
    simpa using σ.hom
  have hcomp :
      αsheaf ≫ Functor.whiskerLeft
          (Opens.map (extensionByZeroOpenSubsetInclusion U)).op σhom =
        αpublic := by
    simpa [σhom, σ, αsheaf, αpublic, TopCat.Presheaf.pushforward] using
      (probe_openSubspaceModuleRingSheafObjIsoConcretePullback_hom_sheafUnit_eq_publicUnit
        (U := U))
  let compIso :
      Praw ⋙ PresheafOfModules.pullback (F := 𝟭 _) σhom ≅
        PresheafOfModules.pullback αpublic :=
    (PresheafOfModules.pullbackComp αsheaf σhom) ≪≫
      eqToIso (congrArg (fun η => PresheafOfModules.pullback η) hcomp)
  let pullbackSigmaIso :
      PresheafOfModules.pullback (F := 𝟭 _) σhom ≅ Rσinv := by
    simpa [σhom, Rσinv, σ] using (probePullbackSigmaIso (U := U))
  let rawInvIso : Praw ⋙ Rσinv ≅ PresheafOfModules.pullback αpublic :=
    (CategoryTheory.Functor.isoWhiskerLeft Praw pullbackSigmaIso.symm) ≪≫ compIso
  simpa [Praw, Rσinv, Rσhom, σ, αsheaf, αpublic] using
    (CategoryTheory.Functor.rightUnitor Praw).symm ≪≫
      CategoryTheory.Functor.isoWhiskerLeft Praw (probeRestrictScalarsInvHomUnitIso (U := U)) ≪≫
      CategoryTheory.Functor.isoWhiskerRight rawInvIso Rσhom

public noncomputable def probeRawPresheafExtensionRestrictionCompIso :
    openSubsetModuleExtensionByZero U
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom ⋙
      PresheafOfModules.pullback
        ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom ≅
      𝟭 (PresheafOfModules
        ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).obj
          ((TopCat.Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            ambientModuleRingSheaf))) := by
  let σ := probeSourceIso (U := U)
  let αsheaf := ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
    (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom
  let Eraw := openSubsetModuleExtensionByZero U αsheaf
  let Praw := PresheafOfModules.pullback αsheaf
  let Epublic := openSubsetModulePresheafExtensionByZero U ambientModuleRingSheaf.presheaf
  let Ppublic := PresheafOfModules.pullback
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u}
      (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf.presheaf)
  let Rσinv := PresheafOfModules.restrictScalars σ.inv
  let Rσhom := PresheafOfModules.restrictScalars σ.hom
  let eSource : Rσinv ⋙ Epublic ≅ Eraw := by
    simpa [Rσinv, Epublic, Eraw, σ, αsheaf] using
      (probeRestrictSourceChangeIso (U := U))
  let eRestrict : Praw ≅ Ppublic ⋙ Rσhom := by
    simpa [Praw, Ppublic, Rσhom, σ, αsheaf] using
      (probeSheafUnitPresheafPullbackIsoPublic (U := U))
  let eCollapse :=
    CategoryTheory.Functor.isoWhiskerLeft Rσinv
      (CategoryTheory.Functor.isoWhiskerRight
        (probe_presheafExtensionPublicPullbackCompIso (U := U)) Rσhom)
  simpa [Eraw, Praw, Epublic, Ppublic, Rσinv, Rσhom, σ, αsheaf] using
    (CategoryTheory.Functor.isoWhiskerRight eSource.symm Praw) ≪≫
      (CategoryTheory.Functor.isoWhiskerLeft (Rσinv ⋙ Epublic) eRestrict) ≪≫
      eCollapse ≪≫
      (probeRestrictScalarsInvHomUnitIso (U := U)).symm

public noncomputable def probeSheafExtensionRestrictionCompIso :
    openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf ⋙
      moduleSheafRestrictionToOpen U ambientModuleRingSheaf ≅
      𝟭 (SheafOfModules (openSubspaceModuleRingSheaf U)) := by
  let φ :=
    ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
      (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf)
  let Eraw := openSubsetModuleExtensionByZero U φ.hom
  let ShU := PresheafOfModules.sheafification (R := openSubspaceModuleRingSheaf U)
    (R₀ := (openSubspaceModuleRingSheaf U).obj)
    (α := 𝟙 (openSubspaceModuleRingSheaf U).obj)
  let e₁ :=
    CategoryTheory.Functor.isoWhiskerLeft
      (SheafOfModules.forget (openSubspaceModuleRingSheaf U) ⋙ Eraw)
      (SheafOfModules.sheafificationCompPullback (φ := φ))
  let e₂ :=
    CategoryTheory.Functor.isoWhiskerLeft
      (SheafOfModules.forget (openSubspaceModuleRingSheaf U))
      (CategoryTheory.Functor.isoWhiskerRight
        (probeRawPresheafExtensionRestrictionCompIso (U := U)) ShU)
  simpa [openSubsetModuleSheafExtensionByZero, moduleSheafRestrictionToOpen, φ, Eraw, ShU,
    ambientModuleRingSheaf, openSubspaceModuleRingSheaf] using
      e₁ ≪≫ e₂ ≪≫ probeSourceSheafificationCounitIso (U := U)

/-- Helper for Lemma 6.31.8: the module-valued unit component is an isomorphism exactly when its
image under `SheafOfModules.toSheaf` is an isomorphism. -/
public theorem openSubspaceModuleSheafExtensionByZero_unit_isIso_iff_toSheaf_map
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    IsIso ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ) ↔
      IsIso
        ((SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U)).map
          ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ)) := by
  constructor
  · intro hUnit
    letI := hUnit
    -- Any functor preserves the invertibility of the unit component once the module map is known
    -- to be an isomorphism.
    simpa using
      (Functor.map_isIso
        (SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U))
        ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ))
  · intro hUnit
    letI := hUnit
    -- Conversely, `toSheaf` reflects isomorphisms because it is faithful and its composition with
    -- the additive-sheaf forgetful functor is the underlying additive-presheaf forgetful functor.
    exact isIso_of_reflects_iso
      ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ)
      (SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U))

-- Proof sketch: on the open subspace `U`, the unit of the sheaf-level adjunction restricts to the
-- identity on sections, so every unit component is an isomorphism.
public instance openSubspaceModuleSheafExtensionByZero_unit_app_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    IsIso ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ) := by
  let _ := (openSubsetModuleSheafExtensionByZeroAdjunction U).isIso_unit_of_iso
    (probeSheafExtensionRestrictionCompIso (U := U))
  infer_instance

/-- On sheaves of modules over `U`, the unit map
`\mathrm{id} \to j^{-1} j_!` is a natural isomorphism. -/
noncomputable abbrev openSubspaceModuleSheafExtensionByZero_unitIso :
    𝟭 (SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X))) ≅
      openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X) ⋙
        moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X) :=
  NatIso.ofComponents
    (fun ℱ ↦ asIso ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ))
    (fun φ ↦ by
      simpa using
        (openSubsetModuleSheafExtensionByZeroAdjunction U).unit.naturality φ)

-- Proof sketch: `openSubspaceModuleSheafExtensionByZero_unitIso` is assembled from the adjunction
-- unit by `NatIso.ofComponents`, so its hom component is exactly the unit morphism.
/-- The hom component of the unit isomorphism is the unit morphism of the sheaf adjunction. -/
theorem openSubspaceModuleSheafExtensionByZero_unitIso_hom_app
    (ℱ : SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X))) :
    (openSubspaceModuleSheafExtensionByZero_unitIso U).hom.app ℱ =
      (openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ := by
  -- `NatIso.ofComponents` stores the adjunction unit as its hom component.
  rfl

/-- Helper for Lemma 6.31.8: outside `U`, the additive stalk underlying `j_! ℱ` is initial. -/
public noncomputable def openSubspaceModuleSheafExtensionByZero_stalk_isInitial_of_not_mem
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U))
    {x : X.carrier} (hx : x ∉ (U : Set X.carrier)) :
    IsInitial
      (Presheaf.stalk
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
        x) := by
  -- Reuse the generic additive extension-by-initial-object stalk computation on the underlying
  -- sheaf of abelian groups.
  simpa using
    (OpenSubsetExtensionByInitial.sheafExtensionByInitial_stalk_isInitial_of_not_mem
      (C := AddCommGrpCat.{u}) U
      ((SheafOfModules.toSheaf (openSubspaceModuleRingSheaf U)).obj ℱ) hx)

/-- Lemma 6.31.8 (3), outside `U`: the module-valued stalk of `j_! ℱ` vanishes. -/
theorem openSubspaceModuleSheafExtensionByZero_stalk_isZero_of_not_mem
    (ℱ : SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X)))
    {x : X} (hx : x ∉ (U : Set X.carrier)) :
    IsZero (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
      ↑(Presheaf.stalk
        ((openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj ℱ).val.presheaf
        x)) := by
  -- First show that the underlying additive-group stalk is initial, hence has a subsingleton
  -- carrier; then package that carrier as a zero module over the ambient stalk ring.
  let hInitial :
      IsInitial
        (Presheaf.stalk
          ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
          x) :=
    openSubspaceModuleSheafExtensionByZero_stalk_isInitial_of_not_mem (U := U) ℱ hx
  let hZero :
      IsZero
        (Presheaf.stalk
          ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
          x) :=
    hInitial.isZero
  letI :
      Subsingleton
        (↑(Presheaf.stalk
          ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
          x)) :=
    AddCommGrpCat.subsingleton_of_isZero hZero
  simpa [ambientModuleRingSheaf] using
    (ModuleCat.isZero_of_subsingleton
      (ModuleCat.of ((RingedSpace.ringCatSheaf X).presheaf.stalk x)
        ↑(Presheaf.stalk
          ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
          x)))

public abbrev openSubspaceModuleSheafExtensionByZeroRestricted
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    SheafOfModules (openSubspaceModuleRingSheaf U) :=
  (moduleSheafRestrictionToOpen U ambientModuleRingSheaf).obj
    ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)

public abbrev openSubspaceModuleSheafExtensionByZeroUnitPresheafMap
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    ℱ.val ⟶ (openSubspaceModuleSheafExtensionByZeroRestricted U ℱ).val :=
  ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ).val

public abbrev openSubspaceModuleSheafExtensionByZeroUnitStalkMap
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    Presheaf.stalk ℱ.val.presheaf x ⟶
      Presheaf.stalk (openSubspaceModuleSheafExtensionByZeroRestricted U ℱ).val.presheaf x := by
  simpa using
    (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((PresheafOfModules.toPresheaf _).map
        (openSubspaceModuleSheafExtensionByZeroUnitPresheafMap U ℱ))

/-- Helper for Lemma 6.31.8: the stalk map induced by a morphism of module presheaves, after
forgetting to additive presheaves. -/
public noncomputable abbrev openSubspaceModuleExtensionByZeroStalkUnderlyingMap
    {Y : TopCat.{u}} {R : Y.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj}
    (x : Y) (φ : ℱ ⟶ 𝒢) :
    Presheaf.stalk ℱ.presheaf x ⟶ Presheaf.stalk 𝒢.presheaf x :=
  (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((PresheafOfModules.toPresheaf R.obj).map φ)

/-- Helper for Lemma 6.31.8: the stalk map induced by a morphism of module presheaves over a
fixed ring sheaf is linear over the stalk ring. -/
public theorem openSubspaceModuleExtensionByZeroStalkUnderlyingMap_smul
    {Y : TopCat.{u}} {R : Y.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj}
    (x : Y) (φ : ℱ ⟶ 𝒢) :
    ∀ (r : R.presheaf.stalk x) (m : ↑(Presheaf.stalk ℱ.presheaf x)),
      openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ (r • m) = r • openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ m := by
  -- Compare both stalk elements on a common neighborhood representative for the scalar and
  -- the section, then use sectionwise linearity of `φ`.
  intro r m
  obtain ⟨U, hxU, rU, hr⟩ := TopCat.Presheaf.germ_exist R.presheaf x r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist ℱ.presheaf x m
  let W : Opens Y := U ⊓ V
  let iWU : W ⟶ U := homOfLE inf_le_left
  let iWV : W ⟶ V := homOfLE inf_le_right
  have hxW : x ∈ W := ⟨hxU, hxV⟩
  let rW : R.presheaf.obj (Opposite.op W) := R.presheaf.map iWU.op rU
  let mW : ℱ.presheaf.obj (Opposite.op W) := ℱ.presheaf.map iWV.op mV
  have hrW : R.presheaf.germ W x hxW rW = r := by
    simpa [W, iWU, hxW, rW] using (R.presheaf.germ_res_apply iWU x hxW rU).trans hr
  have hmW : TopCat.Presheaf.germ ℱ.presheaf W x hxW mW = m := by
    simpa [W, iWV, hxW, mW] using
      (TopCat.Presheaf.germ_res_apply ℱ.presheaf iWV x hxW mV).trans hm
  have hsmulW :
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) = r • m := by
    calc
      TopCat.Presheaf.germ ℱ.presheaf W x hxW (rW • mW) =
          R.presheaf.germ W x hxW rW • TopCat.Presheaf.germ ℱ.presheaf W x hxW mW := by
            simpa using
              (PresheafOfModules.germ_ringCat_smul (R := R.obj) (M := ℱ) x W hxW rW mW)
      _ = r • m := by rw [hrW, hmW]
  have hmφW :
      (show ↑(Presheaf.stalk 𝒢.presheaf x) from
        ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          ((PresheafOfModules.toPresheaf R.obj).map φ)) m) =
        TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) mW) := by
    rw [← hmW]
    simpa [W, hxW, mW] using
      (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
        ((PresheafOfModules.toPresheaf R.obj).map φ) mW)
  calc
    openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ (r • m)
        =
          TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) (rW • mW)) := by
            rw [← hsmulW]
            simpa [W, hxW, rW, mW] using
              (TopCat.Presheaf.stalkFunctor_map_germ_apply W x hxW
                ((PresheafOfModules.toPresheaf R.obj).map φ) (rW • mW))
    _ = TopCat.Presheaf.germ 𝒢.presheaf W x hxW (rW • φ.app (Opposite.op W) mW) := by
          congr 1
          exact (φ.app (Opposite.op W)).hom.map_smul rW mW
    _ = R.presheaf.germ W x hxW rW •
          TopCat.Presheaf.germ 𝒢.presheaf W x hxW (φ.app (Opposite.op W) mW) := by
          simpa using
            (PresheafOfModules.germ_ringCat_smul (R := R.obj) (M := 𝒢) x W hxW rW
              (φ.app (Opposite.op W) mW))
    _ = r • openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ m := by
          rw [hrW]
          simpa [openSubspaceModuleExtensionByZeroStalkUnderlyingMap] using (congrArg (fun z ↦ r • z) hmφW).symm

/-- Helper for Lemma 6.31.8: package the stalk map of a morphism of module presheaves as a
module homomorphism over the stalk ring. -/
public noncomputable def openSubspaceModuleExtensionByZeroStalkModuleMap
    {Y : TopCat.{u}} {R : Y.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj}
    (x : Y) (φ : ℱ ⟶ 𝒢) :
    ModuleCat.of (R.presheaf.stalk x) ↑(Presheaf.stalk ℱ.presheaf x) ⟶
      ModuleCat.of (R.presheaf.stalk x) ↑(Presheaf.stalk 𝒢.presheaf x) :=
  ModuleCat.ofHom
    { toFun := openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ
      map_add' := by
        intro m n
        exact (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ).hom.map_add m n
      map_smul' := openSubspaceModuleExtensionByZeroStalkUnderlyingMap_smul x φ }

/-- Helper for Lemma 6.31.8: if the underlying additive stalk map is an isomorphism, then the
corresponding packaged module-valued stalk map is also an isomorphism. -/
public theorem openSubspaceModuleExtensionByZeroStalkModuleMap_isIso
    {Y : TopCat.{u}} {R : Y.Sheaf RingCat.{u}} {ℱ 𝒢 : PresheafOfModules R.obj}
    (x : Y) (φ : ℱ ⟶ 𝒢) [IsIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ)] :
    IsIso (openSubspaceModuleExtensionByZeroStalkModuleMap x φ) := by
  let F := forget₂ (ModuleCat (R.presheaf.stalk x)) AddCommGrpCat
  haveI : IsIso (F.map (openSubspaceModuleExtensionByZeroStalkModuleMap x φ)) := by
    change IsIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ)
    infer_instance
  exact isIso_of_reflects_iso (openSubspaceModuleExtensionByZeroStalkModuleMap x φ) F

public instance openSubspaceModuleSheafExtensionByZeroUnitStalkMap_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    IsIso (openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x) := by
  -- Once the unit component is an isomorphism, both forgetting to abelian presheaves and taking
  -- the stalk preserve that isomorphism.
  let η := ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ).val
  have hη : IsIso η := by
    simpa [η] using
      (Functor.map_isIso (SheafOfModules.forget (openSubspaceModuleRingSheaf U))
        ((openSubsetModuleSheafExtensionByZeroAdjunction U).unit.app ℱ))
  have hPresheaf : IsIso ((PresheafOfModules.toPresheaf _).map η) := by
    simpa using (Functor.map_isIso (PresheafOfModules.toPresheaf _) η)
  simpa [openSubspaceModuleSheafExtensionByZeroUnitStalkMap,
    openSubspaceModuleSheafExtensionByZeroUnitPresheafMap, η] using
    (Functor.map_isIso (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x)
      ((PresheafOfModules.toPresheaf _).map η))

public theorem openSubspaceModuleSheafExtensionByZeroUnitStalkMap_smul
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (r : ↑((openSubspaceModuleRingSheaf U).presheaf.stalk x))
    (m : ↑(Presheaf.stalk ℱ.val.presheaf x)) :
    openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x (r • m) =
      r • openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x m := by
  -- This is the generic stalk-linearity statement specialized to the unit presheaf map.
  simpa [openSubspaceModuleSheafExtensionByZeroUnitStalkMap,
    openSubspaceModuleSheafExtensionByZeroUnitPresheafMap] using
    (openSubspaceModuleExtensionByZeroStalkUnderlyingMap_smul x
      (openSubspaceModuleSheafExtensionByZeroUnitPresheafMap U ℱ) r m)

public abbrev openSubspaceModuleSheafStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk ℱ.val.presheaf x)

public abbrev openSubspaceModuleSheafExtensionByZeroRestrictedStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk (openSubspaceModuleSheafExtensionByZeroRestricted U ℱ).val.presheaf x)

public def openSubspaceModuleSheafExtensionByZeroUnitStalkHom
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafStalk U ℱ x ⟶
      openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x :=
  ModuleCat.homMk
    (openSubspaceModuleSheafExtensionByZeroUnitStalkMap U ℱ x)
    (fun r ↦ by
      ext m
      exact (openSubspaceModuleSheafExtensionByZeroUnitStalkMap_smul U ℱ x r m).symm)

public instance openSubspaceModuleSheafExtensionByZeroUnitStalkHom_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    IsIso (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x) := by
  let F :=
    forget₂ (ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x)) AddCommGrpCat
  have : IsIso (F.map (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x)) := by
    simpa [F, openSubspaceModuleSheafExtensionByZeroUnitStalkHom] using
      (openSubspaceModuleSheafExtensionByZeroUnitStalkMap_isIso U ℱ x)
  exact isIso_of_reflects_iso (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x) F

public noncomputable abbrev openSubspaceModuleSheafExtensionByZero_restrictedStalkIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U))
    (x : U) :
    ModuleCat.of
        (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X)).presheaf.stalk x)
        ↑(Presheaf.stalk
          ((moduleSheafRestrictionToOpen U (RingedSpace.ringCatSheaf X)).obj
            ((openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj ℱ)).val.presheaf
          x) ≅
      ModuleCat.of
        (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X)).presheaf.stalk x)
        ↑(Presheaf.stalk ℱ.val.presheaf x) := by
  simpa [ambientModuleRingSheaf, openSubspaceModuleRingSheaf,
    openSubspaceModuleSheafExtensionByZeroRestricted, openSubspaceModuleSheafStalk,
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk] using
    (asIso (openSubspaceModuleSheafExtensionByZeroUnitStalkHom U ℱ x)).symm

public abbrev openSubspaceModuleSheafExtensionByZeroAmbientStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  let M :
      ModuleCat (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x)) :=
    ModuleCat.of
      (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x))
      ↑(Presheaf.stalk
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
        (extensionByZeroOpenSubsetInclusion U x))
  (ModuleCat.restrictScalars
      (((TopCat.Sheaf.stalkPullbackIso
          (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).symm).hom.hom)).obj M

/-- Helper for Lemma 6.31.8: after forgetting module structure, the stalk of the ambient
extension-by-zero sheaf at `j(x)` identifies with the stalk of its pullback to the open subspace
at `x`. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroUnderlyingStalkPullbackIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    let G : TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
      (SheafOfModules.toSheaf ambientModuleRingSheaf).obj
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)
    G.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x) ≅
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        G).presheaf.stalk x := by
  -- This is exactly the sheaf-level stalk pullback owner for the underlying additive sheaf.
  dsimp
  exact TopCat.Sheaf.stalkPullbackIso
    (extensionByZeroOpenSubsetInclusion U)
    ((SheafOfModules.toSheaf ambientModuleRingSheaf).obj
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)) x

/-- Helper for Lemma 6.31.8: transport the ambient stalk module structure across the underlying
additive stalk pullback isomorphism, so the pulled-back additive stalk carries the same
`\mathcal{O}_{U, x}`-module structure as the ambient stalk viewed by restriction of scalars. -/
public noncomputable abbrev openSubspaceModuleSheafExtensionByZeroPullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  let e := openSubspaceModuleSheafExtensionByZeroUnderlyingStalkPullbackIso (U := U) ℱ x
  let G : TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
    (SheafOfModules.toSheaf ambientModuleRingSheaf).obj
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)
  let M := openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x
  let eAdd :
      ↑(((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj G).presheaf.stalk
          x) ≃+
        ↑M :=
    e.symm.addCommGroupIsoToAddEquiv
  letI :
      Module ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
        ↑(((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj G).presheaf.stalk
          x) :=
    eAdd.module ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj G).presheaf.stalk x)

/-- Helper for Lemma 6.31.8: once the pulled-back stalk is given the transported module
structure, the underlying additive stalk pullback isomorphism becomes an isomorphism of
`\mathcal{O}_{U, x}`-modules. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroPullbackStalkIsoAmbient
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroPullbackStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x := by
  -- Route correction: isolate the linearity of the stalk pullback owner first, so the remaining
  -- blocker is only the comparison between the abstract restricted stalk and this explicit
  -- transported pullback-stalk module.
  let e := openSubspaceModuleSheafExtensionByZeroUnderlyingStalkPullbackIso (U := U) ℱ x
  let G : TopCat.Sheaf AddCommGrpCat.{u} X.carrier :=
    (SheafOfModules.toSheaf ambientModuleRingSheaf).obj
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)
  let M := openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x
  let eAdd :
      ↑(((TopCat.Sheaf.pullback AddCommGrpCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj G).presheaf.stalk
          x) ≃+
        ↑M :=
    e.symm.addCommGroupIsoToAddEquiv
  simpa [openSubspaceModuleSheafExtensionByZeroPullbackStalk,
    openSubspaceModuleSheafExtensionByZeroAmbientStalk] using
    (eAdd.linearEquiv ((openSubspaceModuleRingSheaf U).presheaf.stalk x)).toModuleIso

/-- Helper for Lemma 6.31.8: the sheafified module-pullback owner appearing in
`SheafOfModules.pullbackIso`, evaluated at the explicit extension-by-zero sheaf and then taken at
the stalk `x`. -/
public abbrev openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk
      (((PresheafOfModules.sheafification (𝟙 (openSubspaceModuleRingSheaf U).obj)).obj
          ((PresheafOfModules.pullback
            ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
                (extensionByZeroOpenSubsetInclusion U)).unit.app
              ambientModuleRingSheaf).hom).obj
            ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val)).val.presheaf)
        x)

/-- Helper for Lemma 6.31.8: the raw module-pullback presheaf owner underlying restriction, taken
at the stalk `x`. -/
public abbrev openSubspaceModuleSheafExtensionByZeroModulePullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  let P :=
    ((PresheafOfModules.pullback
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app
        ambientModuleRingSheaf).hom).obj
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val)
  let φ :=
    (PresheafOfModules.sheafificationAdjunction
      (α := 𝟙 (openSubspaceModuleRingSheaf U).obj)).unit.app P
  let e :
      Presheaf.stalk P.presheaf x ≅
        Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (openSubspaceModuleRingSheaf U).obj)).obj
              P).val.presheaf) x := by
    let hφ : IsIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ) := by
      change IsIso
        ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (CategoryTheory.toSheafify
            (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
            P.presheaf))
      simpa [openSubspaceModuleExtensionByZeroStalkUnderlyingMap, φ] using
        (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
          P.presheaf)
    simpa [φ] using (asIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ))
  let M := openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk U ℱ x
  let eAdd : ↑(Presheaf.stalk P.presheaf x) ≃+ ↑M := e.addCommGroupIsoToAddEquiv
  letI : Module ((openSubspaceModuleRingSheaf U).presheaf.stalk x) ↑(Presheaf.stalk P.presheaf x) :=
    eAdd.module ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x) ↑(Presheaf.stalk P.presheaf x)

/-- Helper for Lemma 6.31.8: `SheafOfModules.pullbackIso` identifies the restricted stalk of the
explicit extension-by-zero sheaf with the stalk of the sheafified module-pullback owner. -/
public noncomputable def
    openSubspaceModuleSheafExtensionByZeroRestrictedStalkHomToSheafifiedPullback
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x ⟶
      openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk U ℱ x := by
  -- First pass the restricted sheaf through the owner comparison `SheafOfModules.pullbackIso`,
  -- then package the induced stalk map as a module homomorphism.
  simpa [moduleSheafRestrictionToOpen, openSubspaceModuleSheafExtensionByZeroRestricted,
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk,
    openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk] using
    openSubspaceModuleExtensionByZeroStalkModuleMap x (((SheafOfModules.pullbackIso
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app
        ambientModuleRingSheaf)).app
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)).hom.val)

/-- Helper for Lemma 6.31.8: the stalk map induced by the `SheafOfModules.pullbackIso`
comparison is an isomorphism. -/
public instance openSubspaceModuleSheafExtensionByZeroRestrictedStalkHomToSheafifiedPullback_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    IsIso (openSubspaceModuleSheafExtensionByZeroRestrictedStalkHomToSheafifiedPullback U ℱ x) := by
  let e :=
    ((SheafOfModules.pullbackIso
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app
        ambientModuleRingSheaf)).app
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ))
  let φ :=
    e.hom.val
  haveI : IsIso e.hom := by
    infer_instance
  haveI : IsIso φ := by
    simpa [φ] using (Functor.map_isIso (SheafOfModules.forget _) e.hom)
  have hφ : IsIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ) := by
    simpa [openSubspaceModuleExtensionByZeroStalkUnderlyingMap, φ] using
      (Functor.map_isIso (Presheaf.stalkFunctor AddCommGrpCat.{u} x)
        ((PresheafOfModules.toPresheaf _).map φ))
  simpa [openSubspaceModuleSheafExtensionByZeroRestrictedStalkHomToSheafifiedPullback, φ,
    moduleSheafRestrictionToOpen, openSubspaceModuleSheafExtensionByZeroRestricted,
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk,
    openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk] using
    (openSubspaceModuleExtensionByZeroStalkModuleMap_isIso x φ)

/-- Helper for Lemma 6.31.8: after transporting the module structure along the sheafification-unit
stalk isomorphism, the raw module-pullback presheaf stalk identifies with the sheafified
module-pullback stalk. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoSheafifiedPullback
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk U ℱ x :=
  -- Package the already constructed restricted-to-sheafified stalk hom as an isomorphism so the
  -- later stalk comparisons can compose at the `Iso` level instead of repeatedly unpacking `asIso`.
  asIso (openSubspaceModuleSheafExtensionByZeroRestrictedStalkHomToSheafifiedPullback U ℱ x)

/-- Helper for Lemma 6.31.8: after transporting the module structure along the sheafification-unit
stalk isomorphism, the raw module-pullback presheaf stalk identifies with the sheafified
module-pullback stalk. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoSheafifiedPullback
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroModulePullbackStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk U ℱ x := by
  let P :=
    ((PresheafOfModules.pullback
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
          (extensionByZeroOpenSubsetInclusion U)).unit.app
        ambientModuleRingSheaf).hom).obj
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val)
  let φ :=
    (PresheafOfModules.sheafificationAdjunction
      (α := 𝟙 (openSubspaceModuleRingSheaf U).obj)).unit.app P
  let e :
      Presheaf.stalk P.presheaf x ≅
        Presheaf.stalk
          (((PresheafOfModules.sheafification (𝟙 (openSubspaceModuleRingSheaf U).obj)).obj
              P).val.presheaf) x := by
    let hφ : IsIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ) := by
      change IsIso
        ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (CategoryTheory.toSheafify
            (Opens.grothendieckTopology (extensionByZeroOpenSubsetSpace U))
            P.presheaf))
      simpa [openSubspaceModuleExtensionByZeroStalkUnderlyingMap, φ, P] using
        (TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
          P.presheaf)
    simpa [φ] using (asIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ))
  let M := openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk U ℱ x
  let eAdd : ↑(Presheaf.stalk P.presheaf x) ≃+ ↑M := e.addCommGroupIsoToAddEquiv
  simpa [openSubspaceModuleSheafExtensionByZeroModulePullbackStalk,
    openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk] using
    (eAdd.linearEquiv ((openSubspaceModuleRingSheaf U).presheaf.stalk x)).toModuleIso

/-- Helper for Lemma 6.31.8: the restricted stalk of the explicit extension-by-zero sheaf agrees
with the stalk of the raw module-pullback presheaf owner. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoModulePullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroModulePullbackStalk U ℱ x :=
  openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoSheafifiedPullback U ℱ x ≪≫
    (openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoSheafifiedPullback U ℱ x).symm

/-- Helper for Lemma 6.31.8: the raw module-pullback stalk owner agrees with the restricted
stalk after inverting the previously constructed comparison. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoRestrictedStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroModulePullbackStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x := by
  -- The target normalization is exactly the inverse of the earlier restricted-to-pullback
  -- comparison, now packaged once so the final stalk proof does not reopen it locally.
  exact
    (openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoModulePullbackStalk
      (U := U) ℱ x).symm

/-- Helper for Lemma 6.31.8: the stalk of the pulled-back ambient ring sheaf at `x` is the
ambient stalk of `\mathcal{O}_X` at `j(x)`. -/
public noncomputable abbrev openSubspaceModuleRingSheafStalkIsoAmbient
    (x : U) :
    (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf).presheaf.stalk x) ≅
      ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x) := by
  -- This is the canonical stalk pullback isomorphism for the ambient ring sheaf, specialized to
  -- the open inclusion `j : U ↪ X`.
  simpa [ambientModuleRingSheaf, openSubspaceModuleRingSheaf] using
    (TopCat.Sheaf.stalkPullbackIso
      (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).symm

/-- Helper for Lemma 6.31.8: the stalk ring isomorphism for the open inclusion induces the
equivalence between modules over `\mathcal{O}_{U, x}` and modules over `\mathcal{O}_{X, j(x)}`
used by the final stalk transport. -/
public noncomputable abbrev openSubspaceModuleRingSheafStalkEquivalence
    (x : U) :
    ModuleCat (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf).presheaf.stalk x) ≌
      ModuleCat (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x)) :=
  -- Package the ring-stalk identification once, so later owner normalizations can transport
  -- modules by functoriality instead of rewriting raw scalar structures repeatedly.
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    ((openSubspaceModuleRingSheafStalkIsoAmbient (U := U) x).symm.ringCatIsoToRingEquiv)

/-- Helper for Lemma 6.31.8: this is the plain ambient stalk module before transporting scalars
back to `\mathcal{O}_{U, x}`. -/
public abbrev openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x)) :=
  ModuleCat.of
    (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x))
    ↑(Presheaf.stalk
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
      (extensionByZeroOpenSubsetInclusion U x))

/-- Helper for Lemma 6.31.8: the transported ambient-stalk owner is literally the inverse-image
object of the stalk-ring equivalence applied to the plain ambient stalk module. -/
public theorem openSubspaceModuleSheafExtensionByZeroAmbientStalk_eq_inverse_obj
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x =
      (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).inverse.obj
        (openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x) := by
  -- Both sides are the same restriction-of-scalars construction along the stalk ring isomorphism.
  rfl

/-- Helper for Lemma 6.31.8: after transporting the local ambient-stalk owner across the
stalk-ring equivalence, one recovers the plain ambient stalk module. -/
public noncomputable abbrev openSubspaceModuleSheafExtensionByZeroAmbientStalkIsoPlainAmbient
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.obj
        (openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x) ≅
      openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x := by
  -- The ambient-stalk owner is the inverse-image object of the equivalence, so the counit
  -- collapses the transported scalars back to the plain ambient module.
  simpa [openSubspaceModuleSheafExtensionByZeroAmbientStalk_eq_inverse_obj] using
    ((openSubspaceModuleRingSheafStalkEquivalence (U := U) x).counitIso.app
      (openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x))

/-- Helper for Lemma 6.31.8: after transporting the already normalized restricted-stalk versus
raw module-pullback comparison across the stalk-ring equivalence, both stalk owners live in the
ambient scalar world. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroFunctorObjModulePullbackStalkIsoRestrictedStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.obj
        (openSubspaceModuleSheafExtensionByZeroModulePullbackStalk U ℱ x) ≅
      (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.obj
        (openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x) := by
  -- Move the module-pullback/restricted-stalk identification through the stalk-ring equivalence
  -- so the final base-change argument can stay entirely over the ambient stalk ring.
  exact
    (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.mapIso
      (openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoRestrictedStalk
        (U := U) ℱ x)

/-- Helper for Lemma 6.31.8: the commutative-ring stalk pullback comparison from Lemma 6.20.3,
specialized to the open-inclusion unit, lands in the restricted stalk `j^{-1} j_! \mathcal{F}`.
-/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroBaseChangeStalkIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :=
  -- Record the exact ambient base-change stalk isomorphism before transporting it to the local
  -- stalk owners used in this file.
  sheafOfModules_pullback_stalkIso
    (p := ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u}
      (extensionByZeroOpenSubsetInclusion U)).unit.app X.sheaf))
    (ℱ := ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ))
    (x := extensionByZeroOpenSubsetInclusion U x)

public noncomputable abbrev probeOpenEmbeddingRestrictionSheaf
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) :
    SheafOfModules (openSubspaceModuleRingSheaf U) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  exact
    (SheafOfModules.pushforward.{u} (F := U.isOpenEmbedding.functor)
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)).obj
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)

public noncomputable abbrev probeRestrictStalkIsoViaPresheafedSpace
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    Presheaf.stalk (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf x ≅
      Presheaf.stalk
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
        (extensionByZeroOpenSubsetInclusion U x) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let Xps : AlgebraicGeometry.PresheafedSpace AddCommGrpCat.{u} :=
    { carrier := X.carrier
      presheaf := ((SheafOfModules.toSheaf ambientModuleRingSheaf).obj
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)).val }
  simpa [probeOpenEmbeddingRestrictionSheaf, Xps, SheafOfModules.pushforward,
    ambientModuleRingSheaf, openSubspaceModuleRingSheaf] using
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Xps U.isOpenEmbedding x)


public abbrev probeOpenEmbeddingRestrictionStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    ModuleCat ((openSubspaceModuleRingSheaf U).presheaf.stalk x) :=
  ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf x)

public noncomputable def probeOpenEmbeddingRestrictionStalkHomToRestricted
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    probeOpenEmbeddingRestrictionStalk (U := U) ℱ x ⟶
      openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let G : SheafOfModules ambientModuleRingSheaf :=
    (openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ
  let e := (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U ambientModuleRingSheaf).app G
  simpa [probeOpenEmbeddingRestrictionStalk, probeOpenEmbeddingRestrictionSheaf,
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk,
    openSubspaceModuleSheafExtensionByZeroRestricted, G] using
    openSubspaceModuleExtensionByZeroStalkModuleMap x e.hom.val

public instance probeOpenEmbeddingRestrictionStalkHomToRestricted_isIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    IsIso (probeOpenEmbeddingRestrictionStalkHomToRestricted (U := U) ℱ x) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let G : SheafOfModules ambientModuleRingSheaf :=
    (openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ
  let e := (moduleSheafRestrictionToOpen_compare_open_embedding_pushforward U ambientModuleRingSheaf).app G
  let φ := e.hom.val
  haveI : IsIso e.hom := by infer_instance
  haveI : IsIso φ := by
    simpa [φ] using (Functor.map_isIso (SheafOfModules.forget _) e.hom)
  haveI : IsIso (openSubspaceModuleExtensionByZeroStalkUnderlyingMap x φ) := by
    simpa [openSubspaceModuleExtensionByZeroStalkUnderlyingMap, φ] using
      (Functor.map_isIso
        (SheafOfModules.forget (openSubspaceModuleRingSheaf U) ⋙
          PresheafOfModules.toPresheaf (openSubspaceModuleRingSheaf U).obj ⋙
          Presheaf.stalkFunctor AddCommGrpCat.{u} x)
        e.hom)
  simpa [probeOpenEmbeddingRestrictionStalkHomToRestricted,
    probeOpenEmbeddingRestrictionStalk, probeOpenEmbeddingRestrictionSheaf,
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk,
    openSubspaceModuleSheafExtensionByZeroRestricted, G, φ] using
    (openSubspaceModuleExtensionByZeroStalkModuleMap_isIso x φ)

public noncomputable abbrev probeOpenEmbeddingRestrictionStalkIsoRestricted
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    probeOpenEmbeddingRestrictionStalk (U := U) ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x :=
  asIso (probeOpenEmbeddingRestrictionStalkHomToRestricted (U := U) ℱ x)


public noncomputable abbrev probeConcreteRingStalkIsoAmbient (x : U) :
    (openSubspaceModuleRingSheaf U).presheaf.stalk x ≅
      ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let Rps : AlgebraicGeometry.PresheafedSpace RingCat.{u} :=
    { carrier := X.carrier
      presheaf := ambientModuleRingSheaf.val }
  let e₁raw :=
    (Presheaf.stalkFunctor RingCat.{u} x).mapIso
      ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso
        (openSubspaceModuleRingSheafIsoConcretePullback (U := U)))
  let e₁ :
      (openSubspaceModuleRingSheaf U).presheaf.stalk x ≅
        (((Topology.IsOpenEmbedding.sheafPullback RingCat.{u} U.isOpenEmbedding).obj
            ambientModuleRingSheaf).presheaf.stalk x) := by
    simpa using e₁raw
  exact e₁ ≪≫
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x)

public theorem probeConcreteRingStalkIsoAmbient_symm_germ
    (x : U) (V : Opens (extensionByZeroOpenSubsetSpace U)) (hxV : x ∈ V)
    (r : ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V))) :
    (probeConcreteRingStalkIsoAmbient (U := U) x).symm.hom
      (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
        (U.isOpenEmbedding.functor.obj V)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r) =
    TopCat.Presheaf.germ (openSubspaceModuleRingSheaf U).presheaf V x hxV
      ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).inv.hom.app
        (Opposite.op V)) r) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let Rps : AlgebraicGeometry.PresheafedSpace RingCat.{u} :=
    { carrier := X.carrier
      presheaf := ambientModuleRingSheaf.val }
  let σinv :
      (Rps.restrict U.isOpenEmbedding).presheaf ⟶ (openSubspaceModuleRingSheaf U).presheaf := by
    simpa [Rps, openSubspaceModuleRingSheaf] using
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).inv.hom)
  dsimp [probeConcreteRingStalkIsoAmbient]
  change
    (RingCat.Hom.hom ((Presheaf.stalkFunctor RingCat.{u} x).map σinv))
      ((AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x).inv
        (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
          (U.isOpenEmbedding.functor.obj V)
          (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r)) =
    TopCat.Presheaf.germ (openSubspaceModuleRingSheaf U).presheaf V x hxV
      (σinv.app (Opposite.op V) r)
  have hrestrict :
      (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x).inv
        (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
          (U.isOpenEmbedding.functor.obj V)
          (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r) =
      TopCat.Presheaf.germ (Rps.restrict U.isOpenEmbedding).presheaf V x hxV r := by
    simpa [Rps] using
      (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ_apply
        Rps U.isOpenEmbedding V x hxV r)
  rw [hrestrict]
  simpa [σinv] using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV σinv r)


public noncomputable abbrev probeConcreteRingStalkEquivalence (x : U) :
    ModuleCat (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        ambientModuleRingSheaf).presheaf.stalk x) ≌
      ModuleCat (ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x)) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv
    ((probeConcreteRingStalkIsoAmbient (U := U) x).symm.ringCatIsoToRingEquiv)

public theorem probeConcrete_source_germ_smul
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) (hxV : x ∈ V)
    (r : ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)))
    (m : (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf.obj (Opposite.op V)) :
    let source :=
      (probeConcreteRingStalkEquivalence (U := U) x).functor.obj
        (probeOpenEmbeddingRestrictionStalk (U := U) ℱ x)
    let mgerm : ↑source := by
      simpa [source, probeOpenEmbeddingRestrictionStalk] using
        (TopCat.Presheaf.germ
          (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV m)
    let rLocal : (openSubspaceModuleRingSheaf U).presheaf.obj (Opposite.op V) :=
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).inv.hom.app
        (Opposite.op V)) r
    (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
        (U.isOpenEmbedding.functor.obj V)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r) • mgerm =
      TopCat.Presheaf.germ
        (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV (rLocal • m) := by
  intro source mgerm rLocal
  change
    ((probeConcreteRingStalkIsoAmbient (U := U) x).symm.hom
      (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
        (U.isOpenEmbedding.functor.obj V)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r)) •
      (TopCat.Presheaf.germ
        (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV m) =
    TopCat.Presheaf.germ
      (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV (rLocal • m)
  rw [probeConcreteRingStalkIsoAmbient_symm_germ]
  exact (PresheafOfModules.germ_ringCat_smul
    (R := (openSubspaceModuleRingSheaf U).obj)
    (M := (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val)
    x V hxV rLocal m).symm



public theorem probeRestrictStalkIsoViaPresheafedSpace_germ
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) (hxV : x ∈ V)
    (m : (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf.obj (Opposite.op V)) :
    (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv
      (TopCat.Presheaf.germ
        (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV m) =
    TopCat.Presheaf.germ
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
      (U.isOpenEmbedding.functor.obj V)
      (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩
      (by
        simpa [probeOpenEmbeddingRestrictionSheaf] using m) := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let Xps : AlgebraicGeometry.PresheafedSpace AddCommGrpCat.{u} :=
    { carrier := X.carrier
      presheaf := ((SheafOfModules.toSheaf ambientModuleRingSheaf).obj
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ)).val }
  simpa [probeRestrictStalkIsoViaPresheafedSpace, probeOpenEmbeddingRestrictionSheaf,
    Xps, SheafOfModules.pushforward, ambientModuleRingSheaf, openSubspaceModuleRingSheaf] using
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_hom_eq_germ_apply
      Xps U.isOpenEmbedding V x hxV (by simpa [probeOpenEmbeddingRestrictionSheaf] using m))


public theorem probeConcrete_target_section_smul
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U))
    (V : Opens (extensionByZeroOpenSubsetSpace U))
    (r : ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)))
    (m : (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf.obj (Opposite.op V)) :
    let rLocal : (openSubspaceModuleRingSheaf U).presheaf.obj (Opposite.op V) :=
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).inv.hom.app
        (Opposite.op V)) r
    (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
      (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
      (by simpa [rLocal, probeOpenEmbeddingRestrictionSheaf] using (rLocal • m))) =
    r •
      (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
        (by simpa [probeOpenEmbeddingRestrictionSheaf] using m)) := by
  intro rLocal
  change
    (show ↑(ambientModuleRingSheaf.presheaf.obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
        (by
          simpa [Topology.IsOpenEmbedding.sheafPullback] using
            ((ConcreteCategory.hom
              ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom.app
                (Opposite.op V)) rLocal)))) •
      (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
        (by simpa [probeOpenEmbeddingRestrictionSheaf] using m)) =
    r •
      (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
        (by simpa [probeOpenEmbeddingRestrictionSheaf] using m))
  have hσ :
      (show ↑(ambientModuleRingSheaf.presheaf.obj
          (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
          (by
            simpa [Topology.IsOpenEmbedding.sheafPullback] using
              ((ConcreteCategory.hom
                ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom.app
                  (Opposite.op V)) rLocal)))) = r := by
    let σ := ((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf)
    let r' : ↑(((Topology.IsOpenEmbedding.sheafPullback RingCat.{u} U.isOpenEmbedding).obj
        ambientModuleRingSheaf).obj.obj (Opposite.op V)) := by
      simpa [Topology.IsOpenEmbedding.sheafPullback] using r
    let T := (Topology.IsOpenEmbedding.sheafPullback RingCat.{u} U.isOpenEmbedding).obj
      ambientModuleRingSheaf
    have happ : σ.inv.hom.app (Opposite.op V) ≫ σ.hom.hom.app (Opposite.op V) = 𝟙 _ := by
      change (σ.inv ≫ σ.hom).hom.app (Opposite.op V) = (𝟙 T : T ⟶ T).hom.app (Opposite.op V)
      rw [σ.inv_hom_id]
    have happly :
        (ConcreteCategory.hom (σ.hom.hom.app (Opposite.op V)))
          ((ConcreteCategory.hom (σ.inv.hom.app (Opposite.op V))) r') = r' := by
      simpa using (ConcreteCategory.congr_hom happ r')
    simpa [rLocal, r', σ, Topology.IsOpenEmbedding.sheafPullback] using happly
  rw [hσ]


public theorem probeConcrete_target_germ_smul
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) (hxV : x ∈ V)
    (r : ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)))
    (m : (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf.obj (Opposite.op V)) :
    let rLocal : (openSubspaceModuleRingSheaf U).presheaf.obj (Opposite.op V) :=
      (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).inv.hom.app
        (Opposite.op V)) r
    (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv
      (TopCat.Presheaf.germ
        (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV (rLocal • m)) =
    (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
        (U.isOpenEmbedding.functor.obj V)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r) •
      (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv
        (TopCat.Presheaf.germ
          (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV m) := by
  intro rLocal
  rw [probeRestrictStalkIsoViaPresheafedSpace_germ]
  rw [probeRestrictStalkIsoViaPresheafedSpace_germ]
  have hsec := probeConcrete_target_section_smul (U := U) ℱ V r m
  change
    TopCat.Presheaf.germ
      ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
      (U.isOpenEmbedding.functor.obj V)
      (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩
      (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
        (by simpa [rLocal, probeOpenEmbeddingRestrictionSheaf] using (rLocal • m))) =
    TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
      (U.isOpenEmbedding.functor.obj V)
      (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r •
      TopCat.Presheaf.germ
        ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf
        (U.isOpenEmbedding.functor.obj V)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩
        (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
          (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
          (by simpa [probeOpenEmbeddingRestrictionSheaf] using m))
  rw [hsec]
  exact
    (PresheafOfModules.germ_ringCat_smul
      (R := ambientModuleRingSheaf.obj)
      (M := ((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val)
      (extensionByZeroOpenSubsetInclusion U x)
      (U.isOpenEmbedding.functor.obj V) ⟨x, hxV, rfl⟩ r
      (show ↑(((openSubsetModuleSheafExtensionByZero U ambientModuleRingSheaf).obj ℱ).val.presheaf.obj
        (Opposite.op (U.isOpenEmbedding.functor.obj V))) from
        (by simpa [probeOpenEmbeddingRestrictionSheaf] using m)))


public theorem probeConcreteRestrictStalkIsoViaPresheafedSpace_germ_smul_same
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (V : Opens (extensionByZeroOpenSubsetSpace U)) (hxV : x ∈ V)
    (r : ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)))
    (m : (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf.obj (Opposite.op V)) :
    let source :=
      (probeConcreteRingStalkEquivalence (U := U) x).functor.obj
        (probeOpenEmbeddingRestrictionStalk (U := U) ℱ x)
    let mgerm : ↑source := by
      simpa [source, probeOpenEmbeddingRestrictionStalk] using
        (TopCat.Presheaf.germ
          (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf V x hxV m)
    (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv
      ((TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
          (U.isOpenEmbedding.functor.obj V)
          (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r) • mgerm) =
    (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
        (U.isOpenEmbedding.functor.obj V)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r) •
      (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv mgerm := by
  intro source mgerm
  let rLocal : (openSubspaceModuleRingSheaf U).presheaf.obj (Opposite.op V) :=
    (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).inv.hom.app
      (Opposite.op V)) r
  rw [probeConcrete_source_germ_smul]
  exact probeConcrete_target_germ_smul (U := U) ℱ x V hxV r m


public theorem probeConcreteRestrictStalkIsoViaPresheafedSpace_smul
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U)
    (r : ambientModuleRingSheaf.presheaf.stalk (extensionByZeroOpenSubsetInclusion U x))
    (m : ↑((probeConcreteRingStalkEquivalence (U := U) x).functor.obj
      (probeOpenEmbeddingRestrictionStalk (U := U) ℱ x))) :
    (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv (r • m) =
      r • (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv m := by
  let H := (probeOpenEmbeddingRestrictionSheaf (U := U) ℱ).val.presheaf
  let source :=
    (probeConcreteRingStalkEquivalence (U := U) x).functor.obj
      (probeOpenEmbeddingRestrictionStalk (U := U) ℱ x)
  let m0 : ↑(Presheaf.stalk H x) := by
    simpa [source, H, probeOpenEmbeddingRestrictionStalk] using m
  obtain ⟨W, hxW, rW, hr⟩ :=
    TopCat.Presheaf.germ_exist ambientModuleRingSheaf.presheaf
      (extensionByZeroOpenSubsetInclusion U x) r
  obtain ⟨V, hxV, mV, hm⟩ := TopCat.Presheaf.germ_exist H x m0
  let WU : Opens (extensionByZeroOpenSubsetSpace U) :=
    (Opens.map (extensionByZeroOpenSubsetInclusion U)).obj W
  let C : Opens (extensionByZeroOpenSubsetSpace U) := V ⊓ WU
  have hxWU : x ∈ WU := by
    simpa [WU] using hxW
  have hxC : x ∈ C := ⟨hxV, hxWU⟩
  have hImageCW : U.isOpenEmbedding.functor.obj C ≤ W := by
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hz.2
  let rC : ambientModuleRingSheaf.presheaf.obj
      (Opposite.op (U.isOpenEmbedding.functor.obj C)) :=
    ambientModuleRingSheaf.presheaf.map (homOfLE hImageCW).op rW
  let mC : H.obj (Opposite.op C) := H.map (homOfLE inf_le_left).op mV
  have hrC :
      TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
        (U.isOpenEmbedding.functor.obj C)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxC, rfl⟩ rC = r := by
    calc
      TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
          (U.isOpenEmbedding.functor.obj C)
          (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxC, rfl⟩ rC =
        TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf W
          (extensionByZeroOpenSubsetInclusion U x) (hImageCW ⟨x, hxC, rfl⟩) rW := by
          simpa [rC] using
            (ambientModuleRingSheaf.presheaf.germ_res_apply (homOfLE hImageCW)
              (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxC, rfl⟩ rW)
      _ = r := by
        simpa using hr
  have hmC : TopCat.Presheaf.germ H C x hxC mC = m0 := by
    calc
      TopCat.Presheaf.germ H C x hxC mC =
          TopCat.Presheaf.germ H V x hxV mV := by
          simpa [mC] using (TopCat.Presheaf.germ_res_apply H (homOfLE inf_le_left) x hxC mV)
      _ = m0 := hm
  have hmC_source :
      (show ↑source from TopCat.Presheaf.germ H C x hxC mC) = m := by
    simpa [source, H, m0, probeOpenEmbeddingRestrictionStalk] using hmC
  have hsame :=
    probeConcreteRestrictStalkIsoViaPresheafedSpace_germ_smul_same
      (U := U) ℱ x C hxC rC mC
  change
    (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv
        ((TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
            (U.isOpenEmbedding.functor.obj C)
            (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxC, rfl⟩ rC) •
          (show ↑source from TopCat.Presheaf.germ H C x hxC mC)) =
      (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
          (U.isOpenEmbedding.functor.obj C)
          (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxC, rfl⟩ rC) •
        (probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x).addCommGroupIsoToAddEquiv
          (show ↑source from TopCat.Presheaf.germ H C x hxC mC) at hsame
  rw [hrC, hmC_source] at hsame
  exact hsame


public noncomputable abbrev probeConcreteFunctorObjOpenEmbeddingRestrictionStalkIsoPlain
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    (probeConcreteRingStalkEquivalence (U := U) x).functor.obj
        (probeOpenEmbeddingRestrictionStalk (U := U) ℱ x) ≅
      openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x := by
  let source :=
    (probeConcreteRingStalkEquivalence (U := U) x).functor.obj
      (probeOpenEmbeddingRestrictionStalk (U := U) ℱ x)
  let target := openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x
  let e := probeRestrictStalkIsoViaPresheafedSpace (U := U) ℱ x
  let eAdd : ↑source ≃+ ↑target := by
    simpa [source, target, probeOpenEmbeddingRestrictionStalk,
      openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk] using e.addCommGroupIsoToAddEquiv
  let eLin : ↑source ≃ₗ[ambientModuleRingSheaf.presheaf.stalk
      (extensionByZeroOpenSubsetInclusion U x)] ↑target :=
    { __ := eAdd
      map_smul' := by
        intro r m
        exact probeConcreteRestrictStalkIsoViaPresheafedSpace_smul (U := U) ℱ x r m }
  exact eLin.toModuleIso



public theorem probeToSheafify_stalk_map_germ_apply_ring {Y : TopCat.{u}}
    (ℱ : Y.Presheaf RingCat.{u}) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t : ℱ.obj (Opposite.op W)) :
    ((TopCat.Presheaf.stalkFunctor RingCat.{u} y).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ))
      (TopCat.Presheaf.germ ℱ W y hy t) =
      (TopCat.Presheaf.germ (CategoryTheory.sheafify (Opens.grothendieckTopology Y) ℱ)
        W y hy)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ).app
          (Opposite.op W) t) := by
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      (CategoryTheory.toSheafify (Opens.grothendieckTopology Y) ℱ) t)

public theorem probePullbackIso_inv_stalk_map_germ_apply_ring {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf RingCat.{u}) (W : Opens Y) (y : Y) (hy : y ∈ W)
    (t :
      (CategoryTheory.sheafify (Opens.grothendieckTopology Y)
        ((TopCat.Sheaf.forget RingCat.{u} T ⋙
          TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).obj
          (Opposite.op W)) :
    ((TopCat.Presheaf.stalkFunctor RingCat.{u} y).map
        ((TopCat.Sheaf.forget RingCat.{u} Y).map
          ((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (CategoryTheory.sheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget RingCat.{u} T ⋙
              TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢))
          W y hy) t) =
      (((f⁻¹).obj 𝒢).presheaf).germ W y hy
        ((((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢).1.app
          (Opposite.op W)) t) := by
  simpa using
    (TopCat.Presheaf.stalkFunctor_map_germ_apply W y hy
      ((TopCat.Sheaf.forget RingCat.{u} Y).map
        ((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢)) t)

public theorem probePullbackIso_inv_toSheafify_unit_section_eq_ring {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf RingCat.{u}) (W : Opens T)
    (s : 𝒢.1.obj (Opposite.op W)) :
    (((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢).1.app
        (Opposite.op ((Opens.map f).obj W)))
      (((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget RingCat.{u} T ⋙ TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).app
          (Opposite.op ((Opens.map f).obj W)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
          (Opposite.op W)) s)) =
      ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
        (Opposite.op W)) s) := by
  have h :=
    CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app
      (TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f)
      (CategoryTheory.Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (Opens.map f) RingCat.{u} (Opens.grothendieckTopology T)
          (Opens.grothendieckTopology Y))
      𝒢
  have happ := congrArg (fun k ↦ (k.1.app (Opposite.op W)) s) h
  have happ' :
      (((TopCat.Sheaf.pullbackIso RingCat.{u} f).hom.app 𝒢).1.app
          (Opposite.op ((Opens.map f).obj W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op W)) s) =
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget RingCat.{u} T ⋙ TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).app
          (Opposite.op ((Opens.map f).obj W)))
        ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
          (Opposite.op W)) s) := by
    simpa using happ
  rw [← happ']
  simpa using
    congrArg
      (fun k ↦ (k.hom.app (Opposite.op ((Opens.map f).obj W)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op W)) s))
      (Iso.hom_inv_id_app (TopCat.Sheaf.pullbackIso RingCat.{u} f) 𝒢)

public theorem probePullbackIso_inv_toSheafify_unit_stalk_germ_eq_ring {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf RingCat.{u}) (W : Opens T) (y : Y)
    (hy : y ∈ (Opens.map f).obj W) (s : 𝒢.1.obj (Opposite.op W)) :
    ((TopCat.Presheaf.stalkFunctor RingCat.{u} y).map
        ((TopCat.Sheaf.forget RingCat.{u} Y).map
          ((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢)))
      ((TopCat.Presheaf.germ
          (CategoryTheory.sheafify (Opens.grothendieckTopology Y)
            ((TopCat.Sheaf.forget RingCat.{u} T ⋙
              TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢))
          ((Opens.map f).obj W) y hy)
        ((CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
          ((TopCat.Sheaf.forget RingCat.{u} T ⋙ TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢)).app
          (Opposite.op ((Opens.map f).obj W))
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
            (Opposite.op W)) s))) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj W) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op W)) s) := by
  rw [probePullbackIso_inv_stalk_map_germ_apply_ring]
  rw [probePullbackIso_inv_toSheafify_unit_section_eq_ring]

public theorem probeSheaf_stalkPullbackIso_germ_apply_ring {Y T : TopCat.{u}}
    (f : Y ⟶ T) (𝒢 : T.Sheaf RingCat.{u}) (W : Opens T) (y : Y)
    (hy : y ∈ (Opens.map f).obj W) (s : 𝒢.1.obj (Opposite.op W)) :
    ((TopCat.Sheaf.stalkPullbackIso f 𝒢 y).hom)
      (𝒢.presheaf.germ W (f y) (by simpa using hy) s) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj W) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op W)) s) := by
  have hy' : f y ∈ W := by simpa using hy
  rw [TopCat.Sheaf.stalkPullbackIso_def]
  simp only [Iso.trans_hom]
  change
    ((TopCat.Presheaf.stalkFunctor RingCat.{u} y).map
        ((TopCat.Sheaf.forget RingCat.{u} Y).map
          ((TopCat.Sheaf.pullbackIso RingCat.{u} f).inv.app 𝒢)))
      (((TopCat.Presheaf.stalkFunctor RingCat.{u} y).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology Y)
            ((TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢.obj)))
        ((TopCat.Presheaf.stalkPullbackIso RingCat.{u} f 𝒢.presheaf y).hom
          (𝒢.presheaf.germ W (f y) hy' s))) =
      (((f⁻¹).obj 𝒢).presheaf).germ ((Opens.map f).obj W) y hy
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢).1.app
          (Opposite.op W)) s)
  have hpresheaf :
      (TopCat.Presheaf.stalkPullbackIso RingCat.{u} f 𝒢.presheaf y).hom
          (𝒢.presheaf.germ W (f y) hy' s) =
        (((TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢.1).germ
          ((Opens.map f).obj W) y hy
          ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
            (Opposite.op W)) s)) := by
    let a := 𝒢.presheaf.germ W (f y) hy'
    let b := TopCat.Presheaf.stalkPullbackHom RingCat.{u} f 𝒢.1 y
    let c := (((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
      (Opposite.op W))
    let d := ((TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢.1).germ
      ((Opens.map f).obj W) y hy
    have h := TopCat.Presheaf.germ_stalkPullbackHom RingCat.{u} f 𝒢.1 y W hy
    have h' : (ConcreteCategory.hom (a ≫ b)) s =
        (ConcreteCategory.hom (c ≫ d)) s := by
      exact congrArg (fun k ↦ (ConcreteCategory.hom k) s) h
    change (ConcreteCategory.hom b) ((ConcreteCategory.hom a) s) =
      (ConcreteCategory.hom d) ((ConcreteCategory.hom c) s)
    convert h' using 1
  rw [hpresheaf]
  rw [probeToSheafify_stalk_map_germ_apply_ring
    (ℱ := ((TopCat.Presheaf.pullback RingCat.{u} f).obj 𝒢.obj))
    (W := (Opens.map f).obj W) (y := y) (hy := hy)
    (t := ((((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat.{u} f).unit.app 𝒢.1).app
      (Opposite.op W)) s))]
  exact probePullbackIso_inv_toSheafify_unit_stalk_germ_eq_ring
    (f := f) (𝒢 := 𝒢) (W := W) (y := y) (hy := hy) (s := s)

public theorem probeOfficialStalkPullbackIso_hom_comp_concrete (x : U) :
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    let Rps : AlgebraicGeometry.PresheafedSpace RingCat.{u} :=
      { carrier := X.carrier
        presheaf := ambientModuleRingSheaf.val }
    (TopCat.Sheaf.stalkPullbackIso
        (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).hom ≫
      (Presheaf.stalkFunctor RingCat.{u} x).map
        ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map
          (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)) =
    (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x).inv := by
  letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
  let Rps : AlgebraicGeometry.PresheafedSpace RingCat.{u} :=
    { carrier := X.carrier
      presheaf := ambientModuleRingSheaf.val }
  apply TopCat.Presheaf.stalk_hom_ext ambientModuleRingSheaf.presheaf
  intro W hxW
  ext r
  let V : Opens (extensionByZeroOpenSubsetSpace U) :=
    (Opens.map (extensionByZeroOpenSubsetInclusion U)).obj W
  have hxV : x ∈ V := by
    simpa [V] using hxW
  let rV : ambientModuleRingSheaf.presheaf.obj (Opposite.op (U.isOpenEmbedding.functor.obj V)) :=
    ambientModuleRingSheaf.presheaf.map
      (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W).op r
  have hgerm :
      TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf
          (U.isOpenEmbedding.functor.obj V)
          (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ rV =
        TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf W
          (extensionByZeroOpenSubsetInclusion U x) hxW r := by
    simpa [V, rV] using
      (ambientModuleRingSheaf.presheaf.germ_res_apply
        (U.isOpenEmbedding.isOpenMap.adjunction.counit.app W)
        (extensionByZeroOpenSubsetInclusion U x) ⟨x, hxV, rfl⟩ r)
  have hunit :
      (RingCat.Hom.hom
          ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom.app
            (Opposite.op V)))
        ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
              (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom.app
            (Opposite.op W)) r) =
      rV := by
    have h :=
      congrArg
        (fun η ↦ RingCat.Hom.hom (η.app (Opposite.op W)) r)
        (open_embedding_pushforward_adjunction_counit_eq U ambientModuleRingSheaf)
    simpa [V, rV, ambientModuleRingSheaf] using h.symm
  calc
    ((RingCat.Hom.hom
          ((Presheaf.stalkFunctor RingCat.{u} x).map
            ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map
              (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom)))).comp
        (RingCat.Hom.hom
          (TopCat.Sheaf.stalkPullbackIso
            (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).hom)).comp
        (RingCat.Hom.hom
          (Presheaf.germ ambientModuleRingSheaf.presheaf W
            (extensionByZeroOpenSubsetInclusion U x) hxW)) r =
      (RingCat.Hom.hom
          ((Presheaf.stalkFunctor RingCat.{u} x).map
            ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map
              (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom))))
        ((TopCat.Sheaf.stalkPullbackIso
            (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).hom
          (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf W
            (extensionByZeroOpenSubsetInclusion U x) hxW r)) := rfl
    _ =
      (RingCat.Hom.hom
          ((Presheaf.stalkFunctor RingCat.{u} x).map
            ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map
              (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom))))
        ((((extensionByZeroOpenSubsetInclusion U)⁻¹).obj ambientModuleRingSheaf).presheaf.germ
          V x hxV
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
              (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).1.app
            (Opposite.op W)) r)) := by
        rw [probeSheaf_stalkPullbackIso_germ_apply_ring
          (f := extensionByZeroOpenSubsetInclusion U) (𝒢 := ambientModuleRingSheaf)
          (W := W) (y := x) (hy := hxV) (s := r)]
    _ =
      TopCat.Presheaf.germ
          (Rps.restrict U.isOpenEmbedding).presheaf V x hxV
        ((RingCat.Hom.hom
          ((((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom).hom.app
            (Opposite.op V)))
          ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
              (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).hom.app
            (Opposite.op W)) r)) := by
        simpa [Rps, V, Topology.IsOpenEmbedding.sheafPullback] using
          (TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
            ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map
              (((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf).hom))
            ((((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat.{u}
              (extensionByZeroOpenSubsetInclusion U)).unit.app ambientModuleRingSheaf).1.app
                (Opposite.op W)) r))
    _ =
      TopCat.Presheaf.germ
          (Rps.restrict U.isOpenEmbedding).presheaf V x hxV rV := by
        rw [hunit]
    _ =
      (RingCat.Hom.hom
          (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x).inv)
        (TopCat.Presheaf.germ ambientModuleRingSheaf.presheaf W
          (extensionByZeroOpenSubsetInclusion U x) hxW r) := by
        rw [← hgerm]
        simpa [Rps, V, Topology.IsOpenEmbedding.sheafPullback] using
          (AlgebraicGeometry.PresheafedSpace.restrictStalkIso_inv_eq_germ_apply
            Rps U.isOpenEmbedding V x hxV rV).symm

public theorem probeConcreteRingStalkIsoAmbient_symm_hom_eq_official (x : U) :
    (probeConcreteRingStalkIsoAmbient (U := U) x).symm.hom.hom =
      (openSubspaceModuleRingSheafStalkIsoAmbient (U := U) x).symm.hom.hom := by
  have hMor :
      (probeConcreteRingStalkIsoAmbient (U := U) x).symm.hom =
        (openSubspaceModuleRingSheafStalkIsoAmbient (U := U) x).symm.hom := by
    letI := Topology.IsOpenEmbedding.functor_isContinuous U.isOpenEmbedding
    let σ := ((U.isOpenEmbedding.sheafPullbackIso RingCat.{u}).app ambientModuleRingSheaf)
    let Rps : AlgebraicGeometry.PresheafedSpace RingCat.{u} :=
      { carrier := X.carrier
        presheaf := ambientModuleRingSheaf.val }
    have hcomp :
        (TopCat.Sheaf.stalkPullbackIso
            (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).hom ≫
          (Presheaf.stalkFunctor RingCat.{u} x).map
            ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map σ.hom) =
        (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x).inv := by
      simpa [Rps, σ] using probeOfficialStalkPullbackIso_hom_comp_concrete (U := U) x
    let mHom :=
      (Presheaf.stalkFunctor RingCat.{u} x).map
        ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map σ.hom)
    let mInv :=
      (Presheaf.stalkFunctor RingCat.{u} x).map
        ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).map σ.inv)
    have hprobe :
        (probeConcreteRingStalkIsoAmbient (U := U) x).symm.hom =
          (AlgebraicGeometry.PresheafedSpace.restrictStalkIso Rps U.isOpenEmbedding x).inv ≫
            mInv := by
      rfl
    have hcancel :
        mHom ≫ mInv =
          𝟙 (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            ambientModuleRingSheaf).presheaf.stalk x) := by
      simpa [mHom, mInv] using
        (Iso.hom_inv_id
          ((Presheaf.stalkFunctor RingCat.{u} x).mapIso
            ((TopCat.Sheaf.forget RingCat.{u} (extensionByZeroOpenSubsetSpace U)).mapIso σ)))
    let official :=
      (TopCat.Sheaf.stalkPullbackIso
        (extensionByZeroOpenSubsetInclusion U) ambientModuleRingSheaf x).hom
    have htail :
        ((official ≫ mHom) ≫ mInv) = official := by
      calc
        ((official ≫ mHom) ≫ mInv) = official ≫ (mHom ≫ mInv) := by
          exact Category.assoc official mHom mInv
        _ = official ≫ 𝟙 _ := by
          exact congrArg (fun t ↦ official ≫ t) hcancel
        _ = official := by
          simp
    rw [hprobe, ← hcomp]
    change
      ((official ≫ mHom) ≫ mInv) =
      (openSubspaceModuleRingSheafStalkIsoAmbient (U := U) x).symm.hom
    rw [htail]
    simp [official, openSubspaceModuleRingSheafStalkIsoAmbient, ambientModuleRingSheaf]
  exact congrArg RingCat.Hom.hom hMor


/-- Helper for Lemma 6.31.8: the plain ambient stalk of `j_! \mathcal{F}` agrees with the image
of the source stalk under the ambient/local stalk-ring equivalence. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroPlainAmbientStalkIsoFunctorObjSource
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x ≅
      (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.obj
        (ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
          ↑(Presheaf.stalk ℱ.val.presheaf x)) := by
  let source := ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
    ↑(Presheaf.stalk ℱ.val.presheaf x)
  let eConcrete :
      openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x ≅
        (probeConcreteRingStalkEquivalence (U := U) x).functor.obj source :=
    (probeConcreteFunctorObjOpenEmbeddingRestrictionStalkIsoPlain (U := U) ℱ x).symm ≪≫
      (probeConcreteRingStalkEquivalence (U := U) x).functor.mapIso
        (probeOpenEmbeddingRestrictionStalkIsoRestricted (U := U) ℱ x ≪≫
          openSubspaceModuleSheafExtensionByZero_restrictedStalkIso (U := U) ℱ x)
  let hRing :
      (probeConcreteRingStalkIsoAmbient (U := U) x).symm.hom.hom =
        (openSubspaceModuleRingSheafStalkIsoAmbient (U := U) x).symm.hom.hom :=
    probeConcreteRingStalkIsoAmbient_symm_hom_eq_official (U := U) x
  exact eConcrete ≪≫ (ModuleCat.restrictScalarsCongr hRing).app source

/-- Helper for Lemma 6.31.8: at a point of `U`, the ambient stalk of `j_! \mathcal{F}` is the
source stalk `\mathcal{F}_x`, viewed as an `\mathcal{O}_{U, x}`-module through the pullback
stalk-ring identification. -/
public noncomputable abbrev openSubspaceModuleSheafExtensionByZeroAmbientStalkIsoSource
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x ≅
      ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
        ↑(Presheaf.stalk ℱ.val.presheaf x) := by
  let M :=
    ModuleCat.of ((openSubspaceModuleRingSheaf U).presheaf.stalk x)
      ↑(Presheaf.stalk ℱ.val.presheaf x)
  -- First normalize in the ambient scalar world, then transport back across the unit of the
  -- stalk-ring equivalence.
  exact
    (eqToIso
      (openSubspaceModuleSheafExtensionByZeroAmbientStalk_eq_inverse_obj (U := U) ℱ x)) ≪≫
      (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).inverse.mapIso
        (openSubspaceModuleSheafExtensionByZeroPlainAmbientStalkIsoFunctorObjSource
          (U := U) ℱ x) ≪≫
      ((openSubspaceModuleRingSheafStalkEquivalence (U := U) x).unitIso.app M).symm

/-- Helper for Lemma 6.31.8: after moving the pullback-side stalk module across the stalk-ring
equivalence, it becomes the plain ambient stalk module at `j(x)`. -/
public noncomputable abbrev openSubspaceModuleSheafExtensionByZeroPullbackStalkIsoPlainAmbient
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    (openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.obj
        (openSubspaceModuleSheafExtensionByZeroPullbackStalk U ℱ x) ≅
      openSubspaceModuleSheafExtensionByZeroPlainAmbientStalk (U := U) ℱ x := by
  -- First identify the pullback-side stalk with the transported ambient-stalk owner, then use
  -- the stalk-ring counit to forget that transport.
  exact
    ((openSubspaceModuleRingSheafStalkEquivalence (U := U) x).functor.mapIso
      (openSubspaceModuleSheafExtensionByZeroPullbackStalkIsoAmbient (U := U) ℱ x)) ≪≫
        openSubspaceModuleSheafExtensionByZeroAmbientStalkIsoPlainAmbient (U := U) ℱ x

/-- Helper for Lemma 6.31.8: the commutative-ring stalk pullback comparison from Lemma 6.20.3,
specialized to the open-inclusion unit, lands in the restricted stalk `j^{-1} j_! \mathcal{F}`.
-/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroCommPullbackStalkIsoRestrictedStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroPullbackStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x := by
  -- Compare both stalk owners through the common source stalk `\mathcal{F}_x`: first identify
  -- the pulled-back ambient stalk with the ambient stalk at `j(x)`, then use the inside-`U`
  -- stalk description for `j_! \mathcal{F}`, and finally invert the already established
  -- restricted-stalk comparison.
  exact
    openSubspaceModuleSheafExtensionByZeroPullbackStalkIsoAmbient (U := U) ℱ x ≪≫
      openSubspaceModuleSheafExtensionByZeroAmbientStalkIsoSource (U := U) ℱ x ≪≫
        (openSubspaceModuleSheafExtensionByZero_restrictedStalkIso (U := U) ℱ x).symm

/-- Helper for Lemma 6.31.8: the inverse component of the additive sheaf pullback comparison
identifies the sheafified pullback stalk with the actual pullback stalk. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalkIsoPullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroPullbackStalk U ℱ x := by
  -- Route correction: bypass the unfinished underlying-sheaf normalization and instead compare
  -- the two stalk owners through the already-established restricted-stalk module isomorphisms.
  exact
    (openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoSheafifiedPullback U ℱ x).symm ≪≫
      (openSubspaceModuleSheafExtensionByZeroCommPullbackStalkIsoRestrictedStalk U ℱ x).symm

/-- Helper for Lemma 6.31.8: composing the raw-to-sheafified comparison with the
sheafified-to-actual-pullback comparison identifies the raw module-pullback stalk owner with the
explicit pullback-side stalk module. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoPullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroModulePullbackStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroPullbackStalk U ℱ x :=
  openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoSheafifiedPullback U ℱ x ≪≫
    openSubspaceModuleSheafExtensionByZeroSheafifiedPullbackStalkIsoPullbackStalk U ℱ x

/-- Helper for Lemma 6.31.8: the restricted stalk of the explicit extension-by-zero sheaf on the
open subspace is canonically isomorphic to the pullback-side stalk module built from the ambient
stalk comparison. -/
public noncomputable abbrev
    openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoPullbackStalk
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroPullbackStalk U ℱ x := by
  -- Compose the already-established restricted-to-raw comparison with the new normalized
  -- raw-to-actual-pullback comparison.
  exact
    openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoModulePullbackStalk U ℱ x ≪≫
      openSubspaceModuleSheafExtensionByZeroModulePullbackStalkIsoPullbackStalk U ℱ x

public noncomputable abbrev openSubspaceModuleSheafExtensionByZeroAmbientStalkIso
    (ℱ : SheafOfModules (openSubspaceModuleRingSheaf U)) (x : U) :
    openSubspaceModuleSheafExtensionByZeroRestrictedStalk U ℱ x ≅
      openSubspaceModuleSheafExtensionByZeroAmbientStalk U ℱ x :=
  openSubspaceModuleSheafExtensionByZeroRestrictedStalkIsoPullbackStalk U ℱ x ≪≫
    openSubspaceModuleSheafExtensionByZeroPullbackStalkIsoAmbient U ℱ x

/-- Lemma 6.31.8 (3), on `U`: for `x : U`, the stalk of `j_! \mathcal{F}` at the corresponding
point of `X` is canonically isomorphic to the stalk of `\mathcal{F}` at `x`. The left-hand side
is viewed as an `\mathcal{O}_{U, x}`-module via the canonical stalk isomorphism
`\mathcal{O}_{U, x} \cong \mathcal{O}_{X, x}` coming from pullback along the open immersion. -/
noncomputable abbrev openSubspaceModuleSheafExtensionByZero_stalkIso
    (ℱ : SheafOfModules
      ((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
        (RingedSpace.ringCatSheaf X)))
    (x : U) :
      (ModuleCat.restrictScalars
        (((TopCat.Sheaf.stalkPullbackIso
            (extensionByZeroOpenSubsetInclusion U) (RingedSpace.ringCatSheaf X) x).symm).hom.hom)).obj
      (ModuleCat.of
        ((RingedSpace.ringCatSheaf X).presheaf.stalk (extensionByZeroOpenSubsetInclusion U x))
        ↑(Presheaf.stalk
          ((openSubsetModuleSheafExtensionByZero U (RingedSpace.ringCatSheaf X)).obj ℱ).val.presheaf
          (extensionByZeroOpenSubsetInclusion U x))) ≅
      ModuleCat.of
        (((Sheaf.pullback RingCat.{u} (extensionByZeroOpenSubsetInclusion U)).obj
            (RingedSpace.ringCatSheaf X)).presheaf.stalk x)
        ↑(Presheaf.stalk ℱ.val.presheaf x) := by
  simpa [ambientModuleRingSheaf, openSubspaceModuleRingSheaf,
    openSubspaceModuleSheafExtensionByZeroAmbientStalk] using
    (openSubspaceModuleSheafExtensionByZeroAmbientStalkIso U ℱ x).symm ≪≫
      openSubspaceModuleSheafExtensionByZero_restrictedStalkIso U ℱ x

end
