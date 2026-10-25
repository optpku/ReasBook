module

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
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopCat TopologicalSpace TopologicalSpace.Opens
open CategoryTheory.Limits
open scoped Classical ZeroObject

attribute [local instance] CategoryTheory.Types.instConcreteCategory CategoryTheory.Types.instFunLike

noncomputable section

universe w v u

section

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{v} C] [HasInitial C]

/-- The topological space underlying the open subspace `U ⊆ X`. -/
abbrev extensionByZeroOpenSubsetSpace (U : Opens X) : TopCat.{w} :=
  (Opens.toTopCat X).obj U

/-- The inclusion of the open subspace `U ⊆ X` into the ambient space `X`. -/
abbrev extensionByZeroOpenSubsetInclusion (U : Opens X) : extensionByZeroOpenSubsetSpace U ⟶ X :=
  Opens.inclusion' U

/-- The pullback of an ambient open subset of `X` to the open subspace `U`. -/
abbrev openSubsetPreimageOpen (U : Opens X) (V : Opens X) :
    Opens (extensionByZeroOpenSubsetSpace U) :=
  (Opens.map (extensionByZeroOpenSubsetInclusion U)).obj V

/-- The value of the presheaf-level extension-by-initial-object construction on an ambient open. -/
public abbrev openSubsetPresheafExtensionByInitialObjectValue
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) (V : (Opens X)ᵒᵖ) : C :=
  if unop V ≤ U then
    ℱ.obj (op (openSubsetPreimageOpen U (unop V)))
  else
    ⊥_ C

/-- Helper for Extension by zero / by the initial object: on an ambient open contained in `U`, the
raw value object of the extension-by-initial-object construction is the original section object. -/
public theorem openSubsetPresheafExtensionByInitialObjectValue_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (hV : unop V ≤ U) :
    openSubsetPresheafExtensionByInitialObjectValue U ℱ V =
      ℱ.obj (op (openSubsetPreimageOpen U (unop V))) := by
  simp [openSubsetPresheafExtensionByInitialObjectValue, hV]

/-- Helper for Extension by zero / by the initial object: on an ambient open not contained in `U`,
the raw value object of the extension-by-initial-object construction is the initial object. -/
public theorem openSubsetPresheafExtensionByInitialObjectValue_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (hV : ¬ unop V ≤ U) :
    openSubsetPresheafExtensionByInitialObjectValue U ℱ V = ⊥_ C := by
  simp [openSubsetPresheafExtensionByInitialObjectValue, hV]

/-- Helper for Extension by zero / by the initial object: transporting a morphism across
equalities of source and target objects is conjugation by the corresponding `eqToHom` maps. -/
private theorem cast_hom_eqToHom_comp_eqToHom
    {A A' B B' : C} (hA : A = A') (hB : B = B') (f : A' ⟶ B') :
    cast (by cases hA; cases hB; rfl) f = eqToHom hA ≫ f ≫ eqToHom hB.symm := by
  -- After both object equalities are reduced to reflexivity, the transport is just the identity.
  cases hA
  cases hB
  simp

/-- Helper for Extension by zero / by the initial object: once an object is identified with the
initial object, the induced map from that object to itself is its identity. -/
@[simp] private theorem eqToHom_comp_initial_to_eq_id {A : C} (hA : A = ⊥_ C) :
    eqToHom hA ≫ initial.to A = 𝟙 A := by
  -- This is the unique endomorphism of the initial object after reducing the identification.
  cases hA
  exact initial.hom_ext _ _

/-- Helper for Extension by zero / by the initial object: the two transports induced by an object
equality cancel to the identity. -/
@[simp] private theorem eqToHom_comp_eqToHom_symm_eq_id {A B : C} (h : A = B) :
    eqToHom h ≫ eqToHom h.symm = 𝟙 A := by
  -- After reducing the equality to reflexivity, both transports are identities.
  cases h
  simp

/-- The restriction map in the presheaf-level extension-by-initial-object construction. -/
public noncomputable def openSubsetPresheafExtensionByInitialObjectMap
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    openSubsetPresheafExtensionByInitialObjectValue U ℱ V ⟶
      openSubsetPresheafExtensionByInitialObjectValue U ℱ W := by
  classical
  by_cases hV : unop V ≤ U
  · let hW : unop W ≤ U := le_trans i.unop.le hV
    exact
      eqToHom (openSubsetPresheafExtensionByInitialObjectValue_eq_of_le U ℱ hV) ≫
        ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
          eqToHom (openSubsetPresheafExtensionByInitialObjectValue_eq_of_le U ℱ hW).symm
  · exact
      eqToHom (openSubsetPresheafExtensionByInitialObjectValue_eq_of_not_le U ℱ hV) ≫
        initial.to (openSubsetPresheafExtensionByInitialObjectValue U ℱ W)

-- Proof sketch: split into the cases `V ⊆ U` and `V ⊈ U`; on the inside branch this reduces to
-- `ℱ.map_id`, while on the outside branch it is the identity on the initial object.
/-- The restriction maps in presheaf extension by the initial object satisfy the identity law. -/
public theorem openSubsetPresheafExtensionByInitialObject_map_id
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) (V : (Opens X)ᵒᵖ) :
    openSubsetPresheafExtensionByInitialObjectMap U ℱ (𝟙 V) =
      𝟙 (openSubsetPresheafExtensionByInitialObjectValue U ℱ V) := by
  classical
  by_cases hV : unop V ≤ U
  · -- Inside `U`, the extension restriction map is literally the original identity restriction.
    have := ℱ.map_id (op (openSubsetPreimageOpen U (unop V)))
    simpa [openSubsetPresheafExtensionByInitialObjectMap,
      openSubsetPresheafExtensionByInitialObjectValue_eq_of_le, hV] using this
  · -- Outside `U`, the source object is identified with the initial object.
    simpa [openSubsetPresheafExtensionByInitialObjectMap, hV] using
      eqToHom_comp_initial_to_eq_id
        (openSubsetPresheafExtensionByInitialObjectValue_eq_of_not_le U ℱ hV)

-- Proof sketch: split into the inside/outside cases for the three opens. The inside branch is
-- exactly `ℱ.map_comp`, and the outside branches are forced by uniqueness of maps from the initial
-- object.
/-- The restriction maps in presheaf extension by the initial object satisfy the composition law.
-/
public theorem openSubsetPresheafExtensionByInitialObject_map_comp
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W Z : (Opens X)ᵒᵖ} (i : V ⟶ W) (j : W ⟶ Z) :
    openSubsetPresheafExtensionByInitialObjectMap U ℱ (i ≫ j) =
      openSubsetPresheafExtensionByInitialObjectMap U ℱ i ≫
        openSubsetPresheafExtensionByInitialObjectMap U ℱ j := by
  classical
  by_cases hV : unop V ≤ U
  · have hW : unop W ≤ U := le_trans i.unop.le hV
    have hZ : unop Z ≤ U := le_trans j.unop.le hW
    -- Once every ambient open lies in `U`, this is exactly functoriality of `ℱ`.
    simpa [openSubsetPresheafExtensionByInitialObjectMap,
      openSubsetPresheafExtensionByInitialObjectValue_eq_of_le, hV, hW, hZ] using
      ℱ.map_comp ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op
        ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map j.unop).op
  · -- If the source open is outside `U`, both sides are the unique map from the initial object.
    simpa [openSubsetPresheafExtensionByInitialObjectMap,
      openSubsetPresheafExtensionByInitialObjectValue_eq_of_not_le, hV] using
      (initial.hom_ext
        (openSubsetPresheafExtensionByInitialObjectMap U ℱ (i ≫ j))
        (openSubsetPresheafExtensionByInitialObjectMap U ℱ i ≫
          openSubsetPresheafExtensionByInitialObjectMap U ℱ j))

/-- The ambient presheaf underlying extension by the initial object along `U ↪ X`. -/
noncomputable def openSubsetPresheafExtensionByInitialObjectOnAmbient
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) : X.Presheaf C where
  obj := openSubsetPresheafExtensionByInitialObjectValue U ℱ
  map := fun i ↦ openSubsetPresheafExtensionByInitialObjectMap U ℱ i
  map_id := openSubsetPresheafExtensionByInitialObject_map_id U ℱ
  map_comp := openSubsetPresheafExtensionByInitialObject_map_comp U ℱ

-- Proof sketch: unfold the defining `if` and evaluate the inside branch `V ⊆ U`.
/-- Over an ambient open contained in `U`, extension by the initial object recovers the original
section object on the corresponding open of the subspace. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (h : unop V ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj V =
      ℱ.obj (op (openSubsetPreimageOpen U (unop V))) := by
  -- This is the defining inside branch of the ambient construction.
  simp [openSubsetPresheafExtensionByInitialObjectOnAmbient,
    openSubsetPresheafExtensionByInitialObjectValue, h]

-- Proof sketch: unfold the defining `if` and evaluate the outside branch `V ⊈ U`.
/-- Over an ambient open not contained in `U`, extension by the initial object takes the initial
value. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V : (Opens X)ᵒᵖ} (h : ¬ unop V ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj V = ⊥_ C := by
  -- This is the defining outside branch of the ambient construction.
  simp [openSubsetPresheafExtensionByInitialObjectOnAmbient,
    openSubsetPresheafExtensionByInitialObjectValue, h]

/-- On opens `W ⊆ V ⊆ U`, the restriction map of extension by the initial object is the original
restriction map of `ℱ`, up to the canonical identifications of the section objects. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : unop V ≤ U) (hW : unop W ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
        ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hW).symm := by
  -- On the inside branch, the explicit ambient map is definitionally the original restriction.
  simpa [openSubsetPresheafExtensionByInitialObjectOnAmbient,
    openSubsetPresheafExtensionByInitialObjectMap,
    openSubsetPresheafExtensionByInitialObjectValue_eq_of_le, hV, hW]

/-- If `V` is not contained in `U`, then the restriction map out of `V` in extension by the
initial object is the unique map from the initial object. -/
theorem openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : ¬ unop V ≤ U) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
        initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj W) := by
  -- Outside `U`, the source object is initial, so every restriction is the canonical map out.
  simpa [openSubsetPresheafExtensionByInitialObjectOnAmbient,
    openSubsetPresheafExtensionByInitialObjectMap,
    openSubsetPresheafExtensionByInitialObjectValue_eq_of_not_le, hV]

/-- The objectwise map induced by a morphism of presheaves under extension by the initial object.
-/
noncomputable def openSubsetPresheafExtensionByInitialObjectHomApp
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj V ⟶
      (openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V := by
  classical
  by_cases hV : unop V ≤ U
  · simpa [openSubsetPresheafExtensionByInitialObjectOnAmbient,
      openSubsetPresheafExtensionByInitialObjectValue, hV] using
        η.app (op (openSubsetPreimageOpen U (unop V)))
  · simpa [openSubsetPresheafExtensionByInitialObjectOnAmbient,
      openSubsetPresheafExtensionByInitialObjectValue, hV] using
        (initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V))

/-- On opens contained in `U`, a morphism of presheaves acts through the original component of
the morphism. -/
theorem openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) (hV : unop V ≤ U) :
    openSubsetPresheafExtensionByInitialObjectHomApp U η V =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
        η.app (op (openSubsetPreimageOpen U (unop V))) ≫
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV).symm := by
  classical
  -- On the inside branch, the only work is to normalize the dependent cast on the component.
  simp only [openSubsetPresheafExtensionByInitialObjectHomApp, hV]
  simpa using
    cast_hom_eqToHom_comp_eqToHom
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV)
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U 𝒢 hV)
      (η.app (op (openSubsetPreimageOpen U (unop V))))

/-- Outside `U`, the component of a morphism of extension-by-initial-object presheaves is the
unique map from the initial object. -/
theorem openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_not_le
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    (V : (Opens X)ᵒᵖ) (hV : ¬ unop V ≤ U) :
    openSubsetPresheafExtensionByInitialObjectHomApp U η V =
      eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
        initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V) := by
  classical
  -- Outside `U`, the component is the unique map from the initial object after source transport.
  simp only [openSubsetPresheafExtensionByInitialObjectHomApp, hV]
  simpa using
    cast_hom_eqToHom_comp_eqToHom
      (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV)
      rfl
      (initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).obj V))

-- Proof sketch: on the inside branch this is the naturality square for `η` after pulling the
-- inclusion back to `U`; on the outside branch all maps factor uniquely through the initial
-- object.
/-- The objectwise maps induced by presheaf extension by the initial object are natural in the
ambient open. -/
private theorem openSubsetPresheafExtensionByInitialObjectHomApp_naturality
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢)
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i ≫
        openSubsetPresheafExtensionByInitialObjectHomApp U η W =
      openSubsetPresheafExtensionByInitialObjectHomApp U η V ≫
        (openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).map i := by
  classical
  by_cases hV : unop V ≤ U
  · have hW : unop W ≤ U := le_trans i.unop.le hV
    -- Inside `U`, the naturality square is inherited from the original morphism `η`.
    simpa [Category.assoc,
      openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le,
      openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le, hV, hW] using
      η.naturality ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op
  · -- Outside `U`, both composites are maps from the initial object.
    simpa [Category.assoc,
      openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le,
      openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_not_le, hV] using
      (initial.hom_ext
        ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).map i ≫
          openSubsetPresheafExtensionByInitialObjectHomApp U η W)
        (openSubsetPresheafExtensionByInitialObjectHomApp U η V ≫
          (openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢).map i))

/-- The morphism of ambient presheaves induced by a morphism on the open subspace `U`. -/
noncomputable def openSubsetPresheafExtensionByInitialObjectHom
    (U : Opens X) {ℱ 𝒢 : (extensionByZeroOpenSubsetSpace U).Presheaf C} (η : ℱ ⟶ 𝒢) :
    openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ ⟶
      openSubsetPresheafExtensionByInitialObjectOnAmbient U 𝒢 where
  app := openSubsetPresheafExtensionByInitialObjectHomApp U η
  naturality := by
    intro V W i
    exact openSubsetPresheafExtensionByInitialObjectHomApp_naturality U η i

-- Proof sketch: check objectwise that on each ambient open the induced morphism is the identity
-- on the original section object or on the initial object.
/-- Extension by the initial object preserves identity morphisms of presheaves. -/
public theorem openSubsetPresheafExtensionByInitialObject_functor_map_id
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf C) :
    openSubsetPresheafExtensionByInitialObjectHom U (𝟙 ℱ) =
      𝟙 (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ) := by
  ext V
  classical
  by_cases hV : V ≤ U
  · -- Inside `U`, the component is the original identity component.
    have hApp :
        (openSubsetPresheafExtensionByInitialObjectHom U (𝟙 ℱ)).app (op V) =
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
            CategoryTheory.NatTrans.app (𝟙 ℱ) (op (openSubsetPreimageOpen U V)) ≫
              eqToHom
                (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV).symm := by
      -- The specialized component formula rewrites the identity natural transformation objectwise.
      simpa [openSubsetPresheafExtensionByInitialObjectHom] using
        (openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le U (𝟙 ℱ) (op V) hV)
    calc
      (openSubsetPresheafExtensionByInitialObjectHom U (𝟙 ℱ)).app (op V)
          = eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
              CategoryTheory.NatTrans.app (𝟙 ℱ) (op (openSubsetPreimageOpen U V)) ≫
                eqToHom
                  (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV).symm := by
            exact hApp
      _ = 𝟙 ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj (op V)) := by
            change eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV) ≫
                𝟙 (ℱ.obj (op (openSubsetPreimageOpen U V))) ≫
                  eqToHom
                    (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV).symm =
              𝟙 ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj (op V))
            simp
      _ =
          CategoryTheory.NatTrans.app
            (𝟙 (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ)) (op V) := by
            rfl
  · -- Outside `U`, the component is the identity on the initial object.
    have hApp :
        (openSubsetPresheafExtensionByInitialObjectHom U (𝟙 ℱ)).app (op V) =
          eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
            initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj (op V)) := by
      -- The outside branch is the canonical map from the initial object, now specialized to `𝟙 ℱ`.
      simpa [openSubsetPresheafExtensionByInitialObjectHom] using
        (openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_not_le U (𝟙 ℱ) (op V) hV)
    calc
      (openSubsetPresheafExtensionByInitialObjectHom U (𝟙 ℱ)).app (op V)
          = eqToHom (openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV) ≫
              initial.to ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj (op V)) := by
            exact hApp
      _ = 𝟙 ((openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ).obj (op V)) := by
            simp
      _ =
          CategoryTheory.NatTrans.app
            (𝟙 (openSubsetPresheafExtensionByInitialObjectOnAmbient U ℱ)) (op V) := by
            rfl

-- Proof sketch: verify the claim objectwise; on opens contained in `U` this is functoriality of
-- the original natural transformations, while outside `U` all components are the unique maps out
-- of the initial object.
/-- Extension by the initial object preserves composition of presheaf morphisms. -/
public theorem openSubsetPresheafExtensionByInitialObject_functor_map_comp
    (U : Opens X) {ℱ 𝒢 ℋ : (extensionByZeroOpenSubsetSpace U).Presheaf C}
    (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    openSubsetPresheafExtensionByInitialObjectHom U (η ≫ θ) =
      openSubsetPresheafExtensionByInitialObjectHom U η ≫
        openSubsetPresheafExtensionByInitialObjectHom U θ := by
  ext V
  classical
  by_cases hV : V ≤ U
  · -- On opens inside `U`, this is objectwise composition of the original morphisms.
    simp [openSubsetPresheafExtensionByInitialObjectHom,
      openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le, hV, Category.assoc]
  · -- Outside `U`, every component is the unique map from the initial object.
    simpa [openSubsetPresheafExtensionByInitialObjectHom,
      openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_not_le, hV, Category.assoc] using
      (initial.hom_ext
        (openSubsetPresheafExtensionByInitialObjectHomApp U (η ≫ θ) (op V))
        (openSubsetPresheafExtensionByInitialObjectHomApp U η (op V) ≫
          openSubsetPresheafExtensionByInitialObjectHomApp U θ (op V)))

/-- Extension by zero / by the initial object: for an open immersion `j : U ↪ X`, the presheaf
functor `j_{p!}` sends an ambient open `V` to the original section object on `V` when `V ⊆ U`,
and otherwise to the initial object of `C`. -/
noncomputable def openSubsetPresheafExtensionByInitialObject
    (U : Opens X) : (extensionByZeroOpenSubsetSpace U).Presheaf C ⥤ X.Presheaf C where
  obj := openSubsetPresheafExtensionByInitialObjectOnAmbient U
  map := fun η ↦ openSubsetPresheafExtensionByInitialObjectHom U η
  map_id := openSubsetPresheafExtensionByInitialObject_functor_map_id U
  map_comp := openSubsetPresheafExtensionByInitialObject_functor_map_comp U

variable [CategoryTheory.HasWeakSheafify (Opens.grothendieckTopology X) C]

/-- Sheaf-level extension by the initial object along `U ↪ X`, obtained by sheafifying the
presheaf-level construction. -/
noncomputable def openSubsetSheafExtensionByInitialObject
    (U : Opens X) : (extensionByZeroOpenSubsetSpace U).Sheaf C ⥤ X.Sheaf C :=
  TopCat.Sheaf.forget C (extensionByZeroOpenSubsetSpace U) ⋙
    openSubsetPresheafExtensionByInitialObject U ⋙
    CategoryTheory.presheafToSheaf (Opens.grothendieckTopology X) C

end

notation:max "jₚ! " U:max =>
  openSubsetPresheafExtensionByInitialObject U

notation:max "j! " U:max =>
  openSubsetSheafExtensionByInitialObject U

section Modules

variable {X : TopCat.{u}}

abbrev openSubsetAbelianPresheafExtensionByZero
    (U : Opens X) :
    (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u} ⥤
      X.Presheaf AddCommGrpCat.{u} :=
  openSubsetPresheafExtensionByInitialObject U

theorem openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj V =
      ℱ.obj (op (openSubsetPreimageOpen U V.unop)) := by
  simpa [openSubsetAbelianPresheafExtensionByZero] using
    openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_le U ℱ hV

theorem openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : ¬ V.unop ≤ U) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj V = ⊥_ AddCommGrpCat.{u} := by
  simpa [openSubsetAbelianPresheafExtensionByZero] using
    openSubsetPresheafExtensionByInitialObjectOnAmbient_obj_eq_of_not_le U ℱ hV

public instance : Subsingleton (⊥_ AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero initialIsInitial.isZero

public instance : Subsingleton (0 : AddCommGrpCat.{u}) :=
  AddCommGrpCat.subsingleton_of_isZero (isZero_zero _)

noncomputable instance openSubsetModuleExtensionByZeroObj_module
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) (V : (Opens X)ᵒᵖ) :
    Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) := by
  classical
  by_cases hV : V.unop ≤ U
  · let αV : 𝒪X.obj V ⟶ 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) := by
      simpa using α.app V
    letI : Module (𝒪X.obj V) (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :=
      Module.compHom (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) αV.hom
    rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV]
    infer_instance
  · rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ.presheaf hV]
    exact
      { smul := fun _ _ ↦ 0
        one_smul := fun _ ↦ Subsingleton.elim _ _
        mul_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        smul_zero := fun _ ↦ Subsingleton.elim _ _
        smul_add := fun _ _ _ ↦ Subsingleton.elim _ _
        add_smul := fun _ _ _ ↦ Subsingleton.elim _ _
        zero_smul := fun _ ↦ Subsingleton.elim _ _ }

/-- Helper for Extension by zero / by the initial object: on `AddCommGrpCat`, the underlying
function of an `eqToHom` transport is the corresponding carrier cast. -/
@[simp] private theorem addCommGrp_eqToHom_apply_eq_cast
    {A B : AddCommGrpCat.{u}} (h : A = B) (x : A) :
    CategoryTheory.ConcreteCategory.hom (eqToHom h) x =
      cast (by
        cases h
        rfl) x := by
  -- Once the object equality is reflexive, both sides are the identity function.
  cases h
  rfl

/-- Helper for Extension by zero / by the initial object: on the inside branch, the canonical
transport from the additive extension object to the original section object acts as the identity
on underlying elements. -/
@[simp] private theorem openSubsetAbelianPresheafExtensionByZero_eqToHom_apply_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U)
    (m : ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj V) :
    CategoryTheory.ConcreteCategory.hom
        (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV)) m =
      cast (by
        rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV]) m := by
  -- Specialize the generic carrier-level transport lemma to the inside-branch equality.
  simpa using
    addCommGrp_eqToHom_apply_eq_cast
      (h := openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV)
      m

/-- Helper for Extension by zero / by the initial object: on the inside branch, the inverse
transport back to the additive extension object also acts as the identity on underlying elements.
-/
@[simp] private theorem openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_apply_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U)
    (m : ℱ.obj (op (openSubsetPreimageOpen U V.unop))) :
    CategoryTheory.ConcreteCategory.hom
        (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV).symm) m =
      cast (by
        rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV]) m := by
  -- The inverse transport is the same carrier cast specialized to the inverse equality.
  simpa using
    addCommGrp_eqToHom_apply_eq_cast
      (h := (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV).symm)
      m

/-- Helper for Extension by zero / by the initial object: the inside-branch object equality
induces the corresponding equality of underlying additive carriers. -/
private theorem openSubsetAbelianPresheafExtensionByZero_obj_carrier_eq_of_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    ↥(((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj V) =
      ↥(ℱ.obj (op (openSubsetPreimageOpen U V.unop))) := by
  -- This is the carrier-level form of the inside-branch object identification.
  simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A)
    (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ hV)

/-- Helper for Extension by zero / by the initial object: casting along an equality of additive
group objects turns the source `Module.compHom` scalar action into the visible target scalar
action. -/
@[simp] private theorem cast_compHom_smul_of_eq
    {R S : Type u} [Semiring R] [Semiring S]
    {A B : AddCommGrpCat.{u}} (h : A = B) [Module S B] (f : R →+* S)
    (r : R) (a : A) :
    letI : Module R A := by
      cases h
      simpa using (Module.compHom A f)
    cast (congrArg (fun T : AddCommGrpCat.{u} => ↥T) h) (r • a) =
      (f r) • cast (congrArg (fun T : AddCommGrpCat.{u} => ↥T) h) a := by
  -- After the object equality becomes reflexive, the transported source action is definitionally
  -- the restricted-scalar action coming from `Module.compHom`.
  cases h
  rfl

/-- Helper for Extension by zero / by the initial object: casting back along the symmetric
equality of additive group objects restores the source `Module.compHom` scalar action. -/
@[simp] private theorem cast_compHom_smul_symm_of_eq
    {R S : Type u} [Semiring R] [Semiring S]
    {A B : AddCommGrpCat.{u}} (h : A = B) [Module S B] (f : R →+* S)
    (r : R) (b : B) :
    letI : Module R A := by
      cases h
      simpa using (Module.compHom A f)
    cast (congrArg (fun T : AddCommGrpCat.{u} => ↥T) h.symm) ((f r) • b) =
      r • cast (congrArg (fun T : AddCommGrpCat.{u} => ↥T) h.symm) b := by
  -- The inverse carrier cast reduces to the same reflexive computation after eliminating `h`.
  cases h
  rfl

/-- Helper for Extension by zero / by the initial object: an equality of additive group objects
induces the corresponding equality of module-structure types. -/
private theorem module_type_eq_of_addCommGrp_eq
    {R : Type u} [Semiring R] {A B : AddCommGrpCat.{u}} (h : A = B) :
    Module R A = Module R B := by
  -- Reducing the object equality to reflexivity also identifies the corresponding module types.
  cases h
  rfl

/-- Helper for Extension by zero / by the initial object: if the source module structure is the
explicit cast of a `Module.compHom` structure along an object equality, then the carrier cast
respects scalar multiplication. -/
private theorem cast_casted_compHom_smul_of_eq
    {R S : Type u} [Semiring R] [Semiring S]
    {A B : AddCommGrpCat.{u}} (h : A = B) [Module S B] (f : R →+* S)
    (r : R) (a : A) :
    let transportType : Module R A = Module R B := module_type_eq_of_addCommGrp_eq (R := R) h
    let transportInst : Module R A := cast transportType.symm (Module.compHom B f)
    cast (congrArg (fun T : AddCommGrpCat.{u} => ↥T) h)
      (@SMul.smul _ _ transportInst.toSMul r a) =
      (f r) • cast (congrArg (fun T : AddCommGrpCat.{u} => ↥T) h) a := by
  -- Once the object equality is reflexive, both the casted module structure and the carrier cast
  -- reduce to the ordinary `Module.compHom` action.
  cases h
  rfl

/-- Helper for Extension by zero / by the initial object: on the inside branch, the carrier cast
from the additive extension object to the original section object respects the restricted scalar
action induced by `α.app V`. -/
theorem openSubsetModuleExtensionByZeroObj_module_eq_compHom_of_le
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    openSubsetModuleExtensionByZeroObj_module U α ℱ V =
      (by
        let αV : 𝒪X.obj V ⟶ 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) := by
          simpa using α.app V
        letI : Module (𝒪X.obj V) (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :=
          Module.compHom (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) αV.hom
        rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV]
        infer_instance) := by
  -- Unfold the inside branch of the instance definition and expose the `Module.compHom` action.
  simp [openSubsetModuleExtensionByZeroObj_module, hV]

/-- Helper for Extension by zero / by the initial object: equal module structures induce the same
scalar action on a fixed additive carrier. -/
private theorem openSubsetModuleExtensionByZeroObj_smul_congr_of_module_eq
    {R M : Type u} [Semiring R] [AddCommMonoid M]
    (inst₁ inst₂ : Module R M) (hmod : inst₁ = inst₂) (r : R) (m : M) :
    @SMul.smul R M inst₁.toSMul r m = @SMul.smul R M inst₂.toSMul r m := by
  -- Once the module structures agree, their scalar actions are definitionally identical.
  cases hmod
  rfl

/-- Helper for Extension by zero / by the initial object: on the inside branch, the additive
extension object equality can be obtained directly by simplifying the defining `if`. -/
private theorem openSubsetModuleExtensionByZeroObj_obj_eq_of_le_by_simp
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    (ℱ : PresheafOfModules 𝒪U)
    {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V =
      ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop)) := by
  -- This is the inside branch of the `if` defining the additive extension object.
  simpa [openSubsetAbelianPresheafExtensionByZero,
    openSubsetPresheafExtensionByInitialObject,
    openSubsetPresheafExtensionByInitialObjectOnAmbient,
    openSubsetPresheafExtensionByInitialObjectValue, hV]

/-- Helper for Extension by zero / by the initial object: casts along propositionally equal proof
witnesses coincide. -/
@[simp] private theorem cast_eq_of_proof_irrel_eq
    {α β : Sort u} (p q : α = β) (x : α) :
    cast p x = cast q x := by
  -- Equality proofs are subsingletons, so the two casts agree.
  cases Subsingleton.elim p q
  rfl

/-- Helper for Extension by zero / by the initial object: on the inside branch, the carrier cast
from the additive extension object to the original section object respects the restricted scalar
action induced by `α.app V`. -/
private theorem openSubsetModuleExtensionByZeroObj_cast_smul_eq_of_le
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) (r : 𝒪X.obj V)
    (m : ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
    cast (by
      simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A)
        (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV)) (r • m) =
      (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
        cast (by
          simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A)
            (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV)) m := by
  -- Route correction: compare the explicit inside-branch module instance with the theorem-local
  -- transport instance that mirrors the cast-smul normalization proof, and rewrite the scalar
  -- action across that equality.
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
  let f : 𝒪X.obj V →+* 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) :=
    (show 𝒪X.obj V ⟶ 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V).hom
  let instCurrent : Module (𝒪X.obj V)
      (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) := by
    let αV : 𝒪X.obj V ⟶ 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) := by
      simpa using α.app V
    letI : Module (𝒪X.obj V) (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :=
      Module.compHom (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) αV.hom
    rw [openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV]
    infer_instance
  have hobj0 :
      ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V =
        ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop)) := by
    exact openSubsetModuleExtensionByZeroObj_obj_eq_of_le_by_simp U ℱ hV
  have htransportType :
      Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) =
        Module (𝒪X.obj V) (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :=
    module_type_eq_of_addCommGrp_eq (R := 𝒪X.obj V) hobj0
  let transportInst : Module (𝒪X.obj V)
      (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :=
    cast htransportType.symm
      (Module.compHom (ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) f)
  have hinstCurrent :
      openSubsetModuleExtensionByZeroObj_module U α ℱ V = instCurrent := by
    exact openSubsetModuleExtensionByZeroObj_module_eq_compHom_of_le U α ℱ hV
  have hsmul :
      @SMul.smul _ _ (openSubsetModuleExtensionByZeroObj_module U α ℱ V).toSMul r m =
        @SMul.smul _ _ transportInst.toSMul r m := by
    calc
      @SMul.smul _ _ (openSubsetModuleExtensionByZeroObj_module U α ℱ V).toSMul r m
          = @SMul.smul _ _ instCurrent.toSMul r m := by
              exact
                openSubsetModuleExtensionByZeroObj_smul_congr_of_module_eq
                  (openSubsetModuleExtensionByZeroObj_module U α ℱ V) instCurrent
                  hinstCurrent r m
      _ = @SMul.smul _ _ transportInst.toSMul r m := by
            -- Once the transport instance is written as an explicit cast of `Module.compHom`,
            -- the scalar action agrees with the inside-branch instance after reducing `hobj0`.
            rfl
  calc
    cast (by simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A) hobj0)
        (@SMul.smul _ _ (openSubsetModuleExtensionByZeroObj_module U α ℱ V).toSMul r m)
      = cast (by simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A) hobj0)
          (@SMul.smul _ _ transportInst.toSMul r m) := by
            exact
              congrArg
                (cast (by simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A) hobj0)) hsmul
    _ = (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
          cast (by simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A) hobj0) m := by
            letI : Module (𝒪X.obj V)
                (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :=
              transportInst
            -- The rewritten goal now uses the same theorem-local transport instance as the
            -- normalized `Module.compHom` scalar action.
            simpa [transportInst, htransportType, f] using
              (cast_casted_compHom_smul_of_eq (h := hobj0) (f := f) (r := r) (a := m))

/-- Helper for Extension by zero / by the initial object: on the inside branch, the inverse
carrier cast back to the additive extension object also respects the restricted scalar action. -/
private theorem openSubsetModuleExtensionByZeroObj_cast_smul_symm_eq_of_le
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) (r : 𝒪X.obj V)
    (m : ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
    cast (by
      simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A)
        (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV).symm)
      ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) • m) =
      r • cast (by
        simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A)
          (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV).symm) m := by
  -- Route correction: derive the inverse transport by applying the forward inside-branch lemma
  -- to the cast-back element and then transporting the resulting equality back along `hV`.
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
  let hcarrier :
      ↥(((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) =
        ↥(ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) := by
    simpa using congrArg (fun A : AddCommGrpCat.{u} => ↥A)
      (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV)
  have hforward :=
    openSubsetModuleExtensionByZeroObj_cast_smul_eq_of_le U α ℱ hV r (cast hcarrier.symm m)
  have hback := congrArg (cast hcarrier.symm) hforward
  simpa [hcarrier, eq_comm] using hback

/-- Helper for Extension by zero / by the initial object: after identifying the inside branch of
the additive extension with the original section object, the transported scalar action is the
restricted-scalar action coming from `α.app V`. -/
theorem openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) (r : 𝒪X.obj V)
    (m : ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
    eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV) (r • m) =
      (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV) m := by
  -- Rewrite `eqToHom` to the carrier cast and then use the dedicated cast-scalar lemma.
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
  rw [openSubsetAbelianPresheafExtensionByZero_eqToHom_apply_of_le U ℱ.presheaf hV (r • m)]
  rw [openSubsetAbelianPresheafExtensionByZero_eqToHom_apply_of_le U ℱ.presheaf hV m]
  exact openSubsetModuleExtensionByZeroObj_cast_smul_eq_of_le U α ℱ hV r m

/-- Helper for Extension by zero / by the initial object: the inverse inside-branch transport also
commutes with the restricted scalar action induced from `α.app V`. -/
theorem openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_smul_of_le
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) {V : (Opens X)ᵒᵖ} (hV : V.unop ≤ U) (r : 𝒪X.obj V)
    (m : ℱ.presheaf.obj (op (openSubsetPreimageOpen U V.unop))) :
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
    eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV).symm
        ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) • m) =
      r • eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV).symm m := by
  -- Rewrite the inverse transport to the carrier cast and use the inverse cast-scalar lemma.
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
  rw [openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_apply_of_le U ℱ.presheaf hV
    ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) • m)]
  rw [openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_apply_of_le U ℱ.presheaf hV m]
  exact openSubsetModuleExtensionByZeroObj_cast_smul_symm_eq_of_le U α ℱ hV r m

/-- Helper for Extension by zero / by the initial object: if the source ambient open is not
contained in `U`, the additive extension restriction map is the zero morphism. -/
private theorem openSubsetAbelianPresheafExtensionByZero_map_eq_zero_of_not_le
    (U : Opens X) (ℱ : (extensionByZeroOpenSubsetSpace U).Presheaf AddCommGrpCat.{u})
    {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : ¬ V.unop ≤ U) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).map i = 0 := by
  -- Outside `U`, the map is the unique map out of the zero object, hence the zero morphism.
  rw [show ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).map i =
      eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ hV) ≫
        initial.to (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ).obj W) by
      simpa [openSubsetAbelianPresheafExtensionByZero] using
        openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_not_le
          (C := AddCommGrpCat.{u}) U ℱ i hV]
  simp

/-- Helper for Extension by zero / by the initial object: on opens contained in `U`, the
restriction map in the additive extension presheaf is semilinear for the module structure obtained
by restricting scalars along `α`. -/
private theorem openSubsetModuleExtensionByZero_inside_map_smul
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) (hV : V.unop ≤ U)
    (hW : W.unop ≤ U)
    (r : 𝒪X.obj V)
    (m : ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ W
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).map i (r • m) =
      (𝒪X.map i) r • ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).map i m := by
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ W
  -- Route correction: first expose the inside-branch restriction map as the original presheaf
  -- restriction up to the canonical `eqToHom` transports.
  have hi :
      ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).map i =
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV) ≫
          ℱ.presheaf.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op ≫
            eqToHom
              (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hW).symm := by
    simpa [openSubsetAbelianPresheafExtensionByZero] using
      openSubsetPresheafExtensionByInitialObjectOnAmbient_map_eq_of_le
        (C := AddCommGrpCat.{u}) U ℱ.presheaf i hV hW
  have hα :
      𝒪U.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op
          (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) =
        (show 𝒪U.obj (op (openSubsetPreimageOpen U W.unop)) from α.app W ((𝒪X.map i) r)) := by
    -- Naturality of `α` aligns the transported scalar with the target restricted-scalar action.
    simpa using (CategoryTheory.congr_fun (α.naturality i).symm r)
  rw [hi]
  -- Evaluate the composite pointwise, move the source scalar through the first transport, and
  -- then use semilinearity of the original restriction map on `ℱ`.
  simp only [CategoryTheory.comp_apply]
  rw [openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U α ℱ hV r m]
  have hmap_smul :
      CategoryTheory.ConcreteCategory.hom
          (ℱ.presheaf.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)
          ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
            CategoryTheory.ConcreteCategory.hom
              (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV)) m) =
        𝒪U.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op
            (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
          (show ℱ.presheaf.obj (op (openSubsetPreimageOpen U W.unop)) from
            CategoryTheory.ConcreteCategory.hom
              (ℱ.presheaf.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)
              (CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m)) := by
    -- This is the original semilinearity statement of the restriction map of `ℱ`.
    change (ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op).hom
        ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
          CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
            m) =
      𝒪U.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op
          (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
        (ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op).hom
          (CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
            m)
    exact
      (ℱ.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op).hom.map_smul
        (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r)
        (CategoryTheory.ConcreteCategory.hom
          (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
          m)
  rw [hmap_smul]
  rw [hα]
  -- Finally, move the target scalar back across the inverse transport on the inside branch.
  simpa [CategoryTheory.comp_apply] using
    (openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_smul_of_le U α ℱ hW
      ((𝒪X.map i) r)
      (CategoryTheory.ConcreteCategory.hom
        (ℱ.presheaf.map ((Opens.map (extensionByZeroOpenSubsetInclusion U)).map i.unop).op)
        (CategoryTheory.ConcreteCategory.hom
          (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
          m)))


noncomputable def openSubsetModuleExtensionByZeroObj
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) :
    PresheafOfModules 𝒪X :=
  letI : ∀ V : (Opens X)ᵒᵖ,
      Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :=
    fun V ↦ openSubsetModuleExtensionByZeroObj_module U α ℱ V
  PresheafOfModules.ofPresheaf
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf)
    (by
      intro V W i r m
      classical
      by_cases hV : V.unop ≤ U
      · have hW : W.unop ≤ U := le_trans i.unop.le hV
        -- Inside `U`, semilinearity is the dedicated scalar-transport lemma above.
        exact openSubsetModuleExtensionByZero_inside_map_smul U α ℱ i hV hW r m
      · -- Outside `U`, the restriction map is zero, so both sides reduce by `map_zero` and
        -- `smul_zero`.
        rw [openSubsetAbelianPresheafExtensionByZero_map_eq_zero_of_not_le U ℱ.presheaf i hV]
        simp)

public noncomputable def openSubsetModuleExtensionByZeroHomApp
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V ⟶
      ((openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf).obj V := by
  let _ := α
  classical
  by_cases hV : V.unop ≤ U
  · exact
      eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV) ≫
        ((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)) ≫
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm
  · exact
      eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U ℱ.presheaf hV) ≫
        0 ≫
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_not_le U 𝒢.presheaf hV).symm

/-- Helper for Extension by zero / by the initial object: forgetting the module structure, the
component of the module-valued extension-by-zero morphism is the presheaf-level extension
component for the underlying additive natural transformation. -/
public theorem openSubsetModuleExtensionByZeroHomApp_eq_presheafHomApp
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) :
    openSubsetModuleExtensionByZeroHomApp U α η V =
      openSubsetPresheafExtensionByInitialObjectHomApp U ((PresheafOfModules.toPresheaf _).map η) V := by
  let _ := α
  classical
  by_cases hV : V.unop ≤ U
  · -- Inside `U`, both constructions are the same transported component of `η`.
    simpa [openSubsetModuleExtensionByZeroHomApp, openSubsetAbelianPresheafExtensionByZero, hV] using
      (openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_le
        U ((PresheafOfModules.toPresheaf _).map η) V hV).symm
  · -- Outside `U`, both constructions are the unique map between zero objects.
    simpa [openSubsetModuleExtensionByZeroHomApp, openSubsetAbelianPresheafExtensionByZero, hV] using
      (openSubsetPresheafExtensionByInitialObjectHomApp_eq_of_not_le
        U ((PresheafOfModules.toPresheaf _).map η) V hV).symm

/-- Helper for Extension by zero / by the initial object: each component of the module-valued
extension-by-zero morphism is linear for the restricted scalar action coming from `α`. -/
public theorem openSubsetModuleExtensionByZeroHomApp_map_smul
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) (V : (Opens X)ᵒᵖ) (r : 𝒪X.obj V)
    (m : ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :
    letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
    letI := openSubsetModuleExtensionByZeroObj_module U α 𝒢 V
    openSubsetModuleExtensionByZeroHomApp U α η V (r • m) =
      r • openSubsetModuleExtensionByZeroHomApp U α η V m := by
  classical
  letI := openSubsetModuleExtensionByZeroObj_module U α ℱ V
  letI := openSubsetModuleExtensionByZeroObj_module U α 𝒢 V
  by_cases hV : V.unop ≤ U
  · -- Inside `U`, move the source scalar through the transport, apply linearity of `η.app`, and
    -- transport the target scalar back.
    have hη :
        openSubsetModuleExtensionByZeroHomApp U α η V =
        eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV) ≫
          ((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)) ≫
            eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm := by
      simp [openSubsetModuleExtensionByZeroHomApp, hV]
    rw [hη]
    -- Normalize the source scalar, apply linearity of `η.app`, and then transport the target
    -- scalar back to the additive extension object.
    simp only [CategoryTheory.comp_apply]
    rw [openSubsetAbelianPresheafExtensionByZero_eqToHom_smul_of_le U α ℱ hV r m]
    have hη_smul :
        CategoryTheory.ConcreteCategory.hom
            (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
            ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
              CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m) =
          (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
            (show 𝒢.presheaf.obj (op (openSubsetPreimageOpen U V.unop)) from
              CategoryTheory.ConcreteCategory.hom
                (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
                (CategoryTheory.ConcreteCategory.hom
                  (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                  m)) := by
      -- The underlying additive map is induced by the `𝒪U`-linear component `η.app _`.
      change (η.app (op (openSubsetPreimageOpen U V.unop))).hom
            ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
              CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m) =
          (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
            (η.app (op (openSubsetPreimageOpen U V.unop))).hom
              (CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m)
      exact
        (η.app (op (openSubsetPreimageOpen U V.unop))).hom.map_smul
          (show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r)
          (CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
            m)
    have htransport :
        CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm)
            (CategoryTheory.ConcreteCategory.hom
              (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
              ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
                CategoryTheory.ConcreteCategory.hom
                  (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                  m)) =
          CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm)
            ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
              (show 𝒢.presheaf.obj (op (openSubsetPreimageOpen U V.unop)) from
                CategoryTheory.ConcreteCategory.hom
                  (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
                  (CategoryTheory.ConcreteCategory.hom
                    (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                    m))) := by
      -- Apply the target transport functorially to the semilinearity statement for `η.app`.
      exact congrArg
        (CategoryTheory.ConcreteCategory.hom
          (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm))
        hη_smul
    calc
      CategoryTheory.ConcreteCategory.hom
          (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm)
          (CategoryTheory.ConcreteCategory.hom
            (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
            ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
              CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m)) =
          CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm)
            ((show 𝒪U.obj (op (openSubsetPreimageOpen U V.unop)) from α.app V r) •
              (show 𝒢.presheaf.obj (op (openSubsetPreimageOpen U V.unop)) from
                CategoryTheory.ConcreteCategory.hom
                  (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
                  (CategoryTheory.ConcreteCategory.hom
                    (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                    m))) := htransport
      _ = r •
          CategoryTheory.ConcreteCategory.hom
            (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U 𝒢.presheaf hV).symm)
            (CategoryTheory.ConcreteCategory.hom
              (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
              (CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m)) := by
        -- The inverse transport converts the restricted scalar back to the ambient scalar.
        simpa [CategoryTheory.comp_apply] using
          (openSubsetAbelianPresheafExtensionByZero_eqToHom_symm_smul_of_le U α 𝒢 hV r
            (CategoryTheory.ConcreteCategory.hom
              (((PresheafOfModules.toPresheaf _).map η).app (op (openSubsetPreimageOpen U V.unop)))
              (CategoryTheory.ConcreteCategory.hom
                (eqToHom (openSubsetAbelianPresheafExtensionByZero_obj_eq_of_le U ℱ.presheaf hV))
                m)))
  · -- Outside `U`, both the source and target objects are zero, so the statement is subsingleton.
    have hη0 : openSubsetModuleExtensionByZeroHomApp U α η V = 0 := by
      simp [openSubsetModuleExtensionByZeroHomApp, hV]
    rw [hη0]
    simp

public theorem openSubsetModuleExtensionByZeroHomApp_naturality
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) {V W : (Opens X)ᵒᵖ} (i : V ⟶ W) :
    ((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).map i ≫
        openSubsetModuleExtensionByZeroHomApp U α η W =
      openSubsetModuleExtensionByZeroHomApp U α η V ≫
        ((openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf).map i := by
  -- Rewrite the module-valued components to the additive presheaf extension components.
  rw [openSubsetModuleExtensionByZeroHomApp_eq_presheafHomApp U α η W,
    openSubsetModuleExtensionByZeroHomApp_eq_presheafHomApp U α η V]
  -- The remaining statement is exactly presheaf-level naturality.
  simpa [openSubsetAbelianPresheafExtensionByZero] using
    (openSubsetPresheafExtensionByInitialObjectHomApp_naturality U
      ((PresheafOfModules.toPresheaf _).map η) i)

public noncomputable def openSubsetModuleExtensionByZeroHom
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) :
    openSubsetModuleExtensionByZeroObj U α ℱ ⟶
      openSubsetModuleExtensionByZeroObj U α 𝒢 :=
  let φ :
      (openSubsetModuleExtensionByZeroObj U α ℱ).presheaf ⟶
        (openSubsetModuleExtensionByZeroObj U α 𝒢).presheaf := by
    simpa [openSubsetModuleExtensionByZeroObj] using
      ({ app := openSubsetModuleExtensionByZeroHomApp U α η
         naturality := fun {_ _} i ↦
           openSubsetModuleExtensionByZeroHomApp_naturality U α η i } :
        (openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf ⟶
          (openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf)
  PresheafOfModules.homMk φ
    (by
      intro V r m
      letI :
          Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj ℱ.presheaf).obj V) :=
        openSubsetModuleExtensionByZeroObj_module U α ℱ V
      letI :
          Module (𝒪X.obj V) (((openSubsetAbelianPresheafExtensionByZero U).obj 𝒢.presheaf).obj V) :=
        openSubsetModuleExtensionByZeroObj_module U α 𝒢 V
      -- The objectwise linearity was isolated so `homMk` only has to package it.
      simpa [openSubsetModuleExtensionByZeroObj] using
        openSubsetModuleExtensionByZeroHomApp_map_smul U α η V r m)

/-- Helper for Extension by zero / by the initial object: after forgetting the module structure,
the extension-by-zero morphism is the presheaf-level extension-by-initial-object morphism on the
underlying additive presheaves. -/
theorem openSubsetModuleExtensionByZeroHom_toPresheaf_eq
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) :
    (PresheafOfModules.toPresheaf 𝒪X).map (openSubsetModuleExtensionByZeroHom U α η) =
      openSubsetPresheafExtensionByInitialObjectHom U ((PresheafOfModules.toPresheaf _).map η) := by
  ext V x
  -- The component formula of `homMk` matches the presheaf-level extension component exactly.
  change openSubsetModuleExtensionByZeroHomApp U α η V x =
    openSubsetPresheafExtensionByInitialObjectHomApp U ((PresheafOfModules.toPresheaf _).map η) V x
  rw [openSubsetModuleExtensionByZeroHomApp_eq_presheafHomApp U α η V]
  rfl

public theorem openSubsetModuleExtensionByZero_functor_map_id
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    (ℱ : PresheafOfModules 𝒪U) :
    openSubsetModuleExtensionByZeroHom U α (𝟙 ℱ) =
      𝟙 (openSubsetModuleExtensionByZeroObj U α ℱ) := by
  -- Forgetting to additive presheaves is faithful, so the module-level identity law reduces to
  -- the already proved presheaf-level identity law.
  apply (PresheafOfModules.toPresheaf _).map_injective
  rw [openSubsetModuleExtensionByZeroHom_toPresheaf_eq U α (𝟙 ℱ)]
  simpa using openSubsetPresheafExtensionByInitialObject_functor_map_id U ℱ.presheaf

public theorem openSubsetModuleExtensionByZero_functor_map_comp
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U)
    {ℱ 𝒢 ℋ : PresheafOfModules 𝒪U} (η : ℱ ⟶ 𝒢) (θ : 𝒢 ⟶ ℋ) :
    openSubsetModuleExtensionByZeroHom U α (η ≫ θ) =
      openSubsetModuleExtensionByZeroHom U α η ≫
        openSubsetModuleExtensionByZeroHom U α θ := by
  -- Forgetting to additive presheaves is faithful, so composition is checked on the underlying
  -- extension-by-initial-object morphisms.
  apply (PresheafOfModules.toPresheaf _).map_injective
  rw [Functor.map_comp, openSubsetModuleExtensionByZeroHom_toPresheaf_eq U α η,
    openSubsetModuleExtensionByZeroHom_toPresheaf_eq U α θ,
    openSubsetModuleExtensionByZeroHom_toPresheaf_eq U α (η ≫ θ)]
  simpa using openSubsetPresheafExtensionByInitialObject_functor_map_comp
    U ((PresheafOfModules.toPresheaf _).map η) ((PresheafOfModules.toPresheaf _).map θ)

noncomputable def openSubsetModuleExtensionByZero
    (U : Opens X) {𝒪U : (extensionByZeroOpenSubsetSpace U).Presheaf RingCat.{u}}
    {𝒪X : X.Presheaf RingCat.{u}}
    (α : 𝒪X ⟶ (TopCat.Presheaf.pushforward RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪U) :
    PresheafOfModules 𝒪U ⥤ PresheafOfModules 𝒪X where
  obj := openSubsetModuleExtensionByZeroObj U α
  map := fun η ↦ openSubsetModuleExtensionByZeroHom U α η
  map_id := openSubsetModuleExtensionByZero_functor_map_id U α
  map_comp := openSubsetModuleExtensionByZero_functor_map_comp U α

/-- The presheaf-level extension-by-zero functor on modules along the open inclusion `U ↪ X`. -/
noncomputable abbrev openSubsetModulePresheafExtensionByZero
    (U : Opens X) (𝒪 : X.Presheaf RingCat.{u}) :
    PresheafOfModules ((TopCat.Presheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      PresheafOfModules 𝒪 :=
  openSubsetModuleExtensionByZero U
    ((TopCat.Presheaf.pullbackPushforwardAdjunction RingCat
      (extensionByZeroOpenSubsetInclusion U)).unit.app 𝒪)

/-- The sheaf-level extension-by-zero functor on modules along the open inclusion `U ↪ X`. -/
noncomputable abbrev openSubsetModuleSheafExtensionByZero
    (U : Opens X) (𝒪 : X.Sheaf RingCat.{u}) :
    SheafOfModules ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⥤
      SheafOfModules 𝒪 :=
  -- Route correction: the raw additive extension presheaf is not a sheaf in general, so the
  -- public module-valued functor is obtained by forgetting to presheaves of modules and then
  -- sheafifying over the ambient ring sheaf.
  SheafOfModules.forget
      ((TopCat.Sheaf.pullback RingCat (extensionByZeroOpenSubsetInclusion U)).obj 𝒪) ⋙
    openSubsetModuleExtensionByZero U
      ((TopCat.Sheaf.pullbackPushforwardAdjunction RingCat
        (extensionByZeroOpenSubsetInclusion U)).unit.app 𝒪).hom ⋙
    PresheafOfModules.sheafification (R := 𝒪) (R₀ := 𝒪.obj) (α := 𝟙 𝒪.obj)

end Modules
