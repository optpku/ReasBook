module

public import Mathlib
public import stacks_project.Chap04.Definition_4_39_3
public import stacks_project.Chap08.Definition_8_5_5
public import stacks_project.Chap08.Definition_8_6_1


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory
open Bicategory.InducedBicategory
open ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 8.6.5:
- primary domain: stacks in setoids over a fixed site, organized as a full owner subcategory of
  stacks in groupoids.
- inspected owner-level declarations:
  `StackOver`,
  `StackInGroupoidsOver`,
  `FibredInSetoidsOver`,
  `IsStackInSetoids`.
- best owner abstraction: the primitive owner datum here is an object of `StackInGroupoidsOver J`
  together with the additional fiberwise condition `IsFibredInSetoids X.p`; the stack condition is
  already part of the ambient owner, so it should be derived rather than stored again as
  primitive data.
- primitive data: a bundled stack in groupoids over `(C, J)` and a proof that its projection is
  fibred in setoids.
- derived API: coercions to `StackOver J`, `FibredInSetoidsOver C`, the induced owner
  instance `IsStackInSetoids J X.p`, and the owner-hom bridge surface from `X ⟶ Y` to the
  ambient owner-hom and `FibredCategoryMor`/based-functor APIs.

Source/core/bridge triage:
- `source-facing`: `StackInSetoidsOver J`.
- `core/canonical`: `StackInGroupoidsOver J`, `FibredInSetoidsOver C`, `IsFibredInSetoids`, and
  `IsStackInSetoids`.
- `bridge/view`: the forgetful coercions to stacks over `(C, J)` and to categories fibred in
  setoids over `C`, together with the canonical morphism bridge to the ambient setoid-stack
  morphism APIs. -/

/-- Definition 8.6.5 (1): the `2`-category of stacks in setoids over the site `(C, J)` is the full
sub-`2`-category of stacks in groupoids over `(C, J)` cut out by the additional owner predicate
`IsFibredInSetoids X.p`. Equivalently, it is the full sub-`2`-category of stacks over `(C, J)`
whose projection functor satisfies `IsStackInSetoids J X.p`. -/
abbrev stackInSetoidsOverSubTwoCategory (J : GrothendieckTopology C) :
    SubTwoCategory (StackInGroupoidsOver J) where
  obj := fun X ↦ IsFibredInSetoids X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

/-- The owner predicate for the canonical sub-`2`-category of stacks in setoids is exactly
`IsFibredInSetoids` on the projection functor. -/
-- Proof sketch: this is immediate from the defining object predicate of
-- `stackInSetoidsOverSubTwoCategory`.
theorem stackInSetoidsOverSubTwoCategory_obj_iff
    (J : GrothendieckTopology C) (X : StackInGroupoidsOver J) :
    (stackInSetoidsOverSubTwoCategory J).obj X ↔ IsFibredInSetoids X.p := by
  -- Unfold the owner predicate of the defining full sub-`2`-category.
  rfl

/-- Definition 8.6.5 (2): the objects of the canonical owner sub-`2`-category
`stackInSetoidsOverSubTwoCategory J` are stacks in setoids over `(C, J)`. -/
abbrev StackInSetoidsOver (J : GrothendieckTopology C) :=
  (stackInSetoidsOverSubTwoCategory J).Obj

namespace StackInSetoidsOver

variable {J : GrothendieckTopology C}
variable {D : Type (max u v)} [Category.{v} D]

/-- Bundle a projection `p : D ⥤ C` that is already known to be a stack in setoids over
`(C, J)`. -/
abbrev ofProjection (J : GrothendieckTopology C) (p : D ⥤ C) [IsStackInSetoids J p] :
    StackInSetoidsOver J :=
  ⟨StackInGroupoidsOver.ofProjection J p, by
    simpa [StackInGroupoidsOver.p, StackInGroupoidsOver.ofProjection] using
      (inferInstance : IsFibredInSetoids p)⟩

/-- The underlying stack in groupoids over `(C, J)`. -/
abbrev toStackInGroupoidsOver (X : StackInSetoidsOver J) : StackInGroupoidsOver J :=
  X.obj

/-- The underlying stack over `(C, J)`. -/
abbrev toStackOver (X : StackInSetoidsOver J) : StackOver J :=
  X.toStackInGroupoidsOver.toStackOver

/-- The underlying category fibred in groupoids over `C`. -/
abbrev toFibredInGroupoidsOver (X : StackInSetoidsOver J) : FibredInGroupoidsOver C :=
  X.toStackInGroupoidsOver.toFibredInGroupoidsOver

/-- The underlying category fibred in setoids over `C`. -/
abbrev toFibredInSetoidsOver (X : StackInSetoidsOver J) : FibredInSetoidsOver C :=
  ⟨X.toFibredInGroupoidsOver, X.property⟩

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : StackInSetoidsOver J) : FibredCategoryOver C :=
  X.toStackInGroupoidsOver.toFibredCategoryOver

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : StackInSetoidsOver J) : CategoryOver C :=
  X.toStackInGroupoidsOver.toCategoryOver

/-- The total category of a bundled stack in setoids over `(C, J)`. -/
abbrev S (X : StackInSetoidsOver J) :=
  X.toStackInGroupoidsOver.S

/-- The projection functor of a bundled stack in setoids over `(C, J)`. -/
abbrev p (X : StackInSetoidsOver J) :=
  X.toStackInGroupoidsOver.p

/-- The underlying based category over `C` of a stack in setoids over `(C, J)`. -/
abbrev toBasedCategory (X : StackInSetoidsOver J) : BasedCategory C :=
  X.toStackInGroupoidsOver.toBasedCategory

instance : CoeOut (StackInSetoidsOver J) (StackInGroupoidsOver J) where
  coe X := X.toStackInGroupoidsOver

instance : CoeOut (StackInSetoidsOver J) (StackOver J) where
  coe X := X.toStackOver

instance : CoeOut (StackInSetoidsOver J) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

instance : CoeOut (StackInSetoidsOver J) (FibredInSetoidsOver C) where
  coe X := X.toFibredInSetoidsOver

instance : CoeOut (StackInSetoidsOver J) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

instance : CoeOut (StackInSetoidsOver J) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (StackInSetoidsOver J) (BasedCategory C) where
  coe X := X.toBasedCategory

instance (X : StackInSetoidsOver J) : IsFibredInSetoids X.p := by
  simpa [StackInSetoidsOver.p, StackInGroupoidsOver.p] using X.property

instance (X : StackInSetoidsOver J) : IsStackInGroupoids J X.p := by
  change IsStackInGroupoids J X.obj.p
  infer_instance

instance (X : StackInSetoidsOver J) : IsStackInSetoids J X.p :=
  inferInstance

instance (X : StackInSetoidsOver J) : IsStackOnSite J X.p :=
  inferInstance

variable {X Y : StackInSetoidsOver J}

end StackInSetoidsOver

instance (J : GrothendieckTopology C) : Bicategory (StackInSetoidsOver J) :=
  SubTwoCategory.bicategoryObj (stackInSetoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Strict (StackInSetoidsOver J) :=
  SubTwoCategory.strictObj (stackInSetoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Bicategory.Strict (StackInSetoidsOver J) :=
  inferInstance

instance (J : GrothendieckTopology C) : Category (StackInSetoidsOver J) :=
  StrictBicategory.category (StackInSetoidsOver J)

instance stackInSetoidsOverHom₂IsMultiplicative
    (J : GrothendieckTopology C) (X Y : StackInSetoidsOver J) :
    ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom.IsMultiplicative :=
  ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom_isMultiplicative

instance stackInSetoidsOverHomInclusionFull
    (J : GrothendieckTopology C) (X Y : StackInSetoidsOver J) :
    (((stackInSetoidsOverSubTwoCategory J).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

namespace StackInSetoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInSetoidsOver J}

/-- Regard an ambient morphism in `StackInGroupoidsOver J` as the corresponding owner hom in the
full sub-`2`-category `StackInSetoidsOver J`. -/
abbrev ofAmbientHom
    (F : X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver) :
    X ⟶ Y :=
  ⟨⟨F, trivial⟩⟩

abbrev toStackInGroupoidsHom (F : X ⟶ Y) :
    X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver :=
  SubTwoCategory.Hom.toHom F

@[simp]
theorem toStackInGroupoidsHom_ofAmbientHom
    (F : X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver) :
    toStackInGroupoidsHom (ofAmbientHom F) = F :=
  rfl

@[simp]
theorem toStackInGroupoidsHom_comp
    {Z : StackInSetoidsOver J}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    toStackInGroupoidsHom (F ≫ G) =
      toStackInGroupoidsHom F ≫ toStackInGroupoidsHom G :=
  rfl

@[simp]
theorem ofAmbientHom_comp_obj
    {Z : StackInSetoidsOver J}
    (F : X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver)
    (G : Y ⟶ Z) :
    ((ofAmbientHom F) ≫ G).obj.obj = F ≫ G.obj.obj :=
  rfl

@[simp]
theorem comp_ofAmbientHom_obj
    {Z : StackInSetoidsOver J}
    (F : X ⟶ Y)
    (G : Y.toStackInGroupoidsOver ⟶ Z.toStackInGroupoidsOver) :
    (F ≫ ofAmbientHom G).obj.obj = F.obj.obj ≫ G :=
  rfl

set_option maxHeartbeats 1000000 in
/-- Convert an isomorphism between ambient stack-in-groupoids morphisms into an isomorphism in the
owner hom-category of stacks in setoids over `(C, J)`. -/
noncomputable def ofAmbientHomIso
    {F G : X ⟶ Y}
    (e : toStackInGroupoidsHom F ≅ toStackInGroupoidsHom G) :
    F ≅ G :=
  SubTwoCategory.Hom.isoMk e
    (show ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.hom) from trivial)
    (show ((stackInSetoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.inv) from trivial)

end StackInSetoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInSetoidsOver J}

instance : CoeOut (X ⟶ Y)
    (X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver) where
  coe F := StackInSetoidsOver.toStackInGroupoidsHom F

instance : CoeOut (X ⟶ Y)
    (FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver) where
  coe F :=
    StackInGroupoidsOver.Hom.toFibredInGroupoidsMor
      (show X.toStackInGroupoidsOver ⟶ Y.toStackInGroupoidsOver from F)

instance : CoeOut (X ⟶ Y)
    (X.toFibredInSetoidsOver ⟶ Y.toFibredInSetoidsOver) where
  coe F :=
    FibredInSetoidsOver.ofAmbientHom
      (show FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver from F)

instance : CoeOut (X ⟶ Y) (X.toStackOver ⟶ Y.toStackOver) where
  coe F :=
    show X.toStackOver ⟶ Y.toStackOver from
      InducedCategory.Hom.ofFibredCategoryMor
        (show FibredCategoryMor X.toStackOver.toFibredCategoryOver Y.toStackOver.toFibredCategoryOver from
          (show FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver from F).toHom)

end CategoryTheory
