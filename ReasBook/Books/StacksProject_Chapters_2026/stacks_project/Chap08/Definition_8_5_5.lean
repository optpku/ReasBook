module

public import Mathlib
public import Mathlib.CategoryTheory.Widesubcategory
public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap08.Definition_8_4_5
public import stacks_project.Chap08.Definition_8_5_1


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

/-- Definition 8.5.5 at the owner level: stacks in groupoids over `(C, J)` form the full
sub-`2`-category of `FibredInGroupoidsOver C` cut out by the stack-on-site condition on the
projection functor. Equivalently, they are stacks over `(C, J)` whose projection is already
fibred in groupoids. -/
abbrev stackInGroupoidsOverSubTwoCategory (J : GrothendieckTopology C) :
    SubTwoCategory (FibredInGroupoidsOver C) where
  obj := fun X ↦ IsStackOnSite J X.p
  hom _ _ := {
    obj := ⊤
    hom := ⊤
    hom_isMultiplicative := inferInstance
  }
  id_mem _ := by trivial
  comp_mem _ _ := by trivial
  whiskerLeft_mem _ _ _ _ := by trivial
  whiskerRight_mem _ _ _ _ := by trivial

/-- Definition 8.5.5: the objects of the `2`-category of stacks in groupoids over `(C, J)` are
the objects of the canonical owner sub-`2`-category `stackInGroupoidsOverSubTwoCategory J`. -/
abbrev StackInGroupoidsOver (J : GrothendieckTopology C) :=
  (stackInGroupoidsOverSubTwoCategory J).Obj

instance (J : GrothendieckTopology C) : Bicategory (StackInGroupoidsOver J) :=
  SubTwoCategory.bicategoryObj (stackInGroupoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Bicategory.Strict (StackInGroupoidsOver J) :=
  SubTwoCategory.strictObj (stackInGroupoidsOverSubTwoCategory J)

instance (J : GrothendieckTopology C) : Category (StackInGroupoidsOver J) :=
  StrictBicategory.category (StackInGroupoidsOver J)

instance stackInGroupoidsOverHom₂IsMultiplicative
    (J : GrothendieckTopology C) (X Y : StackInGroupoidsOver J) :
    ((stackInGroupoidsOverSubTwoCategory J).hom₂ X Y).IsMultiplicative :=
  ((stackInGroupoidsOverSubTwoCategory J).hom X Y).hom_isMultiplicative

instance stackInGroupoidsOverHomInclusionFull
    (J : GrothendieckTopology C) (X Y : StackInGroupoidsOver J) :
    (((stackInGroupoidsOverSubTwoCategory J).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

instance stackInGroupoidsOverHomWideInclusionFull
    (J : GrothendieckTopology C) (X Y : StackInGroupoidsOver J) :
    (wideSubcategoryInclusion ((stackInGroupoidsOverSubTwoCategory J).hom₂ X Y)).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨η, trivial⟩, rfl⟩

namespace StackInGroupoidsOver

variable {J : GrothendieckTopology C}
variable {D : Type (max u v)} [Category.{v} D]

abbrev ofProjection (J : GrothendieckTopology C) (p : D ⥤ C) [IsStackInGroupoids J p] :
    StackInGroupoidsOver J :=
  ⟨FibredInGroupoidsOver.ofFunctor p, by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor] using
      (inferInstance : IsStackOnSite J p)⟩

abbrev toFibredInGroupoidsOver (X : StackInGroupoidsOver J) : FibredInGroupoidsOver C :=
  X.obj

abbrev toFibredCategoryOver (X : StackInGroupoidsOver J) : FibredCategoryOver C :=
  X.toFibredInGroupoidsOver.toFibredCategoryOver

abbrev toStackOver (X : StackInGroupoidsOver J) : StackOver J :=
  ⟨X.toFibredCategoryOver, X.property⟩

abbrev toCategoryOver (X : StackInGroupoidsOver J) : CategoryOver C :=
  X.toFibredInGroupoidsOver.toCategoryOver

abbrev S (X : StackInGroupoidsOver J) :=
  X.toFibredInGroupoidsOver.S

abbrev p (X : StackInGroupoidsOver J) :=
  X.toFibredInGroupoidsOver.p

abbrev toBasedCategory (X : StackInGroupoidsOver J) : BasedCategory C :=
  X.toFibredInGroupoidsOver.toBasedCategory

instance : CoeOut (StackInGroupoidsOver J) (StackOver J) where
  coe X := X.toStackOver

instance : CoeOut (StackInGroupoidsOver J) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

instance : CoeOut (StackInGroupoidsOver J) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

instance : CoeOut (StackInGroupoidsOver J) (CategoryOver C) where
  coe X := X.toCategoryOver

instance : CoeOut (StackInGroupoidsOver J) (BasedCategory C) where
  coe X := X.toBasedCategory

instance (X : StackInGroupoidsOver J) : IsStackInGroupoids J X.p where
  toIsStackOnSite := X.property
  toIsFibredInGroupoids := inferInstance

instance (X : StackInGroupoidsOver J) : X.p.IsFibered :=
  inferInstance

instance (X : StackInGroupoidsOver J) : IsStackOnSite J X.p :=
  X.property

instance (X : StackInGroupoidsOver J) : HasFibers X.p :=
  HasFibers.canonical X.p

instance (X : StackInGroupoidsOver J) : IsFibredInGroupoids X.p :=
  inferInstance

/-- A stack in groupoids over `(C, J)` has projection functor a stack in groupoids. -/
-- Proof sketch: this is exactly the defining property carried by an object of the full
-- sub-`2`-category `stackInGroupoidsOverSubTwoCategory J`, together with the inherited
-- fibred-in-groupoids structure on its projection.
theorem isStackInGroupoids_p (X : StackInGroupoidsOver J) : IsStackInGroupoids J X.p := by
  -- The projection already carries both components of `IsStackInGroupoids`.
  exact inferInstance

end StackInGroupoidsOver

namespace FibredInGroupoidsMor

variable {J : GrothendieckTopology C}
variable {X : FibredInGroupoidsOver C}
variable {Y : StackInGroupoidsOver J}

abbrev toStackFibredCategoryMor
    (F : FibredInGroupoidsMor X Y) :
    FibredCategoryMor (X : FibredCategoryOver C) (Y : StackOver J) :=
  show FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C) from F

end FibredInGroupoidsMor

namespace StackInGroupoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Regard an ambient morphism of the underlying categories fibred in groupoids over `C` as the
corresponding owner hom in the full sub-`2`-category `StackInGroupoidsOver J`. -/
abbrev ofAmbientHom
    (F : X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) :
    X ⟶ Y :=
  ⟨⟨F, trivial⟩⟩

/-- Regard an ambient morphism of the underlying fibred categories over `C` as the corresponding
owner hom in the full sub-`2`-category `StackInGroupoidsOver J`. -/
abbrev ofFibredCategoryHom
    (F : X.toFibredCategoryOver ⟶ Y.toFibredCategoryOver) :
    X ⟶ Y :=
  ofAmbientHom <|
    FibredInGroupoidsMor.ofAmbientHom F

end StackInGroupoidsOver

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

namespace StackInGroupoidsOver.Hom

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/- The ambient `1`-morphism of categories fibred in groupoids over `C` underlying an owner hom
of stacks in groupoids over `(C, J)`. -/
abbrev toFibredInGroupoidsMor (F : X ⟶ Y) :
    FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver :=
  F.toHom

instance : CoeOut (X ⟶ Y)
    (FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver) where
  coe F := toFibredInGroupoidsMor F

abbrev toFibredCategoryMor (F : X ⟶ Y) :
    FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C) :=
  toFibredInGroupoidsMor F

abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredInGroupoidsMor.toBasedFunctor (toFibredInGroupoidsMor F)

abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  (toBasedFunctor F).toFunctor

abbrev comm (F : X ⟶ Y) : G F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

instance : CoeOut (X ⟶ Y)
    (FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C)) where
  coe F := toFibredCategoryMor F

instance : CoeOut (X ⟶ Y)
    (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  (toBasedFunctor F).IsEquivalenceOverBase

abbrev LocallyEssentiallySurjectiveOnObjects
    (F : X ⟶ Y) : Prop :=
  FibredCategoryMor.LocallyEssentiallySurjectiveOnObjects J (toFibredCategoryMor F)

/-- Regard an ambient based functor over `C` as the corresponding owner hom in the full
sub-`2`-category `StackInGroupoidsOver J`. -/
abbrev ofBasedFunctor
    (G : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) :
    X ⟶ Y :=
  StackInGroupoidsOver.ofAmbientHom (FibredInGroupoidsMor.ofBasedFunctor G)

/-- Convert an isomorphism between the ambient fibred-in-groupoids morphisms into an isomorphism
in the owner hom-category of stacks in groupoids over `(C, J)`. -/
noncomputable def ofAmbientHomIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  SubTwoCategory.Hom.isoMk e
    (show ((stackInGroupoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.hom) from trivial)
    (show ((stackInGroupoidsOverSubTwoCategory J).hom X Y).hom
        (ObjectProperty.homMk e.inv) from trivial)

/-- Compatibility alias for `ofAmbientHomIso`. -/
noncomputable def ofAmbientIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  ofAmbientHomIso e

end StackInGroupoidsOver.Hom

namespace WideSubcategory

variable {J : GrothendieckTopology C}
variable {X Y : StackInGroupoidsOver J}

/-- Field-notation bridge to the ambient fibred-in-groupoids morphism underlying an owner hom of
stacks in groupoids over `(C, J)`. -/
abbrev toFibredInGroupoidsMor (F : X ⟶ Y) :
    FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver :=
  StackInGroupoidsOver.Hom.toFibredInGroupoidsMor F

/-- Field-notation bridge to the ambient fibred-category morphism underlying an owner hom of
stacks in groupoids over `(C, J)`. -/
abbrev toFibredCategoryMor (F : X ⟶ Y) :
    FibredCategoryMor (X : FibredCategoryOver C) (Y : FibredCategoryOver C) :=
  StackInGroupoidsOver.Hom.toFibredCategoryMor F

/-- Field-notation bridge to the underlying based functor of an owner hom of stacks in groupoids
over `(C, J)`. -/
abbrev toBasedFunctor (F : X ⟶ Y) :
    X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  StackInGroupoidsOver.Hom.toBasedFunctor F

/-- Field-notation bridge to the induced functor on a fiber of an owner hom of stacks in
groupoids over `(C, J)`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  StackInGroupoidsOver.Hom.fiberFunctor F U

/-- Field-notation bridge to the underlying functor between total categories of an owner hom of
stacks in groupoids over `(C, J)`. -/
abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  StackInGroupoidsOver.Hom.G F

/-- Field-notation bridge to the compatibility of the underlying functor with the base
projections. -/
abbrev comm (F : X ⟶ Y) : F.G ⋙ Y.p = X.p :=
  StackInGroupoidsOver.Hom.comm F

/-- Field-notation bridge to the equivalence-over-base predicate on owner homs of stacks in
groupoids over `(C, J)`. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  StackInGroupoidsOver.Hom.IsEquivalenceOverBase F

/-- Field-notation bridge to the local essential-image predicate on owner homs of stacks in
groupoids over `(C, J)`. -/
abbrev LocallyEssentiallySurjectiveOnObjects
    (F : X ⟶ Y) : Prop :=
  StackInGroupoidsOver.Hom.LocallyEssentiallySurjectiveOnObjects F

end WideSubcategory

end CategoryTheory
