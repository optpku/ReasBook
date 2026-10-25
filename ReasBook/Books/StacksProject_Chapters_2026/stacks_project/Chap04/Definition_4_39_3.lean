module

public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Definition_4_38_3
public import stacks_project.Chap04.Definition_4_39_1
public import stacks_project.Chap04.Definition_4_39_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v vS w

namespace CategoryTheory

open Bicategory
open ObjectProperty
open BasedFunctor
open scoped Bicategory

/-
Domain-style sampling for Definition 4.39.3:
- primary domain: categories fibred in setoids over a fixed base, viewed as a full sub-`2`-
  category of categories fibred in groupoids.
- inspected owner-level declarations:
  `SubTwoCategory`,
  `IsFibredInSetoids`,
  `FibredInGroupoidsOver`,
  `SubTwoCategory.Hom.toHom`.
- best owner abstraction: the source-facing owner is the full sub-`2`-category of
  `FibredInGroupoidsOver C` cut out by the fibred-in-setoids condition.
- primitive data: a category fibred in groupoids over `C` together with the proof that its
  projection is fibred in setoids.
- derived API: the coercions to the ambient fibred-in-groupoids, fibred-category, category-over,
  and based-category owners; the ambient fibred-in-groupoids morphism view is recovered directly
  from the owner homs `X ⟶ Y`.

Source/core/bridge triage:
- `source-facing`: `FibredInSetoidsOver C`;
- `core/canonical`: `SubTwoCategory`, `FibredInGroupoidsOver`, `IsFibredInSetoids`, and the
  owner homs `X ⟶ Y`;
- `bridge/view`: the forgetful coercions to ambient owners.

Primitive-vs-derived split:
- primitive data: the underlying category fibred in groupoids over `C` together with the proof
  that its projection is fibred in setoids;
- derived API: the inherited strict bicategory structure and the short projections to the ambient
  owner data; morphisms are inherited directly from the ambient fibred-in-groupoids owner. -/

/-- Definition 4.39.3 at the owner level: categories fibred in setoids over `C` form the full
sub-`2`-category of `FibredInGroupoidsOver C` cut out by the fibred-in-setoids condition. -/
abbrev fibredInSetoidsOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (FibredInGroupoidsOver C) where
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

variable {C : Type u} [Category.{v} C]

/-- Definition 4.39.3: the objects of the `2`-category of categories fibred in setoids over `C`
are the categories fibred in groupoids over `C` whose projection functor is fibred in setoids;
equivalently, this is the full sub-`2`-category of categories fibred in groupoids over `C` cut
out by the fibred-in-setoids condition. -/
abbrev FibredInSetoidsOver (C : Type u) [Category.{v} C] :=
  (fibredInSetoidsOverSubTwoCategory C).Obj

instance : Bicategory (FibredInSetoidsOver C) :=
  SubTwoCategory.bicategoryObj (fibredInSetoidsOverSubTwoCategory C)

instance : Bicategory.Strict (FibredInSetoidsOver C) :=
  SubTwoCategory.strictObj (fibredInSetoidsOverSubTwoCategory C)

instance fibredInSetoidsOverCategory : Category (FibredInSetoidsOver C) :=
  StrictBicategory.category (FibredInSetoidsOver C)

instance fibredInSetoidsOverHom₂IsMultiplicative (X Y : FibredInSetoidsOver C) :
    ((fibredInSetoidsOverSubTwoCategory C).hom₂ X Y).IsMultiplicative :=
  ((fibredInSetoidsOverSubTwoCategory C).hom X Y).hom_isMultiplicative

instance fibredInSetoidsOverHomInclusionFull (X Y : FibredInSetoidsOver C) :
    (((fibredInSetoidsOverSubTwoCategory C).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

namespace FibredInSetoidsOver

/-- Build a bundled category fibred in setoids over `C` from a functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsFibredInSetoids p] :
    FibredInSetoidsOver C :=
  ⟨FibredInGroupoidsOver.ofFunctor p, by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor] using
      (inferInstance : IsFibredInSetoids p)⟩

/-- The underlying category fibred in groupoids over `C`. -/
abbrev toFibredInGroupoidsOver (X : FibredInSetoidsOver C) : FibredInGroupoidsOver C :=
  X.obj

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : FibredInSetoidsOver C) : FibredCategoryOver C :=
  (X.toFibredInGroupoidsOver : FibredCategoryOver C)

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredInSetoidsOver C) : CategoryOver C :=
  X.toFibredInGroupoidsOver.toCategoryOver

/-- The total category of a bundled category fibred in setoids over `C`. -/
abbrev S (X : FibredInSetoidsOver C) :=
  X.toFibredInGroupoidsOver.S

/-- The projection functor of a bundled category fibred in setoids over `C`. -/
abbrev p (X : FibredInSetoidsOver C) :=
  X.toFibredInGroupoidsOver.p

/-- The defining property of an object of `FibredInSetoidsOver C`: its projection functor is
fibred in setoids. -/
-- Proof sketch: This is the property field of the corresponding object of the full
-- sub-`2`-category.
theorem isFibredInSetoids_p (X : FibredInSetoidsOver C) : IsFibredInSetoids X.p :=
  -- The bundled owner stores exactly the fibred-in-setoids condition on the projection.
  X.property

/-- Forget a bundled category fibred in setoids over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredInSetoidsOver C) : BasedCategory C :=
  X.toFibredInGroupoidsOver.toBasedCategory

/-- Compatibility coercion to categories fibred in groupoids over `C`. -/
instance : CoeOut (FibredInSetoidsOver C) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

/-- Compatibility coercion to fibred categories over `C`. -/
instance : CoeOut (FibredInSetoidsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Compatibility coercion to the ambient category `Cat/C`. -/
instance : CoeOut (FibredInSetoidsOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

/-- Compatibility coercion to the ambient based-category API. -/
instance : CoeOut (FibredInSetoidsOver C) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in setoids over `C` is fibred in
setoids. -/
instance (X : FibredInSetoidsOver C) : IsFibredInSetoids (FibredInSetoidsOver.p X) :=
  X.property

variable {X Y : FibredInSetoidsOver C}

/-- Regard an ambient morphism of the underlying categories fibred in groupoids over `C` as the
corresponding owner hom in the full sub-`2`-category `FibredInSetoidsOver C`. -/
abbrev ofAmbientHom
    (F : X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) : X ⟶ Y :=
  { obj := { obj := F, property := trivial } }

/-- Build a morphism of categories fibred in setoids over `C` from a based functor over `C`.
This is the thin owner-level bridge from the ambient `BasedFunctor` API. -/
abbrev ofBasedFunctor
    (F : X.toBasedCategory ⥤ᵇ Y.toBasedCategory) : X ⟶ Y :=
  ofAmbientHom (FibredInGroupoidsMor.ofBasedFunctor F)

/-- The underlying based functor of a morphism of categories fibred in setoids over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredInGroupoidsMor.toBasedFunctor F.toHom

/- Convert an isomorphism between the ambient morphisms of categories fibred in groupoids into
an isomorphism in the owner hom-category of categories fibred in setoids. -/
noncomputable def ofAmbientIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- Compatibility coercion from owner morphisms to based functors over `C`. -/
instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

/-- A morphism of categories fibred in setoids over `C` is an equivalence over the base if its
underlying based functor is. -/
abbrev IsEquivalenceOverBase (F : X ⟶ Y) : Prop :=
  BasedFunctor.IsEquivalenceOverBase (toBasedFunctor F)

end FibredInSetoidsOver

variable {C : Type u} [Category.{v} C]

/-- A category fibred in sets over `C` canonically defines a category fibred in setoids over
`C`. -/
instance : CoeTC (FibredInSetsOver C) (FibredInSetoidsOver C) where
  coe X := by
    letI : IsFibredInSetoids X.p := inferInstance
    exact FibredInSetoidsOver.ofFunctor X.p

variable {X Y : FibredInSetoidsOver C}

/-- A morphism of categories fibred in setoids over `C` is canonically viewed as the
corresponding ambient morphism of categories fibred in groupoids over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) where
  coe F := F.toHom

variable (F G : X ⟶ Y)

/- Definition 4.39.3: a `2`-morphism between `1`-morphisms of categories fibred in setoids over
`C` is the inherited morphism in the owner hom-category of the full sub-`2`-category
`fibredInSetoidsOverSubTwoCategory C`. -/
#check (F ⟶ G)

end CategoryTheory
