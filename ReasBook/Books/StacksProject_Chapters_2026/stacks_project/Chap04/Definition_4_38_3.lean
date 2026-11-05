module

public import stacks_project.Chap04.Definition_4_35_6
public import stacks_project.Chap04.Definition_4_38_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v vS w

namespace CategoryTheory

open Bicategory
open ObjectProperty
open scoped Bicategory

/-
Domain-style sampling for Definition 4.38.3:
- primary domain: categories fibred in sets over a fixed base, viewed as a full sub-`2`-category
  of categories fibred in groupoids.
- inspected owner-level declarations:
  `SubTwoCategory`,
  `SubTwoCategory.Hom.toHom`,
  `SubTwoCategory.Hom`,
  `FibredInGroupoidsOver`,
  `IsFibredInSets`.
- best owner abstraction: the source-facing owner is the full sub-`2`-category of
  `FibredInGroupoidsOver C` cut out by the property `IsFibredInSets X.p`, with inherited
  `1`-morphisms and `2`-morphisms.
- primitive data: a category fibred in groupoids over `C` together with the proof that its
  projection is fibred in sets.
- derived API: the coercions to the ambient fibred-in-groupoids, fibred-category, category-over,
  and based-category owners; the morphism layer is read directly through the ambient owner hom
  `FibredInGroupoidsMor X.toFibredInGroupoidsOver Y.toFibredInGroupoidsOver`.

Source/core/bridge triage:
- `source-facing`: `FibredInSetsOver C` together with its owner homs `X ⟶ Y`;
- `core/canonical`: `SubTwoCategory`, `FibredInGroupoidsOver`, `IsFibredInSets`;
- `bridge/view`: the forgetful coercions to ambient owners.

Primitive-vs-derived split:
- primitive data: the underlying category fibred in groupoids over `C` together with the proof
  that its projection is fibred in sets;
- derived API: the inherited strict bicategory structure and the short projections to the ambient
  owner data; the owner morphism bridge is the canonical ambient accessor `F.toHom`, and the
  based-functor API is derived from it. -/

/-- Definition 4.38.3 at the owner level: categories fibred in sets over `C` form the full
sub-`2`-category of `FibredInGroupoidsOver C` cut out by the fibred-in-sets condition. -/
abbrev fibredInSetsOverSubTwoCategory (C : Type u) [Category.{v} C] :
    SubTwoCategory (FibredInGroupoidsOver C) where
  obj := fun X ↦ IsFibredInSets X.p
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

/-- Definition 4.38.3: the objects of the `2`-category of categories fibred in sets over `C` are
the categories over `C` whose projection functor is fibred in sets; equivalently, this is the
full sub-`2`-category of categories fibred in groupoids over `C` cut out by the fibred-in-sets
condition. -/
abbrev FibredInSetsOver (C : Type u) [Category.{v} C] :=
  (fibredInSetsOverSubTwoCategory C).Obj

instance : Bicategory (FibredInSetsOver C) :=
  SubTwoCategory.bicategoryObj (fibredInSetsOverSubTwoCategory C)

instance : Bicategory.Strict (FibredInSetsOver C) :=
  SubTwoCategory.strictObj (fibredInSetsOverSubTwoCategory C)

instance fibredInSetsOverCategory : Category (FibredInSetsOver C) :=
  StrictBicategory.category (FibredInSetsOver C)

instance fibredInSetsOverHom₂IsMultiplicative (X Y : FibredInSetsOver C) :
    ((fibredInSetsOverSubTwoCategory C).hom₂ X Y).IsMultiplicative :=
  ((fibredInSetsOverSubTwoCategory C).hom X Y).hom_isMultiplicative

instance fibredInSetsOverHomInclusionFull (X Y : FibredInSetsOver C) :
    (((fibredInSetsOverSubTwoCategory C).hom X Y).inclusion).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨ObjectProperty.homMk η, trivial⟩, rfl⟩

instance fibredInSetsOverHomWideInclusionFull (X Y : FibredInSetsOver C) :
    (wideSubcategoryInclusion ((fibredInSetsOverSubTwoCategory C).hom₂ X Y)).Full where
  map_surjective := by
    intro F G η
    refine ⟨⟨η, trivial⟩, rfl⟩

namespace FibredInSetsOver

/-- Build a bundled category fibred in sets over `C` from a functor to `C`. -/
abbrev ofFunctor {S : Type w} [Category.{vS} S] (p : S ⥤ C) [IsFibredInSets p] :
    FibredInSetsOver C :=
  ⟨FibredInGroupoidsOver.ofFunctor p, by
    simpa [FibredInGroupoidsOver.p, FibredInGroupoidsOver.ofFunctor] using
      (inferInstance : IsFibredInSets p)⟩

/-- The underlying category fibred in groupoids over `C`. -/
abbrev toFibredInGroupoidsOver (X : FibredInSetsOver C) : FibredInGroupoidsOver C :=
  X.obj

/-- The underlying fibred category over `C`. -/
abbrev toFibredCategoryOver (X : FibredInSetsOver C) : FibredCategoryOver C :=
  (X.toFibredInGroupoidsOver : FibredCategoryOver C)

/-- The underlying category over `C`. -/
abbrev toCategoryOver (X : FibredInSetsOver C) : CategoryOver C :=
  X.toFibredInGroupoidsOver.toCategoryOver

/-- The total category of a bundled category fibred in sets over `C`. -/
abbrev S (X : FibredInSetsOver C) :=
  X.toFibredInGroupoidsOver.S

/-- The projection functor of a bundled category fibred in sets over `C`. -/
abbrev p (X : FibredInSetsOver C) :=
  X.toFibredInGroupoidsOver.p

/-- The defining property of an object of `FibredInSetsOver C`: its projection functor is
fibred in sets. -/
-- Proof sketch: This is the property field of the corresponding object of the full
-- sub-`2`-category.
theorem isFibredInSets_p (X : FibredInSetsOver C) : IsFibredInSets X.p :=
  X.property

/-- Forget a bundled category fibred in sets over `C` to its underlying based category. -/
abbrev toBasedCategory (X : FibredInSetsOver C) : BasedCategory C :=
  X.toFibredInGroupoidsOver.toBasedCategory

/-- Compatibility coercion to categories fibred in groupoids over `C`. -/
instance : CoeOut (FibredInSetsOver C) (FibredInGroupoidsOver C) where
  coe X := X.toFibredInGroupoidsOver

/-- Compatibility coercion to fibred categories over `C`. -/
instance : CoeOut (FibredInSetsOver C) (FibredCategoryOver C) where
  coe X := X.toFibredCategoryOver

/-- Compatibility coercion to the ambient category `Cat/C`. -/
instance : CoeOut (FibredInSetsOver C) (CategoryOver C) where
  coe X := X.toCategoryOver

/-- Compatibility coercion to the ambient based-category API. -/
instance : CoeOut (FibredInSetsOver C) (BasedCategory C) where
  coe X := X.toBasedCategory

/-- The projection functor of a bundled category fibred in sets over `C` is fibred in sets. -/
instance (X : FibredInSetsOver C) : IsFibredInSets X.p :=
  X.property

variable {X Y : FibredInSetsOver C}

/-- Regard an ambient morphism of the underlying categories fibred in groupoids over `C` as the
corresponding owner hom in the full sub-`2`-category `FibredInSetsOver C`. -/
abbrev ofAmbientHom
    (F : X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) : X ⟶ Y :=
  { obj := { obj := F, property := trivial } }

/-- The underlying based functor of a morphism of categories fibred in sets over `C`. -/
abbrev toBasedFunctor (F : X ⟶ Y) : X.toBasedCategory ⥤ᵇ Y.toBasedCategory :=
  FibredInGroupoidsMor.toBasedFunctor F.toHom

/- Convert an isomorphism between the ambient morphisms of categories fibred in groupoids into
an isomorphism in the owner hom-category of categories fibred in sets. -/
noncomputable def ofAmbientIso
    {F G : X ⟶ Y}
    (e : F.toHom ≅ G.toHom) :
    F ≅ G :=
  CategoryTheory.isoMk (ObjectProperty.isoMk _ e) trivial trivial

/-- The induced functor on the fiber over `U`. -/
abbrev fiberFunctor (F : X ⟶ Y) (U : C) :=
  (toBasedFunctor F).fiberFunctor U

/-- The underlying functor between the total categories. -/
abbrev G (F : X ⟶ Y) : X.S ⥤ Y.S :=
  (toBasedFunctor F).toFunctor

/-- The compatibility of the underlying functor with the base projections. -/
abbrev comm (F : X ⟶ Y) : G F ⋙ Y.p = X.p :=
  (toBasedFunctor F).w

/-- A morphism of categories fibred in sets over `C` is canonically viewed as the corresponding
ambient morphism of categories fibred in groupoids over `C`. -/
instance : CoeOut (X ⟶ Y)
    (X.toFibredInGroupoidsOver ⟶ Y.toFibredInGroupoidsOver) where
  coe F := F.toHom

/-- Compatibility coercion from owner morphisms to based functors over `C`. -/
instance : CoeOut (X ⟶ Y) (X.toBasedCategory ⥤ᵇ Y.toBasedCategory) where
  coe F := toBasedFunctor F

end FibredInSetsOver

variable {X Y : FibredInSetsOver C}

variable (F G : X ⟶ Y)

/- Definition 4.38.3: a `2`-morphism between `1`-morphisms of categories fibred in sets over `C`
is the inherited morphism in the owner hom-category of the full sub-`2`-category
`fibredInSetsOverSubTwoCategory C`. -/
#check (F ⟶ G)

end CategoryTheory
