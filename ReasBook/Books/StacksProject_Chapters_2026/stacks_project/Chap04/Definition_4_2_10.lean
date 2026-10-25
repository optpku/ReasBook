module

public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Widesubcategory
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open ObjectProperty

variable (C : Type u) [Category.{v} C]

/-
Domain-style sampling for Definition 4.2.10:
- primary domain: subcategories of a category, organized by chosen objects and chosen morphisms;
- sampled owner-level declarations:
  `WideSubcategory`,
  `wideSubcategoryInclusion`,
  `ObjectProperty.FullSubcategory`,
  `Functor.Full`,
  `ObjectProperty.IsClosedUnderIsomorphisms`;
- best owner abstraction: a wide subcategory of the canonical full subcategory cut out by the
  chosen objects;
- primitive data: an object property `obj : ObjectProperty C` and a multiplicative morphism
  property `hom : MorphismProperty obj.FullSubcategory`;
- derived API: the canonical inclusion functor `S.inclusion`, the owner predicate
  `S.inclusion.Full`, and the strict-fullness predicate `S.IsStrictlyFull`.

Source/core/bridge triage:
- `source-facing`: `Subcategory`, `Subcategory.IsStrictlyFull`;
- `core/canonical`: `WideSubcategory`, `wideSubcategoryInclusion`, `ObjectProperty.FullSubcategory`,
  `Functor.Full`;
- `bridge/view`: `Subcategory.inclusion`.
-/

/-- Definition 4.2.10: a subcategory of `C` is given by a class of objects together with, for
every pair of chosen objects, a class of morphisms between them that contains identities and is
closed under composition. Internally this is expressed as a multiplicative morphism property on the
canonical full subcategory cut out by the chosen objects. -/
structure Subcategory where
  obj : ObjectProperty C
  hom : MorphismProperty obj.FullSubcategory
  hom_isMultiplicative : hom.IsMultiplicative

namespace Subcategory

variable {C}

/-- The chosen morphism property of a subcategory is multiplicative. -/
instance homIsMultiplicative (S : Subcategory C) : S.hom.IsMultiplicative :=
  S.hom_isMultiplicative

/-- The chosen objects and morphisms of a subcategory form a category. -/
instance category (S : Subcategory C) : Category (WideSubcategory S.hom) :=
  WideSubcategory.category S.hom

/-- The canonical inclusion of a subcategory into the ambient category. -/
abbrev inclusion (S : Subcategory C) : WideSubcategory S.hom ⥤ C :=
  wideSubcategoryInclusion S.hom ⋙ S.obj.ι

/-
For a subcategory `S`, fullness is expressed by requiring that the canonical inclusion
`S.inclusion : WideSubcategory S.hom ⥤ C` is a full functor, so the owner-level notion is
`[S.inclusion.Full]`.
-/

/-- A subcategory is strictly full if it is full and its chosen objects are
closed under isomorphisms in the ambient category. -/
class IsStrictlyFull (S : Subcategory C) : Prop extends S.inclusion.Full,
    S.obj.IsClosedUnderIsomorphisms

end Subcategory

end CategoryTheory
