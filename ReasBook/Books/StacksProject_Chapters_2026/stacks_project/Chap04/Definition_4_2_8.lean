module

public import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Definition 4.2.8:
- primary domain: basic category theory, specifically the owner object for functors between
  categories;
- sampled owner-level declarations:
  `(C ⥤ D)`,
  `CategoryTheory.Functor`,
  `CategoryTheory.Functor.obj`,
  `CategoryTheory.Functor.map`,
  `CategoryTheory.Functor.map_comp`;
- best owner abstraction: `CategoryTheory.Functor`, with source-facing surface notation `C ⥤ D`;
- primitive data: the object map `Functor.obj`, the morphism map `Functor.map`, and the
  functoriality axioms `Functor.map_id` and `Functor.map_comp`;
- derived API: composition of functors, identity functors, faithfulness/fullness, and the later
  structure built on top of `Functor`.

Source/core/bridge triage:
- `source-facing`: the standard notation `C ⥤ D` for functors from `C` to `D`;
- `core/canonical`: the mathlib owner structure `Functor`;
- `bridge/view`: the primitive field projections `Functor.obj`, `Functor.map`, `Functor.map_id`,
  and `Functor.map_comp`. -/

/- Definition 4.2.8: the canonical owner notion of a functor from `C` to `D` is the structure
`CategoryTheory.Functor`, written `C ⥤ D`. Its primitive data are the object map, morphism map,
and the two functoriality axioms recalled below. -/
recall Functor

/- Companion source-facing notation: the type of functors from `C` to `D` is written `C ⥤ D`. -/
#check (C ⥤ D)

/- Primitive owner field: for a functor `F : C ⥤ D`, the induced map on objects is the canonical
field `Functor.obj`. -/
recall Functor.obj

/- Primitive owner field: for a functor `F : C ⥤ D`, the induced map on morphisms is the
canonical field `Functor.map`. -/
recall Functor.map

/- Primitive functoriality field: the identity preservation axiom in the source definition is the
canonical field `Functor.map_id`. -/
recall Functor.map_id

/- Primitive functoriality field: the composition preservation axiom in the source definition is
the canonical field `Functor.map_comp`. -/
recall Functor.map_comp

end CategoryTheory
