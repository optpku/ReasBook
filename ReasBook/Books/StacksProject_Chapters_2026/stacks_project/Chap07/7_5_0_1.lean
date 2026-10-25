module

public import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for 7.5.0.1:
- primary domain: structured-arrow / comma categories attached to a functor and a chosen source
  object;
- sampled owner API:
  `StructuredArrow`,
  `StructuredArrow.mk`,
  `StructuredArrow.homMk`,
  `StructuredArrow.proj`;
- source/core/bridge triage:
  `source-facing`: the textbook description by pairs `(U, φ)` and commuting triangles;
  `core/canonical`: `StructuredArrow V u`;
  `bridge/view`: the constructor/projection API above, which recovers the pairwise presentation from
  the owner object.

Primitive data are only the object `V : D` and the functor `u : C ⥤ D`. The pair presentation of
objects and the commutativity condition on morphisms are derived API of the canonical owner
`StructuredArrow V u`, so this file should remain a direct recall rather than introducing a local
duplicate structure.
-/

/- 7.5.0.1: for a functor `u : C ⥤ D` and an object `V : D`, the category whose objects are pairs
`(U, φ)` with `U : C` and `φ : V ⟶ u.obj U`, and whose morphisms `(U, φ) ⟶ (U', φ')` are arrows
`f : U ⟶ U'` satisfying `φ ≫ u.map f = φ'`, is the canonical structured-arrow category
`StructuredArrow V u`. -/
recall StructuredArrow

end CategoryTheory
