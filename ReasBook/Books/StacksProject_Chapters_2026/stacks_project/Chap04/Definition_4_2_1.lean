module

public import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/- Domain-style sampling for Definition 4.2.1:
- primary domain: the primitive data and axioms of a category.
- inspected owner declarations: `Quiver.Hom`, `CategoryStruct.id`, `CategoryStruct.comp`,
  and `Category`.
- best owner abstraction: `Category`; its inherited owner stack already carries the textbook data,
  so this file should recall that owner instead of introducing a parallel wrapper.

Primitive-vs-derived split:
- primitive data inherited by the owner stack: hom-types from `Quiver.Hom`, identity morphisms
  from `CategoryStruct.id`, composition from `CategoryStruct.comp`, and the axioms from
  `Category`.
- derived API used on the source-facing surface: the standard notation `X ⟶ Y`, `𝟙 X`, `f ≫ g`,
  together with `Category.id_comp`, `Category.comp_id`, and `Category.assoc`.

Source/core/bridge triage:
- `source-facing`: the textbook hom-set, identity, composition, and three category axioms.
- `core/canonical`: `Category`.
- `bridge/view`: the inherited notation and axiom names exposing the source wording on top of the
  canonical owner stack. -/

/- Definition 4.2.1: a category on the ambient type of objects `C` is the canonical mathlib class
`Category`. The source hom-types, identities, and composition are already the inherited data
`Quiver.Hom`, `CategoryStruct.id`, and `CategoryStruct.comp`, so no parallel local definition is
needed. The left/right identity axioms and associativity are the fields of `Category` itself. -/
recall Category

/- Definition 4.2.1, source hom-set notation: for objects `X Y : C`, the morphisms from `X` to
`Y` form the canonical hom-type `X ⟶ Y`, i.e. the notation for `Quiver.Hom X Y`. -/
#check (X ⟶ Y)

/- Definition 4.2.1, source identity morphism: the identity of an object `X` is the canonical
morphism `𝟙 X`, i.e. the notation for `CategoryStruct.id X`. -/
#check (𝟙 X)

/- Definition 4.2.1, source composition operation: composition of composable morphisms is the
canonical infix operation `≫`, i.e. the notation for `CategoryStruct.comp`. -/
#check fun (f : X ⟶ Y) (g : Y ⟶ Z) ↦ f ≫ g

/- Definition 4.2.1 (1): left identity for composition is the canonical axiom
`Category.id_comp`. -/
recall Category.id_comp

/- Definition 4.2.1 (2): right identity for composition is the canonical axiom
`Category.comp_id`. -/
recall Category.comp_id

/- Definition 4.2.1 (3): associativity of composition is the canonical axiom
`Category.assoc`. -/
recall Category.assoc

end CategoryTheory
