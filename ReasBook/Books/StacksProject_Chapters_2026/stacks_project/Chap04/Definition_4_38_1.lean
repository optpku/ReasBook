module

public import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 4.38.1:
- primary domain: discrete categories;
- inspected owner-level declarations:
  `CategoryTheory.IsDiscrete`,
  `CategoryTheory.obj_ext_of_isDiscrete`,
  `CategoryTheory.isIso_of_isDiscrete`,
  `CategoryTheory.Discrete.isDiscrete`;
- best owner abstraction: `CategoryTheory.IsDiscrete`;
- primitive owner data: `IsDiscrete.subsingleton` and `IsDiscrete.eq_of_hom`;
- derived API: `obj_ext_of_isDiscrete`, `isIso_of_isDiscrete`, and the source wording that every
  morphism is a transported identity, recovered directly from the primitive owner data. -/

/- Definition 4.38.1: a category is discrete exactly when every morphism is an identity morphism
after identifying its source and target. This is the canonical mathlib class
`CategoryTheory.IsDiscrete`. -/
recall IsDiscrete

/- Source/core/bridge triage for Definition 4.38.1:
- core/canonical owner: `CategoryTheory.IsDiscrete`;
- source-facing layer: this item is recall-only, and the textbook wording is recovered directly
  from `IsDiscrete.eq_of_hom` together with subsingleton hom-spaces;
- primitive owner data: `IsDiscrete.subsingleton` and `IsDiscrete.eq_of_hom`;
- derived API: `obj_ext_of_isDiscrete` and the companion bridge theorem below expressing each
  morphism as the transported identity. -/

/- Companion bridge: the textbook assertion that any morphism identifies its source and target is
the owner lemma `obj_ext_of_isDiscrete`. -/
recall obj_ext_of_isDiscrete

/- Companion bridge: in a discrete category every morphism is the identity after transporting
along the canonical equality of its source and target. This matches the source wording directly
without introducing a parallel owner. -/
theorem hom_eq_eqToHom_of_isDiscrete [IsDiscrete C] {X Y : C} (f : X ⟶ Y) :
    f = eqToHom (obj_ext_of_isDiscrete f) :=
  Subsingleton.elim _ _

end CategoryTheory
