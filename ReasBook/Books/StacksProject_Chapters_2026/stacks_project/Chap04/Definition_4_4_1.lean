module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y P : C} {p : P ⟶ X} {q : P ⟶ Y}

/- Domain-style sampling for Definition 4.4.1:
- primary domain: binary products in category theory, expressed via limit cones on the walking-pair
  diagram;
- inspected owner declarations:
  `BinaryFan.mk`,
  `IsLimit`,
  `IsLimit.existsUnique`,
  `BinaryFan.isLimitMk`;
- best owner abstraction: the textbook statement is already the canonical owner-level predicate
  `IsLimit (BinaryFan.mk p q)`;
- primitive data: the two morphisms `p : P ⟶ X` and `q : P ⟶ Y`, assembled into the binary fan
  `BinaryFan.mk p q`;
- derived API: the universal factorization theorem `IsLimit.existsUnique` and the converse
  constructor `BinaryFan.isLimitMk`.

Source/core/bridge triage:
- `source-facing`: the statement that `p` and `q` exhibit `P` as a product of `X` and `Y`;
- `core/canonical`: `IsLimit (BinaryFan.mk p q)`;
- `bridge/view`: `IsLimit.existsUnique` and `BinaryFan.isLimitMk`. -/

/- Definition 4.4.1: morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as a product of `X` and
`Y` precisely when the binary fan `BinaryFan.mk p q` is limiting. -/
#check IsLimit (BinaryFan.mk p q)

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsLimit.existsUnique`. -/
recall IsLimit.existsUnique

/- Companion recall: the converse direction from the textbook `∃!` universal property to a
limiting binary fan is the binary-product-specific constructor `BinaryFan.isLimitMk`. -/
recall BinaryFan.isLimitMk

end CategoryTheory.Limits
