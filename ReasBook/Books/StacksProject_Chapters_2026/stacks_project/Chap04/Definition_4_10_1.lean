module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} {a b : X ⟶ Y} {e : Z ⟶ X} {h : e ≫ a = e ≫ b}

/- Domain-style sampling for Definition 4.10.1:
- primary domain: equalizers in category theory, expressed as limit forks on a parallel pair;
- inspected owner declarations:
  `Fork.ofι`,
  `IsLimit`,
  `Fork.IsLimit.existsUnique`,
  `Fork.IsLimit.ofExistsUnique`;
- best owner abstraction: the textbook notion is already the canonical owner-level predicate
  `IsLimit (Fork.ofι e h)`;
- primitive data: the equalizing morphism `e : Z ⟶ X` and its compatibility `h : e ≫ a = e ≫ b`;
- derived API: the unique-factorization theorem and its converse constructor.

Source/core/bridge triage:
- `source-facing`: the textbook assertion that `e : Z ⟶ X` equalizes `a` and `b`;
- `core/canonical`: `IsLimit (Fork.ofι e h)`;
- `bridge/view`: `Fork.IsLimit.existsUnique` and `Fork.IsLimit.ofExistsUnique`. -/

/-
Definition 4.10.1: for parallel morphisms `a b : X ⟶ Y`, the textbook notion that
`e : Z ⟶ X` with `h : e ≫ a = e ≫ b` is an equalizer of `(a, b)` is exactly the canonical
mathlib notion that the fork `Fork.ofι e h` is limiting.
-/
#check IsLimit (Fork.ofι e h)

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `Fork.IsLimit.existsUnique`. -/
recall Fork.IsLimit.existsUnique

/- Companion recall: the converse direction is the canonical constructor
`Fork.IsLimit.ofExistsUnique`. -/
recall Fork.IsLimit.ofExistsUnique

end CategoryTheory.Limits
