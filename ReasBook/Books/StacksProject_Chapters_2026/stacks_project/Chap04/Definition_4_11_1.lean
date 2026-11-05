module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y Z : C} {a b : X ⟶ Y} {c : Y ⟶ Z} {h : a ≫ c = b ≫ c}

/- Domain-style sampling for Definition 4.11.1:
- primary domain: coequalizers in category theory, expressed as colimit coforks on a parallel
  pair;
- inspected owner declarations:
  `Cofork.ofπ`,
  `IsColimit`,
  `Cofork.IsColimit.existsUnique`,
  `Cofork.IsColimit.ofExistsUnique`;
- best owner abstraction: the textbook statement is already the canonical owner-level predicate
  `IsColimit (Cofork.ofπ c h)`;
- primitive data: the coequalizing morphism `c : Y ⟶ Z` and its compatibility
  `h : a ≫ c = b ≫ c`;
- derived API: the unique-factorization theorem and its converse constructor.
-/

/- Source/core/bridge triage for Definition 4.11.1:
- `source-facing`: the textbook assertion that `c : Y ⟶ Z` is a coequalizer of `(a, b)`.
- `core/canonical`: `IsColimit (Cofork.ofπ c h)`.
- `bridge/view`: `Cofork.IsColimit.existsUnique` and `Cofork.IsColimit.ofExistsUnique`. -/

/- Definition 4.11.1: for parallel morphisms `a b : X ⟶ Y`, the textbook notion that
`c : Y ⟶ Z` is a coequalizer of `(a, b)` is exactly the canonical mathlib notion that the
cofork `Cofork.ofπ c h` is colimiting. -/
#check IsColimit (Cofork.ofπ c h)

/- Companion recall: the unique-factorization clause in the textbook coequalizer universal
property is the canonical theorem `Cofork.IsColimit.existsUnique`. -/
recall Cofork.IsColimit.existsUnique

/- Companion recall: the converse direction from the textbook universal property to a colimiting
cofork is the canonical constructor `Cofork.IsColimit.ofExistsUnique`. -/
recall Cofork.IsColimit.ofExistsUnique

end CategoryTheory.Limits
