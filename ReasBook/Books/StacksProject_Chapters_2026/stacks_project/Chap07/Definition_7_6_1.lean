module

import Mathlib.Tactic.Recall
public import stacks_project.Chap07.Definition_7_8_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Definition 7.6.1:
- primary domain: type-indexed families of arrows with common target in a category, viewed through
  slice categories;
- inspected owner declarations:
  `CategoryTheory.Over`,
  `CategoryTheory.SemiRepresentableFamily`,
  `CategoryTheory.SemiRepresentableFamily.Over`,
  `CategoryTheory.SemiRepresentableFamily.Over.forget`;
- best owner abstraction: `SemiRepresentableFamily.Over U`, i.e. a semi-representable family in the
  slice category `C / U`;
- primitive data: only the common target `U` and the family of objects of `C / U`, equivalently an
  index type together with arrows to `U`;
- derived API: forgetting to the underlying semi-representable family in `C` via
  `SemiRepresentableFamily.Over.forget`.

Source/core/bridge triage:
- `source-facing`: the textbook notion of a family of morphisms with fixed target `U`;
- `core/canonical`: `SemiRepresentableFamily.Over U`;
- `bridge/view`: the equivalent indexed-arrow presentation, obtained by viewing an object of
  `SemiRepresentableFamily.Over U` as a type-indexed family of objects of `Over U`.
-/

/- Definition 7.6.1: for an object `U` of a category `C`, a family of morphisms with fixed target
`U` is canonically modeled by `SemiRepresentableFamily.Over U`, i.e. by a family of objects of the
slice category `C / U`, equivalently an index type `I` together with arrows `Uᵢ ⟶ U` for each
`i : I`. -/
recall SemiRepresentableFamily.Over

end CategoryTheory
