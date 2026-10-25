module

import Mathlib.CategoryTheory.Category.Preorder

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C]

/- Domain-style sampling for Definition 4.21.2:
- primary domain: preorder-indexed diagrams in category theory;
- inspected owner declarations:
  - `Preorder` in `Definition_4_21_1`,
  - the functor category expression `I ⥤ C`,
  - the order-dual indexing expression `Iᵒᵈ ⥤ C`,
  - the downstream inverse-limit owner API
    `nonempty_sections_of_finite_inverse_system : (Jᵒᵖ ⥤ Type v) → _` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`;
- best owner abstraction:
  - `source-facing`: direct systems as `I ⥤ C`, inverse systems as `Iᵒᵈ ⥤ C`,
  - `core/canonical`: the same functor type expressions on the thin category of a preorder and on
    its order dual,
  - `bridge/view`: the opposite-category presentation `Iᵒᵖ ⥤ C` used by some downstream limit
    APIs;
- primitive data: stage objects together with transition morphisms for comparable indices;
- derived API: identity and composition compatibilities from the functor laws.

Source/core/bridge triage for Definition 4.21.2:
- `source-facing`: systems and inverse systems on a preordered set.
- `core/canonical`: functors out of the preorder category and its order dual.
- `bridge/view`: the equivalent opposite-category presentation for inverse systems. -/

/- Definition 4.21.2 (1): a system over a preordered set `I` in a category `C` is exactly a
functor `I ⥤ C`, where `I` is viewed as the thin category attached to the preorder. The primitive
data are the stage objects `F.obj i` and transition morphisms `F.map (homOfLE hij)`, while the
compatibilities are derived from the functor laws. -/
#check (I ⥤ C)

/- Definition 4.21.2 (2): an inverse system over a preordered set `I` in a category `C` is
exactly a functor `Iᵒᵈ ⥤ C`. This keeps the source indices on the original preorder while
reversing the transition direction without extra `op`/`unop` bookkeeping. The equivalent
contravariant presentation `Iᵒᵖ ⥤ C` is a bridge view for opposite-category limit APIs, not a
second owner. -/
#check (Iᵒᵈ ⥤ C)

end CategoryTheory
