module

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Tactic.Recall

@[expose] public section

universe u v w

namespace CategoryTheory

variable {I : Type u} [Preorder I]
variable {C : Type v} [Category.{w} C]

/- Domain-style sampling for Definition 4.21.4:
- primary domain: directed diagrams and inverse diagrams in category theory, indexed by directed
  preorders;
- inspected owner declarations:
  - `IsDirectedOrder` and `CategoryTheory.isFiltered_of_directed_le_nonempty`,
  - the system-owner expressions `I ⥤ C` and `Iᵒᵈ ⥤ C` from `Definition_4_21_2`,
  - `nonempty_sections_of_finite_inverse_system` in
    `Mathlib/CategoryTheory/CofilteredSystem.lean`;
- best owner abstraction:
  - `source-facing`: directed systems and directed inverse systems on a directed set,
  - `core/canonical`: functors from the preorder category `I` and its order dual `Iᵒᵈ`,
  - `bridge/view`: the filtered/cofiltered structure induced on the preorder category by
    `[Nonempty I]` and `[IsDirectedOrder I]`;
- primitive data: exactly the stage objects and transition morphisms already carried by a functor
  `I ⥤ C` or `Iᵒᵈ ⥤ C`;
- derived API: the filtered/cofiltered comparison lemmas and limit/colimit theorems obtained from
  the directedness hypotheses on the index type.

Source/core/bridge triage for Definition 4.21.4:
- `source-facing`: systems and inverse systems indexed by a directed set.
- `core/canonical`: the functor type expressions `I ⥤ C` and `Iᵒᵈ ⥤ C`.
- `bridge/view`: the filtered/cofiltered structure induced by `[Nonempty I]` and
  `[IsDirectedOrder I]`. -/

/- Definition 4.21.4 (1): for a directed set `I`, meaning a preorder equipped with `[Nonempty I]`
and `[IsDirectedOrder I]` as in Definition 4.21.1, a directed system in `C` is still exactly the
canonical owner object `I ⥤ C`; directedness only specializes the index shape from Definition
4.21.2 and adds no new primitive data, so the checked owner expression itself lives under the
minimal preorder assumptions. -/
#check (I ⥤ C)

/- Definition 4.21.4 (2): likewise, for a directed set `I`, a directed inverse system in `C` is
exactly the canonical owner object `Iᵒᵈ ⥤ C`; directedness only specializes the inverse-system
owner of Definition 4.21.2, so the checked canonical type expression again needs only the
underlying preorder structure. -/
#check (Iᵒᵈ ⥤ C)

section

variable [Nonempty I] [IsDirectedOrder I]

/- Companion bridge: once the preorder index is nonempty and directed, its thin category is
canonically filtered via the owner instance
`CategoryTheory.isFiltered_of_directed_le_nonempty`. -/
recall CategoryTheory.isFiltered_of_directed_le_nonempty

/- Companion bridge: dually, the thin category on the order dual of a nonempty directed preorder is
canonically cofiltered. -/
#check (inferInstance : IsCofiltered Iᵒᵈ)

end

end CategoryTheory
