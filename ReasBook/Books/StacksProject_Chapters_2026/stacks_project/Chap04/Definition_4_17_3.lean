module

public import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Tactic.Recall
public import stacks_project.Chap04.Definition_4_16_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe vI vJ uI uJ

namespace CategoryTheory
namespace Functor

variable {I : Type uI} [Category.{vI} I]
variable {J : Type uJ} [Category.{vJ} J]

/- Domain-style sampling for Definition 4.17.3:
- primary domain: initial functors and connected costructured-arrow categories.
- inspected owner/bridge declarations:
  `CategoryTheory.Functor.Initial`,
  `CategoryTheory.IsConnected`,
  `CategoryTheory.isConnected_iff_nonempty_and_zigzag`,
  `final_iff_nonempty_structuredArrow_and_zigzag`.
- best owner abstraction: `Functor.Initial`.
- primitive-vs-derived split:
  primitive data: for each `y : J`, the connectedness witness
    `IsConnected (CostructuredArrow H y)` stored by the owner `Functor.Initial`;
  derived API: the source-facing nonemptiness-and-zigzag criterion for
    `CostructuredArrow H y`.
- layer triage:
  - `source-facing`: the objectwise nonempty-and-zigzag criterion for `CostructuredArrow H y`;
  - `core/canonical`: `Functor.Initial`;
  - `bridge/view`: `initial_iff_nonempty_costructuredArrow_and_zigzag`.

This item should therefore keep `Functor.Initial` as the main owner entry and expose the
textbook zigzag formulation only as a companion theorem. -/

/- Definition 4.17.3: a functor `H : I ⥤ J` is initial when for every object `y : J`, the
category of arrows `H.obj x ⟶ y` is connected. This is the canonical mathlib class
`Functor.Initial`. -/
recall Initial

/-- Bridge/view companion to Definition 4.17.3: the textbook zigzag description of an initial
functor says that for each `y : J`, there is at least one morphism `H.obj x ⟶ y`, and any two
such pairs `(x, H.obj x ⟶ y)` are connected by a zigzag of morphisms in
`CostructuredArrow H y`. -/
-- Proof sketch: unwind `Functor.Initial` as connectedness of each `CostructuredArrow H y`, then
-- use the standard zigzag characterization of connected categories from Definition `4.16.1`.
theorem initial_iff_nonempty_costructuredArrow_and_zigzag (H : I ⥤ J) :
    H.Initial ↔
      ∀ y : J,
        Nonempty (CostructuredArrow H y) ∧ ∀ a b : CostructuredArrow H y, Zigzag a b := by
  constructor
  · intro h y
    simpa using isConnected_iff_nonempty_and_zigzag.mp (h.out y)
  · intro h
    exact ⟨fun y ↦ isConnected_iff_nonempty_and_zigzag.mpr (h y)⟩

end Functor
end CategoryTheory
