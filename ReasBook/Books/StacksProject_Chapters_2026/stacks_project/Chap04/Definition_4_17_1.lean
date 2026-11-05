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

/- Domain-style sampling for Definition 4.17.1:
- primary domain: final/cofinal functors and connected structured-arrow categories.
- inspected owner declarations:
  `CategoryTheory.Functor.Final`,
  `CategoryTheory.IsConnected`,
  `CategoryTheory.isConnected_iff_nonempty_and_zigzag`.
- owner abstraction: the mathlib class `Functor.Final`.
- primitive data: for each `y : J`, the connectedness witness `IsConnected (StructuredArrow y H)`.
- derived API: the source-facing nonemptiness-and-zigzag characterization of each
  `StructuredArrow y H`.

Source/core/bridge triage:
- `source-facing`: the textbook description by existence of an object over `y` and zigzag
  connectivity between any two such objects;
- `core/canonical`: `Functor.Final`;
- `bridge/view`: `final_iff_nonempty_structuredArrow_and_zigzag`.

This item should therefore keep `Functor.Final` as the main owner entry and expose the textbook
zigzag formulation only as a companion theorem. -/

/- Definition 4.17.1: a functor `H : I ⥤ J` is cofinal when for every object `y : J`, the
category of pairs `(x, y ⟶ H.obj x)` is connected; this is the canonical mathlib class
`CategoryTheory.Functor.Final`. -/
recall Final

/-- Bridge/view companion to Definition 4.17.1: the textbook zigzag description of a cofinal
functor says that for each `y : J`, there is at least one morphism `y ⟶ H.obj x`, and any two
such pairs `(x, y ⟶ H.obj x)` are connected by a zigzag of morphisms in `StructuredArrow y H`. -/
-- Proof sketch: unwind `Functor.Final` as connectedness of each `StructuredArrow y H`, then use
-- the standard zigzag characterization of connected categories from Definition `4.16.1`.
theorem final_iff_nonempty_structuredArrow_and_zigzag (H : I ⥤ J) :
    H.Final ↔
      ∀ y : J,
        Nonempty (StructuredArrow y H) ∧
          ∀ a b : StructuredArrow y H, Zigzag a b := by
  constructor
  · intro h y
    simpa using isConnected_iff_nonempty_and_zigzag.mp (h.out y)
  · intro h
    exact ⟨fun y ↦ isConnected_iff_nonempty_and_zigzag.mpr (h y)⟩

end Functor
end CategoryTheory
