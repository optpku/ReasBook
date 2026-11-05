module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] {X : C}

/- Domain-style sampling for Definition 4.12.1:
- primary domain: initial and terminal objects in a category;
- inspected owner declarations:
  `IsInitial`,
  `IsTerminal`,
  `isInitialEquivUnique`,
  `isTerminalEquivUnique`;
- owner abstraction: the canonical owner predicates `IsInitial X` and `IsTerminal X`;
- primitive data: only the object `X`;
- derived API: the unique-morphism characterizations given by
  `isInitialEquivUnique` and `isTerminalEquivUnique`.

Source/core/bridge triage:
- `source-facing`: the textbook predicates that an object is initial or final;
- `core/canonical`: `IsInitial X` and `IsTerminal X`;
- `bridge/view`: the equivalences with the unique-morphism formulations. -/

/- Definition 4.12.1 (1), owner recall: the textbook notion of an initial object is the canonical
mathlib notion `IsInitial X`. -/
#check IsInitial X

/- Definition 4.12.1 (2), owner recall: the textbook notion of a final object is the canonical
mathlib notion `IsTerminal X`. -/
#check IsTerminal X

/- Companion bridge: the textbook unique-morphism characterization of an initial object is the
canonical specialization of `isInitialEquivUnique` to the empty diagram. -/
#check (isInitialEquivUnique (Functor.empty C) X : IsInitial X ≃ ∀ Y, Unique (X ⟶ Y))

/- Companion bridge: the textbook unique-morphism characterization of a terminal object is the
canonical specialization of `isTerminalEquivUnique` to the empty diagram. -/
#check (isTerminalEquivUnique (Functor.empty C) X : IsTerminal X ≃ ∀ Y, Unique (Y ⟶ X))

end CategoryTheory.Limits
