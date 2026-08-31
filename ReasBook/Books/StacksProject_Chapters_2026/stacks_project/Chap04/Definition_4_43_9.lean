module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/- Domain sampling:
- Primary domain: monoidal category theory, specifically braided and symmetric monoidal
  categories.
- Relevant owner/style declarations inspected:
  - project style anchor `CategoryTheory.MonoidalCategory` from Definition `4.43.1`, where a
    textbook notion is refined to a direct owner recall rather than a local wrapper;
  - `CategoryTheory.BraidedCategory`;
  - `CategoryTheory.SymmetricCategory`;
  - `CategoryTheory.SymmetricCategory.braiding_swap_eq_inv_braiding`.
- Owner abstraction: `SymmetricCategory C`.
- Layer triage:
  - `core/canonical`: `SymmetricCategory C`, extending the braided owner by the symmetry axiom;
  - `bridge/view`: none needed here, since Definition 4.43.9 only recalls the canonical owner.
- Primitive vs. derived:
  - primitive data: the inherited braided structure together with the axiom
    `SymmetricCategory.symmetry`;
  - derived API: the source-facing comparison
    `SymmetricCategory.braiding_swap_eq_inv_braiding`.
-/

/- Definition 4.43.9: the Stacks notion of a symmetric monoidal category is the canonical
mathlib class `SymmetricCategory C`. Concretely, on top of the fixed monoidal structure, this is
a braided structure whose braiding is involutive. -/
recall SymmetricCategory

/- Companion recall: the source-facing symmetry condition is the canonical theorem saying that
the swapped braiding is the inverse braiding. -/
recall SymmetricCategory.braiding_swap_eq_inv_braiding

end CategoryTheory
