module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [SymmetricCategory D]

/- Domain sampling:
- Primary domain: monoidal category theory, specifically braided/symmetric monoidal functors.
- Core/canonical declarations inspected:
  - `CategoryTheory.Functor.Monoidal`
  - `CategoryTheory.Functor.LaxBraided`
  - `CategoryTheory.Functor.LaxBraided.braided`
  - `CategoryTheory.Functor.Braided`
- Owner abstraction: `Functor.Braided`.
- Layer triage:
  - `core/canonical`: `Functor.Braided`, whose primitive compatibility axiom is
    `Functor.LaxBraided.braided`;
  - `bridge/view`: the present item is only the symmetric specialization of that braided owner
    abstraction, so it should stay a direct recall rather than a separate local wrapper.
- Primitive vs. derived:
  - primitive data: a monoidal functor structure together with the braiding-compatibility axiom;
  - derived API: reassociated formulas such as `Functor.map_braiding`.
-/

/-
Definition 4.43.11 is the symmetric-monoidal special case of the canonical mathlib class
`Functor.Braided`: in a symmetric monoidal setting, no separate owner is needed beyond the
canonical braided-functor class. -/
recall Braided

/- Companion recall: the defining compatibility axiom is the canonical field
`Functor.LaxBraided.braided`, expressing that the tensorator commutes with the braiding. -/
recall LaxBraided.braided

/- Companion recall: in the strong-monoidal case this compatibility is also available in the
reassociated form `Functor.map_braiding`, derived from the same owner abstraction and specialized
here to symmetric source and target categories. -/
recall map_braiding

end Functor
end CategoryTheory
