module

public import Mathlib.CategoryTheory.Monoidal.Functor
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]

/- Domain sampling:
- Primary domain: monoidal category theory, specifically monoidal functors.
- Core/canonical declarations inspected:
  - `CategoryTheory.Functor.Monoidal`
  - `CategoryTheory.Functor.LaxMonoidal`
  - `CategoryTheory.Functor.Monoidal.εIso`
  - `CategoryTheory.Functor.Monoidal.μIso`
- Owner abstraction: `Functor.Monoidal`.
- Layer triage:
  - `source-facing`: Definition 4.43.2 is a recall-only item for the standard notion of a
    monoidal functor, with no extra source-defined data beyond the ambient owner;
  - `core/canonical`: `Functor.Monoidal`, whose primitive data is the monoidal functor structure;
  - `bridge/view`: the comparison isomorphisms `Monoidal.εIso` and `Monoidal.μIso`, derived from
    that owner abstraction.
- Primitive vs. derived:
  - primitive data: a monoidal functor `F : C ⥤ D`, encoded by the typeclass `F.Monoidal`;
  - derived API: the unit and tensor comparison isomorphisms `Monoidal.εIso` and
    `Monoidal.μIso`. -/

/- Definition 4.43.2: a functor of monoidal categories is the canonical mathlib owner
`Functor.Monoidal`. For a functor `F : C ⥤ D`, the typeclass `F.Monoidal` is the primitive
structure; the unit and tensor comparison isomorphisms belong to its derived API, so no parallel
local wrapper is needed here. -/
recall Monoidal

/- Companion recall: the unit comparison isomorphism of a monoidal functor is the canonical
derived construction `Monoidal.εIso`. -/
recall Monoidal.εIso

/- Companion recall: the tensorator isomorphism of a monoidal functor is the canonical derived
construction `Monoidal.μIso`. -/
recall Monoidal.μIso

end Functor
end CategoryTheory
