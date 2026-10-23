module

public import Mathlib.CategoryTheory.Equivalence
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory
namespace Functor

variable {A : Type u₁} [Category.{v₁} A]
variable {B : Type u₂} [Category.{v₂} B]

/- Domain-style sampling for Definition 4.2.17:
- `Functor.IsEquivalence` is the owner predicate for a functor being an equivalence of
  categories.
- `Functor.IsEquivalence.mk'` is the canonical constructor from a quasi-inverse together with the
  unit and counit isomorphisms.
- `Functor.inv` is the derived quasi-inverse attached to the owner predicate.
- `Functor.asEquivalence` upgrades the owner predicate to the canonical equivalence object
  `A ≌ B`.

Primitive-vs-derived split:
- primitive data: none in this file; the notion is already owned upstream by the `Prop`-valued
  class `Functor.IsEquivalence`.
- derived API: the source-facing quasi-inverse characterization below, exposing the quasi-inverse
  functor together with existential unit/counit isomorphism data, recovered from `Functor.inv`,
  `Functor.asEquivalence`, and `Functor.IsEquivalence.mk'`. -/

/- Source/core/bridge triage for Definition 4.2.17:
- `source-facing`: the textbook quasi-inverse formulation of equivalence of categories.
- `core/canonical`: `Functor.IsEquivalence`.
- `bridge/view`: `isEquivalence_iff_exists_quasiInverse`. -/

/- Definition 4.2.17: the canonical owner abstraction for an equivalence of categories carried by a
functor is `Functor.IsEquivalence`. -/
recall Functor.IsEquivalence

/- Bridge/view: this source-facing quasi-inverse formulation is a companion specification of the
owner abstraction `Functor.IsEquivalence`, not a second owner. The `Nonempty` wrappers record the
existence of the unit and counit isomorphisms while keeping the statement in `Prop`. If `F` is an
equivalence, use `F.inv` together with the unit and counit isomorphisms of `F.asEquivalence`;
conversely, chosen such isomorphisms give `F.IsEquivalence` via `Functor.IsEquivalence.mk'`. -/
/-- Companion bridge for Definition 4.2.17: a functor is an equivalence of categories exactly when
it admits a quasi-inverse together with unit and counit isomorphisms. -/
theorem isEquivalence_iff_exists_quasiInverse (F : A ⥤ B) :
    F.IsEquivalence ↔
      ∃ G : B ⥤ A, Nonempty (𝟭 A ≅ F ⋙ G) ∧ Nonempty (G ⋙ F ≅ 𝟭 B) := by
  constructor
  · intro hF
    letI := hF
    exact ⟨F.inv, ⟨F.asEquivalence.unitIso⟩, ⟨F.asEquivalence.counitIso⟩⟩
  · rintro ⟨G, ⟨η⟩, ⟨ε⟩⟩
    exact Functor.IsEquivalence.mk' G η ε

end Functor
end CategoryTheory
