module

public import stacks_project.Chap04.Definition_4_35_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS vS

namespace CategoryTheory

open Bicategory
open scoped Bicategory

variable {C : Type u} [Category.{v} C]

namespace FibredInGroupoidsOver

/- Domain-style sampling for Definition 4.40.1:
- primary domain: representable categories fibred in groupoids over a fixed base category.
- inspected owner-level declarations:
  `FibredInGroupoidsOver.ofFunctor`,
  `Bicategory.Equivalence`,
  `FibredInGroupoidsMor.exists_equivalence`,
  `FibredInGroupoidsOver.hom_isEquivalenceOverBase`.
- best owner abstraction: representability is source-facing existence of a bicategorical
  equivalence over `C` from `X` to a slice projection `ofFunctor (Over.forget U)`;
  a presentation morphism `j : X ⟶ ofFunctor (Over.forget U)` together with
  `FibredInGroupoidsMor.IsEquivalenceOverBase j` is derived bridge data rather than the primary
  public owner shape.

Source/core/bridge triage:
- `source-facing`: `FibredInGroupoidsOver.IsRepresentable`;
- `core/canonical`: `Bicategory.Equivalence X (ofFunctor (Over.forget U))`;
- `bridge/view`: a presentation morphism `j : X ⟶ ofFunctor (Over.forget U)` together with
  `FibredInGroupoidsMor.IsEquivalenceOverBase j`, and the conversions
  `FibredInGroupoidsMor.exists_equivalence j` and `hom_isEquivalenceOverBase`.

Primitive-vs-derived split:
- primitive witness data: the representing object `U : C` and an equivalence
  `X ≌ ofFunctor (Over.forget U)`;
- derived API: the forward presentation morphism `e.hom` with owner proof
  `hom_isEquivalenceOverBase e`, and conversely the equivalence
  produced existentially by `FibredInGroupoidsMor.exists_equivalence j`. -/

/-- Definition 4.40.1: a category fibred in groupoids over `C` is representable if it is
equivalent over `C` to a slice projection `Over.forget U : Over U ⥤ C`. -/
def IsRepresentable (X : FibredInGroupoidsOver C) : Prop :=
  ∃ U : C, Nonempty (X ≌ ofFunctor (Over.forget U))

/-- Companion bridge for Definition 4.40.1: representability is equivalently the existence of a
presentation morphism over `C` whose underlying based functor is an equivalence over the base. -/
theorem isRepresentable_iff_exists_presentation
    (X : FibredInGroupoidsOver C) :
    X.IsRepresentable ↔
      ∃ (U : C) (j : X ⟶ ofFunctor (Over.forget U)),
        FibredInGroupoidsMor.IsEquivalenceOverBase j := by
  unfold IsRepresentable
  constructor
  · rintro ⟨U, ⟨e⟩⟩
    exact ⟨U, e.hom, hom_isEquivalenceOverBase e⟩
  · rintro ⟨U, j, hj⟩
    rcases FibredInGroupoidsMor.exists_equivalence j hj with ⟨e, rfl⟩
    exact ⟨U, ⟨e⟩⟩

/-- The slice projection `C/U ⥤ C` is a representable category fibred in groupoids. -/
theorem over_forget_isRepresentable (U : C) :
    (ofFunctor (Over.forget U)).IsRepresentable := by
  unfold IsRepresentable
  exact ⟨U, ⟨Bicategory.Equivalence.id _⟩⟩

end FibredInGroupoidsOver

end CategoryTheory
