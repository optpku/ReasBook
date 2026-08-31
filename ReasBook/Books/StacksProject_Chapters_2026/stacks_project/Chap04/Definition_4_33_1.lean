module

public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/- Domain-style sampling for Definition 4.33.1:
- primary domain: fibered categories and universal properties of lifts over a base functor.
- inspected owner-level declarations:
  `Functor.IsStronglyCartesian`,
  `IsStronglyCartesian.universal_property'`,
  `IsStronglyCartesian.universal_property`,
  `IsStronglyCartesian.map`.
- core/canonical owner: `Functor.IsStronglyCartesian` from mathlib's fibered-category API.
- primitive data: the owner field `[p.IsHomLift f φ]` and the universal-property field
  `IsStronglyCartesian.universal_property'`.
- derived API: the associated universal-property lemmas such as `IsStronglyCartesian.universal_property`,
  `IsStronglyCartesian.map`, and the chapter bridge from fibredness to existence of strongly
  cartesian lifts.

Primitive-vs-derived split:
- primitive data: the functor `p`, the base arrow `f`, the total-category arrow `φ`, and the
  strongly-cartesian owner predicate on that data;
- derived API: the universal-property access lemma and the induced comparison morphisms built from
  that owner.

Source/core/bridge triage:
- `source-facing`: the Stacks notion of a strongly cartesian morphism.
- `core/canonical`: `Functor.IsStronglyCartesian`.
- `bridge/view`: later chapter lemmas that restate its behavior in slice categories or under
  composition, without introducing a parallel owner. -/

/- Definition 4.33.1: for a functor `p : 𝒳 ⥤ 𝒮`, a base morphism `f`, and a morphism `φ` lying
over it, the Stacks notion of a strongly cartesian morphism is the canonical owner
`Functor.IsStronglyCartesian`. -/
recall IsStronglyCartesian

/-- Companion bridge for Definition 4.33.1: the textbook universal-property formulation of a
strongly cartesian morphism is equivalent to the canonical owner predicate
`Functor.IsStronglyCartesian`. -/
theorem isStronglyCartesian_iff_universal_property
    (p : 𝒳 ⥤ 𝒮) {R S : 𝒮} {a b : 𝒳} (f : R ⟶ S) (φ : a ⟶ b) :
    p.IsStronglyCartesian f φ ↔
      p.IsHomLift f φ ∧
        ∀ {R' : 𝒮} {a' : 𝒳} (g : R' ⟶ R) (φ' : a' ⟶ b),
          p.IsHomLift (g ≫ f) φ' →
            ∃! χ : a' ⟶ a, p.IsHomLift g χ ∧ χ ≫ φ = φ' := by
  constructor
  · intro h
    letI : p.IsStronglyCartesian f φ := h
    refine ⟨inferInstance, fun g φ' hφ' ↦ ?_⟩
    letI : p.IsHomLift (g ≫ f) φ' := hφ'
    simpa using IsStronglyCartesian.universal_property p f φ g (g ≫ f) rfl φ'
  · rintro ⟨hφ, h⟩
    refine { toIsHomLift := hφ, universal_property' := ?_ }
    intro a' g φ' hφ'
    exact h g φ' hφ'

end CategoryTheory.Functor
