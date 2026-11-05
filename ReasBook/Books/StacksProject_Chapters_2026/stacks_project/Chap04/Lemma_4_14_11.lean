module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Limits

open HasLimitOfHasProductsOfHasEqualizers

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]
variable {F : J ⥤ C}
variable {c₁ : Fan F.obj}
variable {c₂ : Fan fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.2}
variable (s t : c₁.pt ⟶ c₂.pt)
variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, s ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.1⟩ ≫ F.map f.2)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, t ≫ c₂.π.app ⟨f⟩ = c₁.π.app ⟨f.1.2⟩)
variable {i : Fork s t}

/- Domain-style sampling for Lemma 4.14.11:
- primary domain: constructing limits from products and equalizers in category theory.
- sampled owner abstractions in
  `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`:
  `HasLimitOfHasProductsOfHasEqualizers.buildLimit`,
  `HasLimitOfHasProductsOfHasEqualizers.buildIsLimit`,
  `limitConeOfEqualizerAndProduct`,
  `hasLimit_of_equalizer_and_product`.

Primitive-vs-derived split:
- primitive data: the product cones `c₁`, `c₂`, the comparison morphisms `s`, `t`, the
  compatibility equations `hs`, `ht`, and the equalizer fork `i`.
- derived API: the induced cone `buildLimit s t hs ht i` and the owner-level proof
  `buildIsLimit`.

Source/core/bridge triage:
- `source-facing`: the textbook construction of a limit cone from products and an equalizer.
- `core/canonical`: `buildIsLimit`.
- `bridge/view`: this file is a direct canonical recall of that owner theorem, not a parallel
  wrapper.
This rewrite targets the `core/canonical` layer by recalling the owner theorem directly. -/

/- Lemma 4.14.11: for a diagram `F : J ⥤ C`, if one chooses a product of the objects `F.obj j`,
a product of the target objects indexed by morphisms `u : j₁ ⟶ j₂`, and an equalizer of the two
canonical maps whose `u`-components are the projection to `F.obj j₂` and the composite of the
projection to `F.obj j₁` with `F.map u`, then the induced cone is a limit cone of `F`. This is
exactly the canonical mathlib theorem
`HasLimitOfHasProductsOfHasEqualizers.buildIsLimit`. -/
recall buildIsLimit (t₁ : IsLimit c₁) (t₂ : IsLimit c₂) (hi : IsLimit i) :
    IsLimit (buildLimit s t hs ht i)

end CategoryTheory.Limits
