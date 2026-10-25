module

public import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory.Limits

open HasColimitOfHasCoproductsOfHasCoequalizers

variable {C : Type u} [Category.{v} C]
variable {J : Type w} [SmallCategory J]
variable {F : J ⥤ C}
variable {c₁ : Cofan fun f : Σ p : J × J, p.1 ⟶ p.2 ↦ F.obj f.1.1}
variable {c₂ : Cofan F.obj}
variable (s t : c₁.pt ⟶ c₂.pt)
variable
  (hs : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ s = F.map f.2 ≫ c₂.ι.app ⟨f.1.2⟩)
  (ht : ∀ f : Σ p : J × J, p.1 ⟶ p.2, c₁.ι.app ⟨f⟩ ≫ t = c₂.ι.app ⟨f.1.1⟩)
variable {i : Cofork s t}

/- Domain-style sampling for Lemma 4.14.12:
- primary domain: constructing colimits from coproducts and coequalizers in category theory.
- sampled owner abstractions in
  `Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`:
  `HasColimitOfHasCoproductsOfHasCoequalizers.buildColimit`,
  `HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`,
  `colimitCoconeOfCoequalizerAndCoproduct`,
  `hasColimit_of_coequalizer_and_coproduct`.

Primitive-vs-derived split:
- primitive data: the coproduct cocones `c₁`, `c₂`, the comparison morphisms `s`, `t`, the
  compatibility equations `hs`, `ht`, and the coequalizer cofork `i`.
- derived API: the induced cocone `buildColimit s t hs ht i` and the owner-level proof
  `buildIsColimit`.

Source/core/bridge triage:
- `source-facing`: the textbook construction of a colimit cocone from coproducts and a
  coequalizer.
- `core/canonical`: `HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`.
- `bridge/view`: this file is a direct canonical recall of that owner theorem, not a parallel
  wrapper.
This rewrite targets the `core/canonical` layer by recalling the owner theorem directly. -/

/- Lemma 4.14.12: for a diagram `F : J ⥤ C`, if one chooses a coproduct of the objects `F.obj j`,
a coproduct of the source objects indexed by morphisms `u : j₁ ⟶ j₂`, and a coequalizer of the two
canonical maps whose `u`-components are the projection to `F.obj j₁` and the composite of `F.map u`
with the projection to `F.obj j₂`, then the induced cocone is a colimit cocone of `F`. This is
exactly the canonical mathlib theorem
`HasColimitOfHasCoproductsOfHasCoequalizers.buildIsColimit`. -/
recall buildIsColimit (t₁ : IsColimit c₁) (t₂ : IsColimit c₂) (hi : IsColimit i) :
    IsColimit (buildColimit s t hs ht i)

end CategoryTheory.Limits
