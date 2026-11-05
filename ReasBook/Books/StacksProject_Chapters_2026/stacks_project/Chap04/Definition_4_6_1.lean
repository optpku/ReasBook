module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Definition 4.6.1:
- primary domain: pullback squares and fibre-product universal properties in `CategoryTheory`;
- inspected canonical declarations: `IsPullback`, `IsPullback.exists_lift`, `IsPullback.hom_ext`,
  and `IsPullback.of_isLimit`;
- best owner abstraction: `IsPullback`;
- primitive-vs-derived split:
  primitive data: the four edges of the square together with the commutativity and limiting
    pullback witness already bundled by `IsPullback`;
  derived API: the existence clause `IsPullback.exists_lift`, the uniqueness clause
    `IsPullback.hom_ext`, and the converse constructor `IsPullback.of_isLimit`. -/

/- Source/core/bridge triage for Definition 4.6.1:
- source-facing: the Stacks condition that `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as the fibre
  product of `f : X ⟶ S` and `g : Y ⟶ S`;
- core/canonical: `IsPullback`;
- bridge/view: the universal-property projections `IsPullback.exists_lift` and
  `IsPullback.hom_ext`, and the limiting-cone constructor `IsPullback.of_isLimit`. -/

/- Definition 4.6.1: saying that morphisms `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as the fibre
product of `f : X ⟶ S` and `g : Y ⟶ S` is exactly the canonical pullback-square predicate
`IsPullback p q f g`. -/
#check IsPullback

/- Companion recall: the existence clause in the textbook universal property is the canonical
theorem `IsPullback.exists_lift`. -/
#check IsPullback.exists_lift

/- Companion recall: the uniqueness clause in the textbook universal property is the canonical
theorem `IsPullback.hom_ext`. -/
#check IsPullback.hom_ext

/- Companion recall: the converse direction from a limiting pullback cone is the canonical
constructor `IsPullback.of_isLimit`. -/
#check IsPullback.of_isLimit

end CategoryTheory
