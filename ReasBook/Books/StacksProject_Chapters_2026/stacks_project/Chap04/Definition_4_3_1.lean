module

public import Mathlib.CategoryTheory.Opposites
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for Definition 4.3.1:
- primary domain: opposite categories and the reversal of morphisms in category theory
- sampled canonical declarations:
  `Cᵒᵖ`,
  `Category.opposite`,
  `Quiver.Hom.unop`,
  `unop_comp`
- best owner abstraction: the opposite type `Cᵒᵖ` equipped with the canonical instance
  `Category.opposite`
- primitive data: no new primitive data beyond the opposite-type and opposite-category
  constructions already provided by mathlib
- derived API: unopposite morphisms and the reversed-composition formula
-/
/- Source/core/bridge triage for Definition 4.3.1:
- source-facing notion: the opposite category of `C` and its reversed morphisms
- core/canonical owner: the opposite type `Cᵒᵖ` with the canonical instance `Category.opposite`
- primitive data: no new primitive data beyond the existing opposite-type and opposite-category
  constructions from mathlib
- derived API: unopposite morphisms and the reversed-composition formula
-/

/-
Definition 4.3.1: for a category `C`, the opposite category is the canonical mathlib category
instance `Category.opposite` on the opposite type `Cᵒᵖ`.
-/
#check Cᵒᵖ

recall Category.opposite

/- Definition 4.3.1: a morphism in `Cᵒᵖ` canonically unops to a morphism in `C` with reversed
source and target. -/
recall Quiver.Hom.unop

/- In the opposite category, composition is reversed; this is the canonical formula
`unop_comp`. -/
recall unop_comp

end CategoryTheory
