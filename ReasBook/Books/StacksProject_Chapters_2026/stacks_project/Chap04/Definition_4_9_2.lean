module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/-
Domain-style sampling for Definition 4.9.2:
- primary domain: pushout squares in `CategoryTheory`.
- inspected declarations: `CommSq`, `IsPushout`, `Square.IsPushout`, and `IsPushout.toCommSq`.
- best owner abstraction: `IsPushout`.
- primitive-vs-derived split:
  primitive data: the four edges of the square together with commutativity and the pushout
    universal property packaged by `IsPushout`;
  derived API: the projection `IsPushout.toCommSq` and the bundled-square view
    `Square.IsPushout`. -/

/- Source/core/bridge triage for Definition 4.9.2:
- source-facing: the textbook adjective that a commutative square is cocartesian.
- core/canonical: `IsPushout`.
- bridge/view: `IsPushout.toCommSq` and `Square.IsPushout`. -/

/-
Definition 4.9.2: a commutative square
`y ⟶ z`
`↓   ↓`
`x ⟶ w`
in a category is cocartesian if `w` together with the morphisms `x ⟶ w` and `z ⟶ w` forms a
pushout of `y ⟶ x` and `y ⟶ z`. This is the canonical mathlib notion `IsPushout`; the bundled
square view `Square.IsPushout` is only a later bridge/view on top of it.
-/
#check IsPushout

/- The canonical cocartesian-square notion already packages the underlying commutative square via
`IsPushout.toCommSq`. -/
#check IsPushout.toCommSq

end CategoryTheory
