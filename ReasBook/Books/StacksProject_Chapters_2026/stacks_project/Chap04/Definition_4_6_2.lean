module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace CategoryTheory

/- Domain-style sampling for Definition 4.6.2:
- primary domain: pullback squares in `CategoryTheory`.
- inspected declarations: `CommSq`, `IsPullback`, `Square.IsPullback`, and `IsPullback.toCommSq`.
- best owner abstraction: `IsPullback`.
- primitive-vs-derived split:
  primitive data: the four edges of the square together with commutativity and the limiting
    pullback-cone witness packaged by `IsPullback`;
  derived API: the projection `IsPullback.toCommSq` and the bundled-square view
    `Square.IsPullback`. -/

/- Source/core/bridge triage for Definition 4.6.2:
- source-facing: the textbook adjective that a commutative square is cartesian.
- core/canonical: `IsPullback`.
- bridge/view: `IsPullback.toCommSq` and `Square.IsPullback`. -/

/-
Definition 4.6.2: a commutative square
`w ⟶ z`
`↓   ↓`
`x ⟶ y`
in a category is cartesian if `w` together with the morphisms `w ⟶ x` and `w ⟶ z` forms a fibre
product of `x ⟶ y` and `z ⟶ y`. This is the canonical mathlib notion `IsPullback`; the bundled
square view `Square.IsPullback` is only a later bridge/view on top of it. -/
#check IsPullback

/- The canonical cartesian-square notion already packages the underlying commutative square via
`IsPullback.toCommSq`. -/
#check IsPullback.toCommSq

end CategoryTheory
