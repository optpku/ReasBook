module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {S : Type u₁} [Category.{v₁} S]
variable {C : Type u₂} [Category.{v₂} C]

/- Domain-style sampling for Definition 4.32.2:
- `Functor.Fiber` is the canonical mathlib owner abstraction for the fibre category of a functor.
- `Functor.Fiber.mk` and `Functor.Fiber.homMk` are the canonical constructors for the textbook
  object-lift and identity-over-base morphism data in a fibre.
- `Functor.IsHomLift` is the canonical owner abstraction for a morphism in the total category
  lying over a prescribed base morphism.
- `IsHomLift.commSq` and `IsHomLift.of_commSq` are the canonical bridge between the owner
  predicate and the textbook commutative-square presentation.

Primitive-vs-derived split:
- primitive data: an object `x : S` together with an equality `p.obj x = U`, and a morphism
  `φ : x ⟶ y` together with the predicate that it lifts a specified base map.
- derived API: the fibre category structure on `Functor.Fiber p U`, the canonical constructors
  `Functor.Fiber.mk` and `Functor.Fiber.homMk`, and the commutative-square reformulation of
  `Functor.IsHomLift`. -/

/- Source/core/bridge triage for Definition 4.32.2:
- `source-facing`: the textbook notions of fibre object, fibre morphism, and morphism lift over a
  fixed base arrow.
- `core/canonical`: `Functor.Fiber p U` and `Functor.IsHomLift p f φ`.
- `bridge/view`: `IsHomLift.commSq` and `IsHomLift.of_commSq`. -/

/- Definition 4.32.2(1): for a functor `p : S ⥤ C` and an object `U : C`, the fibre category
over `U` is the canonical mathlib category `Functor.Fiber p U`. -/
recall Functor.Fiber

/- Definition 4.32.2(2): a lift of an object `U : C` is canonically an object of
`Functor.Fiber p U`, built from a proof `h : p.obj x = U` via `Functor.Fiber.mk h`. -/
recall Functor.Fiber.mk

/- Definition 4.32.2(2): a morphism in the fibre category over `U` is canonically obtained from a
morphism `φ` lying over `𝟙 U` via `Functor.Fiber.homMk p U φ`. -/
recall Functor.Fiber.homMk

/- Definition 4.32.2(3): a lift of a morphism `f : V ⟶ U` is the canonical predicate
`Functor.IsHomLift p f φ`. -/
recall Functor.IsHomLift

/- Definition 4.32.2(3): from a hom lift one canonically gets the textbook commutative square
after transporting source and target along the induced equalities. -/
recall IsHomLift.commSq

/- Definition 4.32.2(3): conversely, the textbook commutative square yields the canonical hom-lift
predicate via `IsHomLift.of_commSq`. -/
recall IsHomLift.of_commSq

end CategoryTheory
