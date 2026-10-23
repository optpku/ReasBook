module

public import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace CategoryTheory

open Bicategory

/- Domain-style sampling for Definition 4.29.1:
- primary domain: bicategory theory, specializing the textbook notion of a strict `2`-category;
- sampled owner-level declarations:
  `Bicategory`,
  `Bicategory.Strict`,
  `postcomposing`,
  `associatorNatIsoMiddle`;
- best owner abstraction: `Bicategory` is the ambient owner carrying objects, hom-categories,
  `2`-morphisms, whiskering, associator/unitors, and the exchange law, while `Strict` is the
  extra source-facing predicate expressing that this bicategory is a strict `2`-category;
- primitive-vs-derived split:
  primitive data: the ambient bicategory structure `Bicategory B`, together with the strictness
    predicate `Strict B`;
  derived API: the curried composition functor, the associator/unitor natural isomorphisms, the
    exchange law, and the induced ordinary category structure on objects and `1`-morphisms.

Source/core/bridge triage:
- `source-facing`: the textbook notion of a strict `2`-category, namely a bicategory with the
  extra strictness condition, and its horizontal composition data;
- `core/canonical`: `Bicategory`, `Strict`, `postcomposing`, `associatorNatIsoMiddle`,
  `leftUnitorNatIso`, `rightUnitorNatIso`, `whisker_exchange`, `StrictBicategory.category`;
- `bridge/view`: none; the source notions are already owned by the ambient bicategory API. -/

/- Definition 4.29.1: the ambient owner of the objects, `1`-morphisms, `2`-morphisms, whiskering,
associator/unitors, and exchange law of a `2`-category is the canonical mathlib class
`CategoryTheory.Bicategory B`. -/
recall Bicategory

/- Definition 4.29.1: the extra condition making a bicategory into a strict `2`-category is the
canonical strictness predicate `Strict B`. Thus the Stacks notion is expressed by the pair of
assumptions `[Bicategory B] [Strict B]`. -/
recall Strict

variable {B : Type u} [Bicategory B]

/- Definition 4.29.1: for each triple of objects, the textbook composition functor
`Mor(y, z) × Mor(x, y) ⥤ Mor(x, z)` is the canonical curried functor
`postcomposing x y z`. Its action on `2`-morphisms is horizontal composition. -/
recall postcomposing

/- Definition 4.29.1: associativity of horizontal composition of `2`-morphisms is the canonical
middle associator natural isomorphism of the bicategory composition functors. -/
recall associatorNatIsoMiddle

/- Definition 4.29.1: the identity `2`-morphism of an identity `1`-morphism acts as a left unit
for horizontal composition via the canonical left unitor natural isomorphism. -/
recall leftUnitorNatIso

/- Definition 4.29.1: the identity `2`-morphism of an identity `1`-morphism acts as a right unit
for horizontal composition via the canonical right unitor natural isomorphism. -/
recall rightUnitorNatIso

/- Definition 4.29.1: the two standard whiskering formulas for horizontal composition of
`2`-morphisms agree by the canonical bicategorical exchange law. -/
recall whisker_exchange

variable [Strict B]

/- In a strict `2`-category, the objects and `1`-morphisms form the canonical ordinary category
given by `StrictBicategory.category`. -/
recall StrictBicategory.category

end CategoryTheory
