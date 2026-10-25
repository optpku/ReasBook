module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]
variable (S : MorphismProperty C)

/- Domain-style sampling for Definition 4.27.12:
- primary domain: right calculus of fractions and the morphism in the localization represented by
  a roof;
- inspected owner declarations:
  `MorphismProperty.RightFraction`,
  `RightFraction.map`,
  `RightFraction.map_eq_iff`,
  `Localization.exists_rightFraction`;
- best owner abstraction: the represented morphism already lives at the canonical owner
  `RightFraction.map`.

Primitive-vs-derived split:
- primitive data: a right fraction `φ : S.RightFraction X Y`;
- derived API: the induced localization morphism `φ.map S.Q (Localization.inverts _ _)`, with
  equality controlled by `RightFraction.map_eq_iff`.

Source/core/bridge triage:
- `source-facing`: the roof `φ : S.RightFraction X Y`;
- `core/canonical`: `RightFraction.map`;
- `bridge/view`: the textbook description of the represented morphism as the composite `f s⁻¹`.

Definition 4.27.12 is therefore a `core/canonical` recall item, so this file reuses
`RightFraction.map` directly and keeps no parallel local wrapper theorem.
-/
/- Definition 4.27.12: for a morphism `f : X' ⟶ Y` and a denominator `s : X' ⟶ X` in `S`, the
roof `(f, s)` represents the canonical localization morphism from `X` to `Y`. Specialized to the
localization functor `S.Q`, this is exactly the morphism of `S⁻¹ C` denoted in the text by
`f s⁻¹`. -/
recall RightFraction.map

end MorphismProperty
end CategoryTheory
