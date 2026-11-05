module

public import Mathlib.CategoryTheory.Localization.CalculusOfFractions.OfAdjunction
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory
namespace MorphismProperty

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling:
- primary domain: calculus of fractions for morphism properties
- core/canonical owners already present in mathlib:
  `MorphismProperty.HasLeftCalculusOfFractions`,
  `MorphismProperty.HasRightCalculusOfFractions`,
  `MorphismProperty.IsMultiplicative`,
  `MorphismProperty.Q`
- best owner abstraction: the source notion “multiplicative system” is not a third owner; it is
  the direct conjunction of the two canonical calculus-of-fractions owners
- primitive data: exactly the left and right calculus-of-fractions owner instances
- derived API: the direct source-facing conjunction statement

Source/core/bridge triage:
- `source-facing`: the Stacks phrase “multiplicative system”
- `core/canonical`: `W.HasLeftCalculusOfFractions` and `W.HasRightCalculusOfFractions`
- `bridge/view`: the direct conjunction `W.HasLeftCalculusOfFractions ∧
  W.HasRightCalculusOfFractions`
-/

/- Companion recall: a left multiplicative system on a category is the canonical mathlib notion
`MorphismProperty.HasLeftCalculusOfFractions`, encoding closure under identities and composition,
left Ore completion, and left cancellation. -/
recall HasLeftCalculusOfFractions

/- Companion recall: a right multiplicative system on a category is the canonical mathlib notion
`MorphismProperty.HasRightCalculusOfFractions`, encoding closure under identities and composition,
right Ore completion, and right cancellation. -/
recall HasRightCalculusOfFractions

variable (W : MorphismProperty C)

/- Definition 4.27.1: a set of arrows in a category is a multiplicative system if it is both a
left multiplicative system and a right multiplicative system, i.e. if the corresponding morphism
property has both the left and right calculus of fractions. -/
#check W.HasLeftCalculusOfFractions ∧ W.HasRightCalculusOfFractions

/-- The class of isomorphisms in any category has both left and right calculus of fractions. -/
instance : (isomorphisms C).HasLeftCalculusOfFractions := by
  simpa using Adjunction.hasLeftCalculusOfFractions' (Adjunction.id : 𝟭 C ⊣ 𝟭 C)

instance : (isomorphisms C).HasRightCalculusOfFractions := by
  simpa using Adjunction.hasRightCalculusOfFractions' (Adjunction.id : 𝟭 C ⊣ 𝟭 C)

end MorphismProperty
end CategoryTheory
