module

public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C D : Type u} [Category.{v} C] [Category.{v} D]

/- Domain-style sampling for Theorem 4.25.3:
- primary domain: the general adjoint functor theorem in category theory.
- inspected owner-level declarations:
  `SolutionSetCondition`,
  `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`,
  `solutionSetCondition_of_isRightAdjoint`.
- best owner abstraction: `G.IsRightAdjoint` as the canonical adjointness predicate for a functor,
  with `isRightAdjoint_of_preservesLimits_of_solutionSetCondition` as the canonical constructor
  from the theorem hypotheses.

Primitive-vs-derived split:
- primitive data: none in this recall-only theorem file.
- derived API: the solution-set hypothesis is already owned by `SolutionSetCondition`, and the
  theorem conclusion is already packaged by the canonical `IsRightAdjoint` owner.

Source/core/bridge triage:
- `source-facing`: the textbook statement of the adjoint functor theorem.
- `core/canonical`: `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`.
- `bridge/view`: the converse theorem `solutionSetCondition_of_isRightAdjoint`, which is related
  but not part of this numbered item. -/

/- Canonical recall: the small-family hypothesis in the general adjoint functor theorem is the
mathlib predicate `SolutionSetCondition G`. -/
recall SolutionSetCondition

/- Theorem 4.25.3 (Adjoint functor theorem): if `G : D ⥤ C` preserves limits, `D` has limits, and
`G` satisfies the solution set condition, then `G` is a right adjoint. This is exactly the
canonical mathlib theorem `isRightAdjoint_of_preservesLimits_of_solutionSetCondition`. -/
recall isRightAdjoint_of_preservesLimits_of_solutionSetCondition

end CategoryTheory
