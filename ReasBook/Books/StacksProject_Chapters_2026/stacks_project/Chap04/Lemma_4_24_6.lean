module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]
variable {u : C ⥤ D} {v : D ⥤ C}

/- Domain-style sampling for Lemma 4.24.6:
- primary domain: adjunctions and exactness properties of functors;
- inspected owner declarations:
  `Adjunction.leftAdjoint_preservesColimits`,
  `Adjunction.rightAdjoint_preservesLimits`,
  `PreservesColimits.preservesFiniteColimits`,
  `PreservesLimits.preservesFiniteLimits`;
- best owner abstraction: the adjunction owner theorems, with the chapter's exactness predicates
  as the canonical finite-(co)limit view;
- primitive data: a chosen adjunction `u ⊣ v`;
- derived API: the right-exactness of `u` and the left-exactness of `v`, obtained from the owner
  theorems through the canonical finite-(co)limit upgrade lemmas and the exactness predicates. -/

/- Source/core/bridge triage for Lemma 4.24.6:
- source-facing: the Stacks lemma is stated for a chosen adjunction `u ⊣ v`.
- core/canonical: mathlib owns the preservation statements through
  `Adjunction.leftAdjoint_preservesColimits` and `Adjunction.rightAdjoint_preservesLimits`.
- bridge/view: the explicit-adjunction statements below are thin companions from a chosen
  adjunction to the chapter's finite-exactness predicates. -/

/-- Lemma 4.24.6 (1): if `u` is left adjoint to `v`, then `u` is right exact. This is the
source-facing bridge from a chosen adjunction to the owner theorem
`Adjunction.leftAdjoint_preservesColimits`. -/
theorem left_adjoint_is_rightExact_of_adjunction (adj : u ⊣ v) :
    rightExactFunctor C D u := by
  -- First upgrade the chosen adjunction to preservation of all colimits.
  letI : PreservesColimits u := adj.leftAdjoint_preservesColimits
  -- Then restrict from all colimits to finite colimits, which is right exactness.
  exact PreservesColimits.preservesFiniteColimits u

/-- Lemma 4.24.6 (2): if `u` is left adjoint to `v`, then `v` is left exact. This is the
source-facing bridge from a chosen adjunction to the owner theorem
`Adjunction.rightAdjoint_preservesLimits`. -/
theorem right_adjoint_is_leftExact_of_adjunction (adj : u ⊣ v) :
    leftExactFunctor D C v := by
  -- First upgrade the chosen adjunction to preservation of all limits.
  letI : PreservesLimits v := adj.rightAdjoint_preservesLimits
  -- Then restrict from all limits to finite limits, which is left exactness.
  exact PreservesLimits.preservesFiniteLimits v

end CategoryTheory
