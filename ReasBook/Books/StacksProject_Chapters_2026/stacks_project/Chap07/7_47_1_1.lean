module

public import Mathlib.CategoryTheory.Sites.Sieves
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {U : C}

/- Domain-style sampling for 7.47.1.1:
- primary domain: sieves on a fixed object in a category;
- sampled owner abstractions:
  `CategoryTheory.Sieve`,
  `CategoryTheory.Sieve.downward_closed`,
  `CategoryTheory.Sieve.ofArrows`,
  `CategoryTheory.Sieve.instCompleteLattice`;
- layer triage:
  `source-facing`: the closure property for membership in a sieve under precomposition;
  `core/canonical`: the mathlib owner `Sieve U`, whose primitive data are the underlying presieve
    together with the closure field `downward_closed`;
  `bridge/view`: generated-sieve presentations such as `Sieve.ofArrows`, which belong to the
    neighboring files rather than to this recall item.

Primitive data are just the sieve itself. The closure-under-precomposition statement is not a
separate chapter-level construction; it is exactly the primitive owner field
`Sieve.downward_closed`, so no local wrapper or restatement should be kept here.
-/

/- 7.47.1.1: a sieve on `U` is stable under precomposition (equivalently, closed under
left-composition). If `α : T ⟶ U` belongs to the sieve and `g : T' ⟶ T`, then
`g ≫ α : T' ⟶ U` also belongs to the sieve. -/
recall Sieve.downward_closed

end CategoryTheory
