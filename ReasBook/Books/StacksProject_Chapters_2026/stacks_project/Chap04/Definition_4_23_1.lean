module

public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Source/core/bridge triage for Definition 4.23.1:
- primary domain: exactness predicates on functors, owned by
  `Mathlib/CategoryTheory/Limits/ExactFunctor`.
- inspected owner declarations: `leftExactFunctor`, `leftExactFunctor_iff`,
  `rightExactFunctor`, and `exactFunctor_iff`.
- best owner abstraction: the `ObjectProperty (C ⥤ D)` predicates
  `leftExactFunctor C D`, `rightExactFunctor C D`, and `exactFunctor C D`.
- layer: `core/canonical`; this numbered item is a direct recall of the owner predicates.
- primitive data: only the ambient categories `C` and `D`.
- derived API: bundled functor categories and `_iff` companion lemmas stay upstream; this file
  recalls only the canonical predicates used downstream.
-/

/- Definition 4.23.1 (1): the left-exact functors `C ⥤ D` form the canonical object property
`leftExactFunctor C D`, whose value on `F : C ⥤ D` is definitionally `PreservesFiniteLimits F`. -/
recall leftExactFunctor

/- Definition 4.23.1 (2): the right-exact functors `C ⥤ D` form the canonical object property
`rightExactFunctor C D`, whose value on `F : C ⥤ D` is definitionally
`PreservesFiniteColimits F`. -/
recall rightExactFunctor

/- Definition 4.23.1 (3): the exact functors `C ⥤ D` form the canonical object property
`exactFunctor C D`, whose value on `F : C ⥤ D` says that `F` is both left exact and right exact. -/
recall exactFunctor

/- Companion recall: exactness is definitionally preservation of finite limits together with
preservation of finite colimits. -/
recall exactFunctor_iff

end CategoryTheory
