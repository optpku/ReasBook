module

public import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {X : C}

/- Domain-style sampling for Definition 4.26.1:
- `CategoryTheory.IsFinitelyPresentable` is the owner predicate for finitely presentable
  ("categorically compact") objects.
- `CategoryTheory.ObjectProperty.isFinitelyPresentable` is the corresponding object-property owner
  used by the chapter's filtered-generator API.
- `CategoryTheory.isFinitelyPresentable_iff_preservesFilteredColimits` is the source-facing bridge
  to the textbook `Hom(X, -)`/filtered-colimit condition.
- `CategoryTheory.IsFinitelyPresentable.exists_hom_of_isColimit` is a typical derived API showing
  that stagewise factorization is derived from the owner abstraction, not primitive data.

Primitive-vs-derived split:
- primitive data: none; the notion is already owned upstream as a `Prop`.
- derived API: preservation of filtered colimits by `coyoneda.obj (op X)` and filtered-colimit
  factorization lemmas. -/

/- Source/core/bridge triage for Definition 4.26.1:
- `source-facing`: the Stacks notion that `X` is categorically compact.
- `core/canonical`: `CategoryTheory.IsFinitelyPresentable X`.
- `bridge/view`: the preservation-of-filtered-colimits characterization for `coyoneda.obj (op X)`.
-/

/- Definition 4.26.1: categorical compactness is the canonical owner predicate
`IsFinitelyPresentable`. -/
recall IsFinitelyPresentable

/- Companion recall: the textbook formulation via preservation of filtered colimits by `Hom(X, -)`
is the canonical theorem `isFinitelyPresentable_iff_preservesFilteredColimits`. -/
recall isFinitelyPresentable_iff_preservesFilteredColimits

end CategoryTheory
