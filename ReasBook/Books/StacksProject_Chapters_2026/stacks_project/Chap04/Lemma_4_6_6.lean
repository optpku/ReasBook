module

public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Source/core/bridge triage for Lemma 4.6.6:
- `source-facing`: representable morphisms are stable under arbitrary base change squares.
- `core/canonical`: the direct base-change theorem
  `((𝟭 C).relativelyRepresentable).of_isPullback`.
- `bridge/view`: the generic owner instance
  `Functor.relativelyRepresentable.isStableUnderBaseChange`, specialized to the identity functor.
- inspected domain declarations:
  `(𝟭 C).relativelyRepresentable`,
  `((𝟭 C).relativelyRepresentable).of_isPullback`,
  `Functor.relativelyRepresentable`,
  `Functor.relativelyRepresentable.isStableUnderBaseChange`,
  `Limits.IsPullback`.
- primitive data: a cartesian square and a representability witness on one side of it.
- derived API: representability of the base-changed morphism, supplied directly by the owner
  theorem `((𝟭 C).relativelyRepresentable).of_isPullback`.
-/

/- Lemma 4.6.6: stability under base change for ordinary representable morphisms in `C` is already
the direct theorem on the canonical owner `(𝟭 C).relativelyRepresentable`. -/
#check ((𝟭 C).relativelyRepresentable).of_isPullback

end CategoryTheory
