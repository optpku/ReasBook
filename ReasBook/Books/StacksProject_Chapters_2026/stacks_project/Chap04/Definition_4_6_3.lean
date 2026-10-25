module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable (C : Type u) [Category.{v} C]

/- Domain-style sampling for Definition 4.6.3:
- primary domain: categorical pullbacks and existence-of-limits-of-cospans.
- inspected canonical declarations: `HasPullbacks`, `HasPullback`, `HasPullbacksAlong`,
  `pullback.fst`.
- core/canonical owner: `CategoryTheory.Limits.HasPullbacks`.
- primitive data: none beyond the owner predicate itself; this is already the canonical global
  existence predicate.
- derived API: the pointwise specializations `HasPullback f g`, the chosen object `pullback f g`,
  and its universal-property API such as `pullback.fst`, `pullback.snd`, and `pullback.lift`.

Source/core/bridge triage:
- `source-facing`: the Stacks notion that a category has fibre products.
- `core/canonical`: `CategoryTheory.Limits.HasPullbacks`.
- `bridge/view`: the per-morphism existence predicate `HasPullback`, and later chapter uses such as
  `HasPullbacksAlong`, which specialize the global owner to a fixed morphism. -/

/- Definition 4.6.3: a category has fibre products exactly when it has the canonical mathlib
typeclass `HasPullbacks`, meaning that for every pair of morphisms `f : x ⟶ y` and
`g : z ⟶ y` a pullback of `f` and `g` exists. -/
recall HasPullbacks

end CategoryTheory.Limits
