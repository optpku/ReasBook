module

public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {M : J ⥤ C} {c : Cone M}

/- Domain-style sampling for Definition 4.14.1:
- primary domain: limits of a diagram in category theory.
- inspected owner declarations:
  `IsLimit`,
  `Cone`,
  `HasLimit`,
  `limit.cone`,
  `limit.isLimit`,
  `IsLimit.existsUnique`,
  `IsLimit.ofExistsUnique`.
- best owner abstraction: the textbook notion that a cone on `M` is limiting is already the
  canonical owner predicate `IsLimit`.
- primitive data: a cone `Cone M`.
- derived API: the existence typeclass `HasLimit M`, the chosen limit object `limit M`, the
  projections `limit.π`, the chosen cone `limit.cone M`, the proof that it is limiting
  `limit.isLimit M`, and the universal-property constructor/recognition theorems
  `IsLimit.existsUnique` and `IsLimit.ofExistsUnique`.

Source/core/bridge triage:
- `source-facing`: the textbook predicate that a cone on `M` is a limit cone.
- `core/canonical`: `IsLimit`.
- `bridge/view`: `HasLimit`, `limit`, `limit.π`, `limit.cone`, `limit.isLimit`,
  `IsLimit.existsUnique`, and `IsLimit.ofExistsUnique`. -/

/- Definition 4.14.1: for a diagram `M : J ⥤ C`, the textbook notion that a cone `c : Cone M` is
a limit cone is exactly the canonical owner predicate `IsLimit c`. -/
#check IsLimit c

/- Companion recall: the textbook source data of an object equipped with morphisms to `M.obj i` is
packaged by the canonical cone structure `Cone`. -/
recall Cone

/- Companion recall: existence of a chosen limit for a diagram is expressed by the canonical
typeclass `HasLimit`. -/
recall HasLimit

/- Companion recall: the textbook chosen limit object `lim_I M` is the canonical owner `limit`,
with projections `limit.π`. -/
section

variable [HasLimit M]
recall limit
recall limit.π

/- Companion recall: the canonical chosen limiting cone is `limit.cone M`, and it is limiting by
`limit.isLimit M`. -/
recall limit.cone
recall limit.isLimit

end

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsLimit.existsUnique`. -/
recall IsLimit.existsUnique

/- Companion recall: the converse direction from the textbook universal property to a limiting
cone is the canonical constructor `IsLimit.ofExistsUnique`. -/
recall IsLimit.ofExistsUnique

end CategoryTheory.Limits
