module

public import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {M : J ⥤ C} {c : Cocone M}

/- Domain-style sampling for Definition 4.14.2:
- primary domain: colimits of a diagram in category theory.
- inspected owner declarations:
  `IsColimit`,
  `Cocone`,
  `HasColimit`,
  `colimit.cocone`,
  `colimit.isColimit`,
  `IsColimit.existsUnique`,
  `IsColimit.ofExistsUnique`.
- best owner abstraction: the textbook notion that a cocone on `M` is colimiting is already the
  canonical owner witness `IsColimit`.
- primitive data: a cocone `Cocone M`.
- derived API: the existence typeclass `HasColimit M`, the chosen colimit object `colimit M`, the
  coprojections `colimit.ι`, the chosen cocone `colimit.cocone M`, the proof that it is
  colimiting `colimit.isColimit M`, and the universal-property constructor/recognition theorems
  `IsColimit.existsUnique` and `IsColimit.ofExistsUnique`.

Source/core/bridge triage:
- `source-facing`: the textbook notion that a cocone on `M` is a colimit cocone.
- `core/canonical`: the witness `IsColimit`.
- `bridge/view`: `HasColimit`, `colimit`, `colimit.ι`, `colimit.cocone`, `colimit.isColimit`,
  `IsColimit.existsUnique`, and `IsColimit.ofExistsUnique`. -/

/- Definition 4.14.2: for a diagram `M : J ⥤ C`, the textbook notion that a cocone `c : Cocone M`
is a colimit cocone is exactly the canonical owner witness `IsColimit c`. -/
#check IsColimit c

/- Companion recall: the textbook source data of an object equipped with morphisms from each
`M.obj i` is packaged by the cocone structure `Cocone M`. -/
#check Cocone M

/- Companion recall: existence of a chosen colimit for `M` is expressed by `HasColimit M`. -/
#check HasColimit M

section

variable [HasColimit M]

/- Companion recall: under `[HasColimit M]`, the textbook object `colim_I M` is the canonical
chosen colimit object `colimit M`, with coprojections `colimit.ι`. -/
#check (colimit M : C)
recall colimit.ι

/- Companion recall: the canonical chosen colimiting cocone is `colimit.cocone M`, and it is
colimiting by `colimit.isColimit M`. -/
#check (colimit.cocone M : Cocone M)
recall colimit.isColimit

end

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsColimit.existsUnique`. -/
recall IsColimit.existsUnique

/- Companion recall: the converse direction is the canonical constructor
`IsColimit.ofExistsUnique`. -/
recall IsColimit.ofExistsUnique

end CategoryTheory.Limits
