module

public import Mathlib.CategoryTheory.Limits.ConeCategory
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ u₁ v₂ u₂

namespace CategoryTheory.Limits

variable {J : Type u₁} [Category.{v₁} J]
variable {C : Type u₂} [Category.{v₂} C]
variable {F : J ⥤ C}

/- Domain-style sampling for Remark 4.14.5:
- primary domain: cone and cocone categories as the owner categories for limit and colimit
  universal properties.
- sampled canonical declarations:
  `Cone`,
  `Cone.isLimitEquivIsTerminal`,
  `hasLimit_iff_hasTerminal_cone`,
  `Cocone.isColimitEquivIsInitial`,
  `hasColimit_iff_hasInitial_cocone`.
- best owner abstraction: the cone category `Cone F` and the cocone category `Cocone F`.
- primitive data: the cone and cocone structures, together with their canonical category
  instances.
- derived API: the equivalences from `IsLimit` to `IsTerminal` and from `IsColimit` to
  `IsInitial`, plus the corresponding existence-level reformulations.

Source/core/bridge triage:
- `source-facing`: the textbook remark that a limit cone is exactly a terminal object in the
  category of cones, and dually that a colimit cocone is exactly an initial object in the category
  of cocones.
- `core/canonical`: the owner categories `Cone F` and `Cocone F`.
- `bridge/view`: `Cone.isLimitEquivIsTerminal`, `hasLimit_iff_hasTerminal_cone`,
  `Cocone.isColimitEquivIsInitial`, and `hasColimit_iff_hasInitial_cocone`. -/

/- Companion recall: a cone on a diagram `F : J ⥤ C` is the canonical mathlib structure `Cone F`,
consisting of an object together with a compatible family of maps to the objects of the diagram. -/
recall Cone

/- Companion recall: cones on a fixed diagram form a category via the canonical instance
`Cone.category`. -/
recall Cone.category

/- Remark 4.14.5, canonical limit-side formulation: for a fixed cone `c : Cone F`, the data of
`IsLimit c` is canonically equivalent to `IsTerminal c` in the category of cones on `F`. -/
recall Cone.isLimitEquivIsTerminal

/- Companion recall: the existence-level limit reformulation is the canonical theorem
`hasLimit_iff_hasTerminal_cone`. -/
recall hasLimit_iff_hasTerminal_cone

/- Companion recall: a cocone on a diagram `F : J ⥤ C` is the canonical mathlib structure
`Cocone F`, consisting of an object together with a compatible family of maps from the objects of
the diagram. -/
recall Cocone

/- Companion recall: cocones on a fixed diagram form a category via the canonical instance
`Cocone.category`. -/
recall Cocone.category

/- Remark 4.14.5, canonical colimit-side formulation: for a fixed cocone `c : Cocone F`, the data
of `IsColimit c` is canonically equivalent to `IsInitial c` in the category of cocones on `F`. -/
recall Cocone.isColimitEquivIsInitial

/- Companion recall: the existence-level colimit reformulation is the canonical theorem
`hasColimit_iff_hasInitial_cocone`. -/
recall hasColimit_iff_hasInitial_cocone

end CategoryTheory.Limits
