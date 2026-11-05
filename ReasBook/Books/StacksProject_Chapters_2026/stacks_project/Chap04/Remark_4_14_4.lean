module

public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Limits

variable {I : Type u₁} [Category.{v₁} I]
variable {C : Type u₂} [Category.{v₂} C]

/- Domain-style sampling for Remark 4.14.4:
- `limit.homIso'` and `colimit.homIso'` are the canonical owner equivalences for the Hom-formulas
  of limits and colimits.
- `limit.existsUnique` and `colimit.existsUnique` are the canonical unique-factorization theorems
  for compatible component families.
- `Yoneda.ext` and `Coyoneda.ext` are the extensionality owners expressing that the Hom-formulas
  determine the limit or colimit object up to unique isomorphism.

Primitive-vs-derived split:
- primitive data: a diagram `M` together with a compatible family of component morphisms into or
  out of `M.obj i`.
- derived API: the induced morphism, its uniqueness, and the resulting objectwise uniqueness up to
  isomorphism.

Source/core/bridge triage for Remark 4.14.4:
- `source-facing`: the textbook Hom-formulas for limits and colimits, together with the remark
  that they determine the universal object uniquely.
- `core/canonical`: `limit.homIso'` and `colimit.homIso'`.
- `bridge/view`: `limit.existsUnique`, `colimit.existsUnique`, `Yoneda.ext`, and
  `Coyoneda.ext`. -/

/- Remark 4.14.4(1): the limit side of the Hom-formula is the canonical componentwise
universal-property equivalence `limit.homIso'`, identifying maps `W ⟶ limit M` with compatible
families `p_i : W ⟶ M.obj i`.
-/
recall limit.homIso'

/- Companion recall: the source unique-factorization formulation for a compatible family
`p_i : W ⟶ M.obj i` is the canonical theorem `limit.existsUnique`, after packaging that family as a
cone on `M` with cone point `W`. -/
recall limit.existsUnique

/- Remark 4.14.4(2): the colimit side of the Hom-formula is the canonical componentwise
universal-property equivalence `colimit.homIso'`, identifying maps `colimit M ⟶ W` with
compatible families `p_i : M.obj i ⟶ W`.
-/
recall colimit.homIso'

/- Companion recall: the source unique-factorization formulation for a compatible family
`p_i : M.obj i ⟶ W` is the canonical theorem `colimit.existsUnique`, after packaging that family
as a cocone on `M` with cocone point `W`. -/
recall colimit.existsUnique

/- Companion recall: the Hom-formula for limits determines the limit object up to unique
isomorphism by the Yoneda lemma, via `Yoneda.ext`. -/
recall Yoneda.ext

/- Companion recall: the Hom-formula for colimits determines the colimit object up to unique
isomorphism by the dual Yoneda lemma, via `Coyoneda.ext`. -/
recall Coyoneda.ext

end CategoryTheory.Limits
