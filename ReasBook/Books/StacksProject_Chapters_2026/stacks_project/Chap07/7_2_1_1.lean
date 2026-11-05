module

public import Mathlib.CategoryTheory.Yoneda
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-
Domain-style sampling for 7.2.1.1:
- primary domain: representable presheaves and the Yoneda lemma for set-valued presheaves
- sampled canonical declarations:
  `Presheaf`,
  `yoneda.obj`,
  `yonedaEquiv`,
  `yonedaEquiv_apply`
- best owner abstraction: the canonical Hom-to-sections equivalence `yonedaEquiv`
- primitive data: the presheaf `F : Cᵒᵖ ⥤ Type v` and the object `U : C`
- derived API: evaluation `yonedaEquiv_apply` and naturality `yonedaEquiv_naturality`
-/
/-
Source/core/bridge triage for 7.2.1.1:
- source-facing statement: the pointwise form of the Yoneda lemma for a set-valued presheaf
- core/canonical owner: `yonedaEquiv`
- derived API: `yonedaEquiv_naturality` and `yonedaEquiv_apply`

Primitive data are the presheaf `F` and the object `U`. The bijection itself is derived API from
the canonical owner `yonedaEquiv`, so this file should recall that owner directly rather than
introducing a local wrapper around morphisms out of `yoneda.obj U`.
-/
/- 7.2.1.1: for a presheaf `F : Cᵒᵖ ⥤ Type v` and an object `U : C`, morphisms
`yoneda.obj U ⟶ F` from the representable presheaf `h_U` to `F` are naturally in bijection with
the sections `F.obj (op U)`. This is the canonical pointwise Yoneda equivalence `yonedaEquiv`. -/
recall yonedaEquiv

end CategoryTheory
