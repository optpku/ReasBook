module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]
variable {X Y P : C} {ι₁ : X ⟶ P} {ι₂ : Y ⟶ P}

/- Domain-style sampling for Definition 4.5.1:
- primary domain: binary coproducts in category theory.
- relevant owner abstractions already upstream:
  `BinaryCofan.mk`, `BinaryCofan.isColimitMk`, `HasBinaryCoproduct`, `coprod.inl`,
  `coprod.desc`, and `coprodIsCoprod`.

Primitive-vs-derived split:
- primitive data in the source-facing statement: the vertex object `P` and the coprojections
  `ι₁`, `ι₂`.
- derived API: the mediating morphisms and uniqueness clause are canonically packaged by
  `IsColimit`; the chosen-object interface `X ⨿ Y`, `coprod.inl`, `coprod.desc` belongs to the
  downstream existence layer `[HasBinaryCoproduct X Y]`. -/

/- Source/core/bridge triage for Definition 4.5.1:
- `source-facing`: the textbook assertion that `ι₁`, `ι₂` exhibit `P` as a coproduct of `X`,
  `Y`.
- `core/canonical`: `IsColimit (BinaryCofan.mk ι₁ ι₂)`.
- `bridge/view`: the chosen binary coproduct object API, accessed later through
  `HasBinaryCoproduct` and `coprodIsCoprod`. -/

/- Definition 4.5.1: morphisms `ι₁ : X ⟶ P` and `ι₂ : Y ⟶ P` exhibit `P` as a coproduct of `X`
and `Y` precisely when the binary cofan `BinaryCofan.mk ι₁ ι₂` is colimiting. -/
#check IsColimit (BinaryCofan.mk ι₁ ι₂)

/- Companion recall: the unique-factorization clause in the textbook definition is the canonical
theorem `IsColimit.existsUnique`. -/
recall IsColimit.existsUnique

/- Companion recall: for a binary cofan of the form `BinaryCofan.mk ι₁ ι₂`, the converse
direction is the binary-coproduct-specific constructor `BinaryCofan.isColimitMk`. -/
recall BinaryCofan.isColimitMk

end CategoryTheory.Limits
