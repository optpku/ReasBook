module

public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {D : Type u₂} [Category.{v₂} D]

/- Domain-style sampling for Definition 4.24.1:
- `Adjunction` is the owner object for the notion that `u : C ⥤ D` is left adjoint to
  `v : D ⥤ C`.
- `Adjunction.CoreHomEquiv` is the canonical bridge packaging the textbook's natural family of
  hom-set bijections.
- `Adjunction.mkOfHomEquiv` is the canonical constructor from the textbook hom-set bijections.
- `Adjunction.homEquiv` is the derived hom-set equivalence attached to an adjunction.
- `Adjunction.homEquiv_naturality_left` and `Adjunction.homEquiv_naturality_right` are the
  canonical naturality laws for that derived equivalence.

Primitive-vs-derived split:
- primitive data: the adjunction owner `u ⊣ v`.
- derived API: the source-style family of hom-set bijections and its naturality in both
  variables. -/

/- Source/core/bridge triage for Definition 4.24.1:
- `source-facing`: the textbook statement that `u` is left adjoint to `v`, equivalently that
  there is a natural family of bijections
  `(u.obj X ⟶ Y) ≃ (X ⟶ v.obj Y)`.
- `core/canonical`: `Adjunction u v`, written `u ⊣ v`.
- `bridge/view`: `Adjunction.CoreHomEquiv`, `Adjunction.mkOfHomEquiv`, `Adjunction.homEquiv`, and
  the two naturality lemmas expressing the textbook hom-set formulation from the owner
  abstraction.
-/

/- Definition 4.24.1: for functors `u : C ⥤ D` and `v : D ⥤ C`, saying that `u` is a left
adjoint of `v`, or equivalently that `v` is a right adjoint to `u`, is the canonical owner notion
`Adjunction u v`, written `u ⊣ v`. The source-style hom-set bijections are derived from this owner
via `Adjunction.homEquiv`, and conversely a natural family of such bijections gives an adjunction
via `Adjunction.mkOfHomEquiv`. -/
recall Adjunction

/- The textbook's natural family of hom-set bijections is packaged by the canonical bridge object
`Adjunction.CoreHomEquiv`; it is auxiliary data for constructing the owner object `u ⊣ v`, not a
second owner notion. -/
recall Adjunction.CoreHomEquiv

/- The textbook's natural family of hom-set bijections canonically determines an adjunction via
`Adjunction.mkOfHomEquiv`. -/
recall Adjunction.mkOfHomEquiv

/- The textbook's bijections of morphism sets are the canonical equivalences attached to an
adjunction. -/
recall Adjunction.homEquiv

/- The hom-set bijections of an adjunction are natural in the source object. -/
recall Adjunction.homEquiv_naturality_left

/- The hom-set bijections of an adjunction are natural in the target object. -/
recall Adjunction.homEquiv_naturality_right

end CategoryTheory
