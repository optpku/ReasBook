module

public import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w₁ v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace SemiRepresentableFamily

/-- Definition 7.8.1's owner object: a family of arrows with fixed target `U` is an indexed
family of objects in the slice category `C / U`. -/
structure Over (U : C) where
  index : Type w₁
  obj : index → CategoryTheory.Over U

namespace Over

/-- A morphism of fixed-target families is a reindexing together with componentwise maps in the
slice category. -/
structure Hom {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over.{w₁} U) where
  α : 𝒰.index → 𝒱.index
  f : ∀ i : 𝒰.index, 𝒰.obj i ⟶ 𝒱.obj (α i)

instance instQuiver {U : C} : Quiver (SemiRepresentableFamily.Over.{w₁} U) where
  Hom 𝒰 𝒱 := Hom 𝒰 𝒱

/- Domain-style sampling for Definition 7.8.1:
- primary domain: families of arrows with fixed target, modeled by semi-representable families in
  slice categories and transported along `Over.map`;
- inspected owner declarations:
  `Definition_7_6_1`'s owner recall `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.ofArrows`,
  `SemiRepresentableFamily.Hom`,
  `SemiRepresentableFamily.map`,
  `Over.map`;
- best owner abstraction: the chapter owner `SemiRepresentableFamily.Over U`, together with its
  canonical indexed-arrow constructor `SemiRepresentableFamily.Over.ofArrows` and the induced
  functor `SemiRepresentableFamily.map (Over.map f)` on families when the target changes along
  `f`;
- primitive data: an indexed family of arrows into a fixed target, packaged as an object of
  `SemiRepresentableFamily.Over U`;
- derived API: same-target refinement as existence of a canonical owner morphism, and the
  cross-target change-of-target morphism type obtained directly from
  `SemiRepresentableFamily.map (Over.map f)`.

Source/core/bridge triage:
- `source-facing`: `Refines`;
- `core/canonical`: `SemiRepresentableFamily.Hom`, `SemiRepresentableFamily.Over`, and
  `SemiRepresentableFamily.map`;
- `bridge/view`: the upstream constructor `SemiRepresentableFamily.Over.ofArrows`, turning an
  indexed family of arrows into the owner object `SemiRepresentableFamily.Over U`.
-/

/-- Definition 7.8.1: a family `𝒰` refines `𝒱` when there is a morphism in the canonical category
`SemiRepresentableFamily.Over U` from `𝒰` to `𝒱`. -/
abbrev Refines {U : C} (𝒰 𝒱 : SemiRepresentableFamily.Over U) : Prop :=
  Nonempty (𝒰 ⟶ 𝒱)

-- Proof sketch: unfold `Refines`; this is the defining equivalence for the abbreviation.
/-- Refinement is exactly the existence of a morphism between the corresponding fixed-target
families. -/
theorem refines_iff_nonempty_hom {U : C} {𝒰 𝒱 : SemiRepresentableFamily.Over U} :
    Refines 𝒰 𝒱 ↔ Nonempty (𝒰 ⟶ 𝒱) := by
  -- Unfold the abbreviation so both sides become the same proposition.
  rfl

end Over
end SemiRepresentableFamily

end CategoryTheory
