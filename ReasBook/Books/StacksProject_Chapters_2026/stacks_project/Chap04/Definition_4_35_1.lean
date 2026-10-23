module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import Mathlib.CategoryTheory.Groupoid
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor Functor.Fiber IsHomLift IsStronglyCartesian

variable {𝒞 : Type u₁} {𝒮 : Type u₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒮]

/-
Domain-style sampling for Definition 4.35.1:
- primary domain: fibred categories and strongly cartesian morphisms.
- inspected owner-level declarations:
  `Functor.IsFibered`,
  `Functor.IsStronglyCartesian`,
  `Functor.Fiber`,
  `FibredCategoryOver`.
- best owner abstraction: the ambient chapter owner for categories over a fixed base is
  `FibredCategoryOver`, but there is no earlier owner for the source-facing extra condition
  "fibred in groupoids"; this file should therefore define only the minimal Prop-valued class on
  top of the canonical mathlib fibred-category owners.
- primitive data: fibredness of `p` together with the source-facing condition that every morphism
  of the total category is strongly cartesian over its image.
- derived API: every morphism in a standard fiber is an isomorphism, hence each standard fiber
  `p.Fiber U` is a groupoid.

Source/core/bridge triage:
- `source-facing`: `IsFibredInGroupoids p`.
- `core/canonical`: `Functor.IsFibered`, `Functor.IsStronglyCartesian`, `Functor.Fiber`.
- `bridge/view`: the instance deriving `IsGroupoid (p.Fiber U)` from the source-facing class. -/

/-- Definition 4.35.1: a functor `p : 𝒮 ⥤ 𝒞` is fibred in groupoids over `𝒞` if it is fibred
and every morphism of `𝒮` is strongly cartesian over its image in `𝒞`. In a fibered category,
cartesian and strongly cartesian arrows coincide, so this is the canonical mathlib-facing form of
the textbook condition. -/
class IsFibredInGroupoids (p : 𝒮 ⥤ 𝒞) : Prop extends p.IsFibered where
  /-- Every morphism in the total category is strongly cartesian over its image in the base. -/
  isStronglyCartesian_map {x y : 𝒮} (φ : x ⟶ y) : p.IsStronglyCartesian (p.map φ) φ

attribute [instance] IsFibredInGroupoids.isStronglyCartesian_map

/-- The primitive owner data for a functor fibred in groupoids reconstructs the source-facing
class. -/
instance (p : 𝒮 ⥤ 𝒞) [p.IsFibered]
    [∀ (x y : 𝒮) (φ : x ⟶ y), p.IsStronglyCartesian (p.map φ) φ] :
    IsFibredInGroupoids p where
  toIsFibered := inferInstance
  isStronglyCartesian_map _ := inferInstance

namespace IsFibredInGroupoids

variable {p : 𝒮 ⥤ 𝒞} [IsFibredInGroupoids p]
variable (U : 𝒞)

-- Proof sketch: the owner field `IsFibredInGroupoids.isStronglyCartesian_map` already makes the
-- underlying morphism strongly cartesian over `p.map φ.1`. Since `φ` lies in the fiber over `U`,
-- the defining hom-lift equation gives `p.map φ.1 = 𝟙 U`, so the base morphism is an
-- isomorphism. Then
-- `isIso_of_base_isIso` upgrades the underlying morphism, and the resulting inverse in `𝒮`
-- induces the inverse in the fiber.
private theorem fiber_hom_isIso {X Y : p.Fiber U} (φ : X ⟶ Y) : IsIso φ := by
  letI : p.IsHomLift (𝟙 U) φ.1 := φ.2
  haveI : IsIso (p.map φ.1) := by
    simpa [fac' p (𝟙 U) φ.1] using
      (show IsIso (eqToHom X.2 ≫ 𝟙 U ≫ eqToHom Y.2.symm) from inferInstance)
  letI : IsIso φ.1 := IsStronglyCartesian.isIso_of_base_isIso p (p.map φ.1) φ.1
  let e := asIso φ.1
  letI : p.IsHomLift (𝟙 U) e.inv := by
    simpa [e] using (inferInstance : p.IsHomLift (𝟙 U) (inv φ.1))
  refine ⟨⟨⟨e.inv, inferInstance⟩, ?_, ?_⟩⟩
  · apply hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · apply hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

/-- Every fiber of a category fibred in groupoids is a groupoid. -/
instance fiber_isGroupoid : IsGroupoid (p.Fiber U) where
  all_isIso := fiber_hom_isIso U

/-- A morphism in a fiber of a category fibred in groupoids is an isomorphism. -/
theorem hom_isIso {X Y : p.Fiber U} (φ : X ⟶ Y) : IsIso φ := by
  infer_instance

end IsFibredInGroupoids

end CategoryTheory
