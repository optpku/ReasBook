module

public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.CategoryTheory.ConcreteCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Lie.Basic


@[expose] public section

open CategoryTheory

noncomputable section

universe v u

variable (R : Type u) [CommRing R]

/-- The bundled category of Lie algebras over a fixed commutative ring. -/
structure LieAlgebraCat where
  /-- The underlying carrier type. -/
  carrier : Type v
  /-- The Lie-ring structure on the carrier. -/
  [instLieRing : LieRing carrier]
  /-- The Lie-algebra structure over the base ring. -/
  [instLieAlgebra : LieAlgebra R carrier]

attribute [instance] LieAlgebraCat.instLieRing LieAlgebraCat.instLieAlgebra

namespace LieAlgebraCat

instance : CoeSort (LieAlgebraCat R) (Type v) :=
  ⟨LieAlgebraCat.carrier⟩

/-- The object in the category of Lie algebras associated to a type equipped with the appropriate
typeclasses. -/
abbrev of (L : Type v) [LieRing L] [LieAlgebra R L] : LieAlgebraCat R :=
  ⟨L⟩

instance : Category (LieAlgebraCat R) where
  Hom L M := L →ₗ⁅R⁆ M
  id L := LieHom.id
  comp f g := LieHom.comp g f

instance : ConcreteCategory (LieAlgebraCat R) (· →ₗ⁅R⁆ ·) where
  hom := fun f ↦ f
  ofHom := fun f ↦ f
  hom_ofHom := fun _ ↦ rfl
  ofHom_hom := fun _ ↦ rfl
  id_apply := fun _ ↦ rfl
  comp_apply := fun _ _ _ ↦ rfl

/-- Typecheck a Lie algebra morphism as a categorical morphism. -/
abbrev ofHom {L M : Type v} [LieRing L] [LieAlgebra R L] [LieRing M] [LieAlgebra R M]
    (f : L →ₗ⁅R⁆ M) : of R L ⟶ of R M :=
  f

@[ext]
lemma hom_ext {L M : LieAlgebraCat R} {f g : L ⟶ M} (h : ∀ x, f x = g x) : f = g :=
  LieHom.ext fun x ↦ h x

/-- The underlying `R`-module of a bundled Lie algebra. -/
abbrev toModuleCat (L : LieAlgebraCat R) : ModuleCat R :=
  ModuleCat.of R L

instance : HasForget₂ (LieAlgebraCat R) (ModuleCat R) where
  forget₂ :=
    { obj := toModuleCat (R := R)
      map := fun f ↦ ModuleCat.ofHom f.toLinearMap }
  forget_comp := rfl

@[simp]
lemma forget₂_module_map {L M : LieAlgebraCat R} (f : L ⟶ M) :
    (forget₂ (LieAlgebraCat R) (ModuleCat R)).map f = ModuleCat.ofHom f.toLinearMap :=
  rfl

end LieAlgebraCat
