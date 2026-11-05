module

import Mathlib.Tactic.Recall
public import stacks_project.Chap04.«4_34_2_1»

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v uS uS'

namespace CategoryTheory

/- Domain-style sampling for `4.34.2.2`:
- primary domain: relative inertia categories and their canonical section back to the source
  category.
- inspected owner declarations:
  `RelativeInertiaObject`,
  `relativeInertiaStructureFunctor`,
  `BasedCategory.toBase`,
  `CategoryOver.relativeInertiaOver`,
  `CategoryOver.relativeInertiaStructureMap`.
- best owner abstraction: the generic owner declaration is
  `CategoryTheory.relativeInertiaIdentitySection`, defined with the rest of the generic relative
  inertia API in `Lemma_4_34_1`; the `CategoryOver` statements here are `bridge/view` packaging of
  that owner in `Cat/C`, with the chapter owner object `relativeInertiaOver F` already introduced
  in `4.34.2.1`; the absolute case is the direct specialization
  `CategoryOver.absoluteInertiaIdentitySection` along `S.toBase`.
- source/core/bridge triage:
  `core/canonical`: `CategoryTheory.relativeInertiaIdentitySection`;
  `bridge/view`: the `Cat/C` packagings `CategoryOver.relativeInertiaIdentitySection` and
  `CategoryOver.absoluteInertiaIdentitySection` of that owner functor.
- primitive data: the identity automorphism `Iso.refl X` on each source object.
- derived API: the right-inverse identity for the packaged section in `Cat/C`; the absolute case
  is the specialization along `S.toBase`. -/

namespace CategoryOver

open BasedFunctor FibredCategoryMor

variable {C : Type u} [Category.{v} C]
variable {X Y : FibredCategoryOver.{u, v, u, v} C}

/- Core/canonical recall: the underlying neutral section of a relative inertia category is the
generic owner functor `CategoryTheory.relativeInertiaIdentitySection`; this file packages it as the
canonical `Cat/C` bridge and records its right-inverse identity. -/
recall CategoryTheory.relativeInertiaIdentitySection

/-- 4.34.2.2 (1): the identity automorphisms define the neutral section
`e : \mathcal S \to \mathcal I_{\mathcal S/\mathcal S'}`, packaged as a morphism in `Cat/C`. -/
abbrev relativeInertiaIdentitySection (F : X ⟶ Y) :
    X.toCategoryOver ⥤ᵇ
      relativeInertiaOver (toBasedFunctor F) :=
  { toFunctor := CategoryTheory.relativeInertiaIdentitySection (toFunctor F)
    w := rfl }

-- Proof sketch: unfold the packaged based functor defining the neutral relative-inertia section.
/-- The relative neutral section has the expected underlying identity-automorphism functor. -/
theorem relativeInertiaIdentitySection_toFunctor
    (F : X ⟶ Y) :
    (relativeInertiaIdentitySection F).toFunctor =
      CategoryTheory.relativeInertiaIdentitySection (toFunctor F) := by
  -- Unfolding the packaged based functor exposes the owner-level neutral section directly.
  rfl

-- Proof sketch: reduce to the owner-level identity
-- `relativeInertiaIdentitySection_comp_structureFunctor` after unpacking the bundled morphism.
/-- The relative neutral section is a right inverse to the relative-inertia structure map. -/
@[simp] theorem relativeInertiaIdentitySection_comp_structureMap
    (F : X ⟶ Y) :
    relativeInertiaIdentitySection F ⋙ relativeInertiaStructureMap (toBasedFunctor F) =
      𝟭 X.toCategoryOver := by
  -- After unpacking both packaged morphisms, the composition is the owner-level right inverse.
  rfl

variable {S : CategoryOver C}

/-- 4.34.2.2 (2): the identity automorphisms define the neutral section
`e : \mathcal S \to \mathcal I_{\mathcal S}`, packaged as a morphism in `Cat/C`. -/
abbrev absoluteInertiaIdentitySection (S : CategoryOver C) :
    S ⥤ᵇ absoluteInertiaOver S :=
  { toFunctor := CategoryTheory.relativeInertiaIdentitySection S.toBase.toFunctor
    w := rfl }

-- Proof sketch: unfold the absolute specialization of the packaged relative neutral section.
/-- The absolute neutral section has the expected underlying identity-automorphism functor. -/
theorem absoluteInertiaIdentitySection_toFunctor
    (S : CategoryOver C) :
    (absoluteInertiaIdentitySection S).toFunctor =
      CategoryTheory.relativeInertiaIdentitySection S.toBase.toFunctor := by
  -- The absolute section is the specialization of the same packaged owner functor.
  rfl

-- Proof sketch: specialize the relative right-inverse statement to the structure morphism
-- `S.toBase`.
/-- The absolute neutral section is a right inverse to the absolute-inertia structure map. -/
@[simp] theorem absoluteInertiaIdentitySection_comp_structureMap
    (S : CategoryOver C) :
    absoluteInertiaIdentitySection S ⋙ relativeInertiaStructureMap S.toBase = 𝟭 S := by
  -- Specializing the relative packaged identity along `S.toBase` gives the absolute section law.
  rfl

end CategoryOver
end CategoryTheory
