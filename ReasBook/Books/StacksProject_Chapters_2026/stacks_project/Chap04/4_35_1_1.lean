module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.FiberedCategory.Cartesian
import Mathlib.Tactic.Recall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor IsStronglyCartesian

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

section CompositeLiftComparison

variable (p : S ⥤ C)
variable {U V W : C} {x y z z' : S}
variable (f : V ⟶ U) (g : W ⟶ V)
variable (φ : y ⟶ x) (ψ : z ⟶ y) (γ : z' ⟶ x)
variable [p.IsStronglyCartesian f φ] [p.IsStronglyCartesian g ψ]
variable [p.IsStronglyCartesian (g ≫ f) γ]

/-
Domain-style sampling for 4.35.1.1:
- primary domain: fibred categories and strongly cartesian comparison isomorphisms.
- sampled owner-level declarations:
  `Functor.IsStronglyCartesian`,
  `IsStronglyCartesian.comp`,
  `IsStronglyCartesian.domainIsoOfBaseIso`,
  `IsStronglyCartesian.domainUniqueUpToIso_inv_isHomLift`,
  `IsStronglyCartesian.domainUniqueUpToIso_hom_isHomLift`.
- best owner abstraction: `IsStronglyCartesian.domainIsoOfBaseIso`, the canonical isomorphism
  comparing two strongly cartesian lifts over the same base map.
- primitive data: the strongly cartesian lifts `φ`, `ψ`, and `γ` over `f`, `g`, and `g ≫ f`.
- derived API: the two `CommSq` factorizations and the verticality of the comparison arrows.

Source/core/bridge triage:
- `source-facing`: the textbook comparison square of Diagram 4.35.1.1.
- `core/canonical`: `IsStronglyCartesian.domainIsoOfBaseIso`.
- `bridge/view`: the `CommSq` and `IsHomLift` specializations below, which present the owner
  isomorphism in the exact diagrammatic form used by the source. -/

theorem compositeLiftComparisonIso_base :
    g ≫ f = (Iso.refl W).hom ≫ (g ≫ f) := by
  simp

local notation "comparisonIso" =>
  domainIsoOfBaseIso p (compositeLiftComparisonIso_base f g) γ (ψ ≫ φ)

/- 4.35.1.1 is the specialization of the canonical owner isomorphism
`IsStronglyCartesian.domainIsoOfBaseIso` to a direct strongly cartesian lift `γ` of `g ≫ f` and
the iterated strongly cartesian lift `ψ ≫ φ` over the same base morphism. -/
recall IsStronglyCartesian.domainIsoOfBaseIso

-- Proof sketch: apply `IsStronglyCartesian.domainIsoOfBaseIso` to the two strongly cartesian
-- lifts `γ` and `ψ ≫ φ` of the same base morphism `g ≫ f`, using `Iso.refl W` on the source in
-- the base; its defining factorization gives the comparison of Diagram 4.35.1.1.
/-- The hom of the canonical comparison isomorphism gives the commutative square of Diagram
4.35.1.1 comparing the iterated lift with the direct lift. -/
theorem compositeLiftComparisonIso_hom_fac : CommSq (comparisonIso).hom ψ γ φ := by
  refine CommSq.mk ?_
  exact fac p (g ≫ f) γ (compositeLiftComparisonIso_base f g) (ψ ≫ φ)

-- Proof sketch: both `γ` and `ψ ≫ φ` lie over `g ≫ f`, so the comparison isomorphism comes from
-- `IsStronglyCartesian.domainIsoOfBaseIso` with base isomorphism `Iso.refl W`; its hom lies over
-- the identity of the source object `W`.
/-- The hom of the comparison isomorphism in Diagram 4.35.1.1 is vertical over `𝟙 W`. -/
theorem compositeLiftComparisonIso_hom_isHomLift : p.IsHomLift (𝟙 W) (comparisonIso).hom := by
  simpa using
    (domainUniqueUpToIso_inv_isHomLift p
      (compositeLiftComparisonIso_base f g) γ (ψ ≫ φ))

-- Proof sketch: the inverse of `compositeLiftComparisonIso` is the comparison map obtained by
-- swapping the roles of the direct and iterated lifts; its defining factorization gives the
-- second dotted arrow in Diagram 4.35.1.1.
/-- The inverse comparison arrow gives the commutative square of Diagram 4.35.1.1 comparing the
direct lift with the iterated lift. -/
theorem compositeLiftComparisonIso_inv_fac : CommSq (comparisonIso).inv γ (ψ ≫ φ) (𝟙 x) := by
  refine CommSq.mk ?_
  letI : p.IsHomLift ((Iso.refl W).inv ≫ ((Iso.refl W).hom ≫ g ≫ f)) γ := by
    simpa using (inferInstance : p.IsHomLift (g ≫ f) γ)
  have hInv :
      (Iso.refl W).inv ≫ ((Iso.refl W).hom ≫ g ≫ f) = (Iso.refl W).inv ≫ (g ≫ f) := by
    simp
  simpa only [Category.comp_id] using
    (fac p (g ≫ f) (ψ ≫ φ) hInv γ)

-- Proof sketch: as above, the inverse comparison arrow is the universal map between two lifts of
-- `g ≫ f`, hence it also lies over the identity of `W`.
/-- The inverse comparison arrow in Diagram 4.35.1.1 is vertical over `𝟙 W`. -/
theorem compositeLiftComparisonIso_inv_isHomLift : p.IsHomLift (𝟙 W) (comparisonIso).inv := by
  simpa using
    (domainUniqueUpToIso_hom_isHomLift p
      (compositeLiftComparisonIso_base f g) γ (ψ ≫ φ))

end CompositeLiftComparison

end CategoryTheory
