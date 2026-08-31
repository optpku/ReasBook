module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe w v₁ v₂ u

namespace CategoryTheory
namespace Pseudofunctor.CoGrothendieck

open HasFibers
open Opposite
open scoped Bicategory

variable {𝒞 : Type u} [Category.{v₁} 𝒞]

/- Domain-style sampling for Example 4.37.1:
- primary domain: co-Grothendieck constructions of contravariant groupoid-valued functors and
  categories fibred in groupoids.
- inspected owner-level declarations:
  `Pseudofunctor.CoGrothendieck.forget`,
  `HasFibers.inducedFunctor`,
  `IsFibredInGroupoids`,
  `isFibredInGroupoids_of_isFibered_and_fiber_groupoid`.
- best owner abstraction: `IsFibredInGroupoids` on the canonical projection
  `forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')`; the groupoid-valued presheaf is primitive
  data, while the fibred-in-groupoids structure is derived.
- primitive data: `F : 𝒞ᵒᵖ ⥤ Grpd`.
- derived API: the source-facing theorem `groupoidPresheafProjection_isFibredInGroupoids` and
  the resulting canonical `IsFibredInGroupoids` instance on the projection.

Source/core/bridge triage:
- `source-facing`: Example 4.37.1, asserting that the split category attached to a presheaf of
  groupoids is fibred in groupoids over the base.
- `core/canonical`: `Pseudofunctor.CoGrothendieck.forget`, `HasFibers.inducedFunctor`, and
  `IsFibredInGroupoids`.
- `bridge/view`: the passage from `F : 𝒞ᵒᵖ ⥤ Grpd` to the underlying `Cat`-valued pseudofunctor
  `(F ⋙ Grpd.forgetToCat).toPseudofunctor'`. -/

/- Example 4.37.1: for a presheaf of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd`, the associated category
`𝒮_F` over `𝒞` is the canonical projection `forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')`
from the
co-Grothendieck construction of the underlying `Cat`-valued pseudofunctor. -/
example (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    ∫ᶜ ((F ⋙ Grpd.forgetToCat).toPseudofunctor') ⥤ 𝒞
    :=
  forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')

private instance groupoidPresheafProjection_fiber_isGroupoid
    (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) (U : 𝒞) :
    IsGroupoid ((forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')).Fiber U) := by
  let p := forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')
  haveI : IsGroupoid (Fib p U) := by
    change IsGroupoid (F.obj (op U))
    infer_instance
  simpa [p] using
    (isGroupoid_of_reflects_iso (HasFibers.inducedFunctor p U).asEquivalence.symm.functor :
      IsGroupoid (p.Fiber U))

-- Proof sketch: the co-Grothendieck construction attached to `(F ⋙ Grpd.forgetToCat)` is
-- fibered by the canonical cartesian lifts from `FiberedCategory.Grothendieck`. Since each fiber
-- category is a groupoid because `F` lands in `Grpd`, Lemma 4.35.2 upgrades this to a category
-- fibred in groupoids.
/-- Example 4.37.1: for a presheaf of groupoids `F : 𝒞ᵒᵖ ⥤ Grpd`, the canonical projection
`forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor') : 𝒮_F ⥤ 𝒞` is fibred in groupoids. -/
theorem groupoidPresheafProjection_isFibredInGroupoids
    (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    IsFibredInGroupoids (forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) := by
  refine
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid
      (forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) inferInstance ?_
  intro U
  infer_instance

instance (F : 𝒞ᵒᵖ ⥤ Grpd.{v₂, w}) :
    IsFibredInGroupoids (forget ((F ⋙ Grpd.forgetToCat).toPseudofunctor')) :=
  groupoidPresheafProjection_isFibredInGroupoids F

end Pseudofunctor.CoGrothendieck
end CategoryTheory
