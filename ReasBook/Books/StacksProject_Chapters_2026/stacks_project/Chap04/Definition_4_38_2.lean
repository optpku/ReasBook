module

import Mathlib.CategoryTheory.Groupoid.Discrete
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-
Domain-style sampling for Definition 4.38.2:
- primary domain: fibred categories with fiberwise discrete-category structure.
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Functor.IsFibered`,
  `Functor.Fiber`,
  `IsDiscrete`,
  `isFibredInGroupoids_iff_isFibered_and_fiber_groupoid`,
  `IsFibredInSetoids`.
- best owner abstraction: the source-facing notion here is a fibred-in-groupoids functor whose
  standard fibers are discrete; the public owner should therefore extend the existing chapter
  owner `IsFibredInGroupoids`, while the textbook `p.IsFibered` formulation remains as a
  companion characterization.
- primitive data: `IsFibredInGroupoids p` together with `IsDiscrete (p.Fiber U)` for each base
  object `U`; equivalently, and more primitively on the source side, `p.IsFibered` together with
  `IsDiscrete (p.Fiber U)` for each base object `U`.
- derived API: the owner-level specification theorem
  `isFibredInSets_iff_isFibredInGroupoids_and_fiber_discrete`, instance search on each fiber,
  and downstream setoid-valued specializations.

Source/core/bridge triage:
- `source-facing`: `IsFibredInSets p`.
- `core/canonical`: `IsFibredInGroupoids p`, `Functor.Fiber`, `IsDiscrete`.
- `bridge/view`: the owner-level specification theorem
  `isFibredInSets_iff_isFibredInGroupoids_and_fiber_discrete`, together with the downstream
  coercions to fibred-in-setoids and bundled-over-category APIs. -/

/-- Definition 4.38.2: a category fibred in sets, or a category fibred in discrete categories,
over `C` is a functor `p : S ⥤ C` that is fibred and whose fiber category `p.Fiber U` is discrete
for every object `U` of `C`; equivalently, it is fibred in groupoids with discrete fibers. -/
@[mk_iff isFibredInSets_iff_isFibredInGroupoids_and_fiber_discrete]
class IsFibredInSets (p : S ⥤ C) : Prop extends IsFibredInGroupoids p where
  /-- Each standard fiber of a category fibred in sets is a discrete category. -/
  fiber_isDiscrete (U : C) : IsDiscrete (p.Fiber U)

attribute [instance] IsFibredInSets.fiber_isDiscrete

/-- The owner-level data for a category fibred in sets is exactly fiberedness together with
discrete standard fibers. -/
instance (p : S ⥤ C) [p.IsFibered] [∀ U : C, IsDiscrete (p.Fiber U)] :
    IsFibredInSets p where
  toIsFibredInGroupoids :=
    isFibredInGroupoids_of_isFibered_and_fiber_groupoid p inferInstance fun _ ↦ inferInstance
  fiber_isDiscrete := inferInstance

end CategoryTheory
