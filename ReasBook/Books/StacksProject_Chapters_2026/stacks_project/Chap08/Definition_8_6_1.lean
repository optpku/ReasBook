module

public import Mathlib
public import stacks_project.Chap04.Definition_4_38_2
public import stacks_project.Chap04.Definition_4_39_2
public import stacks_project.Chap08.Definition_8_5_1


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

section

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]
variable (J : GrothendieckTopology C) (p : S ⥤ C)

/-
Domain-style sampling for Definition 8.6.1:
- primary domain: stacks on a site with additional fiberwise setoid/discrete conditions.
- inspected owner-level declarations:
  `IsStackInGroupoids`,
  `IsFibredInSetoids`,
  `IsFibredInSets`.
- best owner abstraction: this chapter already organizes stack-theoretic owners by the projection
  functor `p : S ⥤ C` through the owner `IsStackInGroupoids J p`, so the source-facing notions
  here should refine that owner by adjoining the stronger fiberwise setoid/discrete conditions.
- primitive data: `IsStackInGroupoids J p` together with `IsFibredInSetoids p`, and then
  `IsStackInGroupoids J p` together with `IsFibredInSets p`.
- derived API: the later bundled subcategory `StackInSetoidsOver`, together with the automatic
  bridge from stacks in sets to stacks in setoids.

Source/core/bridge triage:
- `source-facing`: `IsStackInSetoids J p` and `IsStackInSets J p`.
- `core/canonical`: `IsStackInGroupoids`, `IsFibredInSetoids`, `IsFibredInSets`.
- `bridge/view`: the later bundled owner `StackInSetoidsOver`. -/

/-- Definition 8.6.1 (1): a stack in setoids over the site `(C, J)` is a category over `C` whose
projection functor is a stack in groupoids over `(C, J)` and is fibred in setoids. Equivalently,
every fiber category over an object of `C` is a setoid `1`-category. -/
@[mk_iff isStackInSetoids_iff_isFibredInSetoids_and_isStackInGroupoids]
class IsStackInSetoids (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsFibredInSetoids p, IsStackInGroupoids J p

/-- A stack in groupoids whose fibers are setoids is a stack in setoids. -/
instance [IsFibredInSetoids p] [IsStackInGroupoids J p] : IsStackInSetoids J p where
  -- The source-facing owner is exactly the conjunction of the setoid-fiber owner and the
  -- inherited stack data carried by `IsStackInGroupoids`.
  toIsFibredInSetoids := inferInstance
  toIsStack := inferInstance

/-- Definition 8.6.1 (2): a stack in sets over `(C, J)` is a stack in groupoids over `(C, J)` whose
fiber category over every object of `C` is discrete. Equivalently, it is a stack in setoids whose
fibers are discrete, or a stack in discrete categories. -/
@[mk_iff isStackInSets_iff_isFibredInSets_and_isStackInGroupoids]
class IsStackInSets (J : GrothendieckTopology C) (p : S ⥤ C) : Prop
    extends IsFibredInSets p, IsStackInGroupoids J p

/-- A stack in groupoids whose fibers are discrete is a stack in sets. -/
instance [IsFibredInSets p] [IsStackInGroupoids J p] : IsStackInSets J p where
  -- The discrete-fiber case is packaged by the same owner-level inheritance pattern, reusing the
  -- stack data already present in `IsStackInGroupoids`.
  toIsFibredInSets := inferInstance
  toIsStack := inferInstance

/-- A stack in sets over `(C, J)` is canonically a stack in setoids. -/
instance [IsStackInSets J p] : IsStackInSetoids J p := by
  -- Route correction: the bridge stays owner-level, so first recover the thin-fiber owner.
  let _ : IsFibredInSetoids p := inferInstance
  -- With the stack and setoid-fiber owners now available, the constructor instance closes.
  exact inferInstance

end

end CategoryTheory
