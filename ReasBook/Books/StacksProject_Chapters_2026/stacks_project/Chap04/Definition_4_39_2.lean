module

public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Definition_4_39_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

/-
Domain-style sampling for Definition 4.39.2:
- primary domain: categories fibred over a base with fiberwise setoid `1`-category structure;
- inspected owner-level declarations:
  `IsFibredInGroupoids`,
  `Functor.Fiber`,
  `Quiver.IsThin`,
  `isThin_iff_subsingleton_aut`;
- best owner abstraction: there is no earlier owner in the chapter for “fibred in setoids”, so the
  correct public owner here is the minimal class obtained by adjoining fiberwise thinness to the
  existing owner `IsFibredInGroupoids`;
- primitive data: `IsFibredInGroupoids p` together with `Quiver.IsThin (p.Fiber U)` for each
  `U : C`;
- derived API: the owner-level specification theorem
  `isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin`, the source-facing automorphism
  criterion `isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_subsingleton_aut`, instance
  search on each fiber, and the bundled owner
  `FibredInSetoidsOver C` defined downstream.

Source/core/bridge triage:
- `source-facing`: `IsFibredInSetoids p`;
- `core/canonical`: `IsFibredInGroupoids p` and `Quiver.IsThin (p.Fiber U)`;
- `bridge/view`: the automorphism reformulation obtained fiberwise from
  `isThin_iff_subsingleton_aut`. -/

/-- Definition 4.39.2: a category fibred in setoids over `C` is a functor `p : S ⥤ C` that is
fibred in groupoids and whose standard fiber `p.Fiber U` is a setoid `1`-category for every
object `U` of `C`. -/
@[mk_iff isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin]
class IsFibredInSetoids (p : S ⥤ C) : Prop extends IsFibredInGroupoids p where
  /-- Each standard fiber of a category fibred in setoids is thin. -/
  fiber_isThin (U : C) : Quiver.IsThin (p.Fiber U)

attribute [instance] IsFibredInSetoids.fiber_isThin

/-- The core owner data for a category fibred in setoids reconstructs the source-facing class. -/
instance (p : S ⥤ C) [IsFibredInGroupoids p] [∀ U : C, Quiver.IsThin (p.Fiber U)] :
    IsFibredInSetoids p :=
  { toIsFibredInGroupoids := inferInstance
    fiber_isThin := inferInstance }

/-- A category fibred in setoids is equivalently a category fibred in groupoids whose every
fiber object has a subsingleton automorphism type. This is the fiberwise source-facing companion
to the owner theorem `isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin`, using
Definition `4.39.1` inside the fibers. -/
theorem isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_subsingleton_aut (p : S ⥤ C) :
    IsFibredInSetoids p ↔
      IsFibredInGroupoids p ∧ ∀ (U : C) (x : p.Fiber U), Subsingleton (Aut x) := by
  rw [isFibredInSetoids_iff_isFibredInGroupoids_and_fiber_thin]
  constructor
  · rintro ⟨hp, hthin⟩
    refine ⟨hp, ?_⟩
    intro U x
    let _ : IsGroupoid (p.Fiber U) := inferInstance
    exact (isThin_iff_subsingleton_aut).1 (hthin U) x
  · rintro ⟨hp, hsub⟩
    refine ⟨hp, ?_⟩
    intro U
    let _ : IsGroupoid (p.Fiber U) := inferInstance
    exact (isThin_iff_subsingleton_aut).2 (hsub U)

end CategoryTheory
