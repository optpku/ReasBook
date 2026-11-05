module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import stacks_project.Chap07.Lemma_7_11_2
public import stacks_project.Chap07.Lemma_7_12_4
public import stacks_project.Chap07.Lemma_7_38_2

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe w v u w' w''

namespace CategoryTheory

namespace GrothendieckTopology

attribute [local instance] Types.instFunLike Types.instConcreteCategory

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Helper for Lemma 7.38.3: the fixed `ULift` functor used to compare small and large
type-valued sheaves. -/
abbrev uliftTypeFunctor : Type w' ⥤ Type (max u v w') :=
  CategoryTheory.uliftFunctor.{max u v, w'}

/-- Helper for Lemma 7.38.3: the fiber functor of the universe-enlarged copy of a point. -/
def uliftPointFiberFunctor
    (q : Point.{w'} J) : C ⥤ Type (max u v w') :=
  { obj := fun X ↦ ULift.{max u v, w'} (q.fiber.obj X)
    map := fun {X Y} f x ↦ ULift.up (q.fiber.map f x.down) }

/-- Helper for Lemma 7.38.3: adding or removing `ULift` on the fibers does not change the
covering-lift condition of a sieve. -/
lemma point_cover_lift_ulift_iff
    (q : Point.{w'} J) {U : C} (S : Sieve U) :
    (∀ x : ULift.{max u v, w'} (q.fiber.obj U),
      ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : ULift.{max u v, w'} (q.fiber.obj Y)),
        ULift.up (q.fiber.map g y.down) = x) ↔
      (∀ x : q.fiber.obj U,
        ∃ (Y : C) (g : Y ⟶ U) (_ : S g) (y : q.fiber.obj Y), q.fiber.map g y = x) := by
  constructor
  · intro h x
    -- Remove the `ULift` wrapper from a lifted witness.
    obtain ⟨Y, g, hg, y, hy⟩ := h (ULift.up.{max u v, w'} x)
    refine ⟨Y, g, hg, y.down, ?_⟩
    simpa using congrArg (ULift.down : ULift.{max u v, w'} (q.fiber.obj U) → q.fiber.obj U) hy
  · intro h x
    -- Conversely, lift any witness for `q` to a witness for the `ULift`-wrapped fibers.
    obtain ⟨Y, g, hg, y, hy⟩ := h x.down
    refine ⟨Y, g, hg, ULift.up.{max u v, w'} y, ?_⟩
    cases x
    simpa using
      congrArg (ULift.up.{max u v, w'} : q.fiber.obj U → ULift.{max u v, w'} (q.fiber.obj U)) hy

/-- Helper for Lemma 7.38.3: composing a small type-valued sheaf with the relevant `ULift`
functor still yields a sheaf in the large universe used by the statement. -/
instance uliftFunctor_hasSheafCompose_type :
    J.HasSheafCompose
      (CategoryTheory.uliftFunctor.{max u v, w'} :
        Type w' ⥤ Type (max u v w')) where
  isSheaf P hP := by
    -- Rewrite the sheaf condition into the type-valued form where `ULift` preserves sheaves.
    rw [isSheaf_iff_isSheaf_of_type]
    exact Presieve.isSheaf_comp_uliftFunctor (J := J)
      ((isSheaf_iff_isSheaf_of_type J P).1 hP)

/-- Helper for Lemma 7.38.3: the larger `ULift` target universe still admits sheafification. -/
instance hasSheafify_ulift_type :
    HasSheafify J (Type (max u v w')) := by
  -- The larger universe is large enough to index the cover multiequalizers used by sheafification.
  letI : ∀ X : C, Small.{max u v w', max u v} (J.Cover X)ᵒᵖ := by infer_instance
  infer_instance

end GrothendieckTopology

end CategoryTheory
