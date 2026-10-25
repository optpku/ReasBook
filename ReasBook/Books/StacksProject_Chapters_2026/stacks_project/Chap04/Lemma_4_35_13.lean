module

public import stacks_project.Chap04.Definition_4_35_1
public import stacks_project.Chap04.Lemma_4_33_11
public import stacks_project.Chap04.Lemma_4_35_2

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Functor

open CategoryTheory.IsHomLift

variable {C : Type u₁} {S : Type u₂} [Category.{v₁} C] [Category.{v₂} S]

/- Domain-style sampling for Lemma 4.35.13:
- primary domain: fibred-in-groupoids structures on functors to a slice category.
- inspected owner-level declarations:
  `CategoryTheory.IsFibredInGroupoids`,
  `Functor.isFibered_of_comp_over_forget`,
  `Functor.isStronglyCartesian_of_comp_over_forget`,
  `IsFibredInGroupoids.isStronglyCartesian_map`.
- best owner abstraction: the source-facing statement should live directly on the owner class
  `IsFibredInGroupoids`; the slice-level structure is derived from the two transfer lemmas of
  Lemma `4.33.11`, not stored through a parallel local wrapper.
- primitive data: the fibred-in-groupoids structure on `p' ⋙ Over.forget U`.
- derived API: the induced `p'.IsFibered` instance from Lemma `4.33.11` and the resulting
  fibred-in-groupoids structure on `p'`.

Source/core/bridge triage:
- `source-facing`: `isFibredInGroupoids_of_comp_over_forget`.
- `core/canonical`: `IsFibredInGroupoids`, `Functor.IsFibered`, `Functor.IsStronglyCartesian`.
- `bridge/view`: the anonymous instance below derived from the source-facing theorem. -/

/-- Helper for Lemma 4.35.13: forgetting a vertical morphism in the slice gives a vertical
morphism in the underlying fiber over the source object. -/
theorem isHomLift_id_comp_over_forget {U : C} (p' : S ⥤ Over U)
    {A : Over U} {x y : S} {g : x ⟶ y} :
    p'.IsHomLift (𝟙 A) g → (p' ⋙ Over.forget U).IsHomLift (𝟙 A.left) g := by
  intro hg
  let q := p' ⋙ Over.forget U
  letI : p'.IsHomLift (𝟙 A) g := hg
  -- Taking underlying arrows in `C` turns the slice identity square into the base identity square.
  refine IsHomLift.of_fac' q (𝟙 A.left) g ?_ ?_ ?_
  · simpa [q] using congrArg (Over.forget U).obj (domain_eq p' (𝟙 A) g)
  · simpa [q] using congrArg (Over.forget U).obj (codomain_eq p' (𝟙 A) g)
  · simpa [q] using congrArg (Over.forget U).map (fac' p' (𝟙 A) g)

/-- Helper for Lemma 4.35.13: every morphism in a fiber of `p'` is invertible because it becomes a
morphism in the corresponding fiber of `p' ⋙ Over.forget U`, which is already a groupoid. -/
theorem fiber_hom_isIso_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] (A : Over U)
    {X Y : p'.Fiber A} (φ : X ⟶ Y) : IsIso φ := by
  let q := p' ⋙ Over.forget U
  letI : p'.IsHomLift (𝟙 A) φ.1 := φ.2
  -- View the slice-fiber morphism as a morphism in the underlying fiber over `A.left`.
  haveI : q.IsHomLift (𝟙 A.left) φ.1 :=
    isHomLift_id_comp_over_forget (p' := p') (A := A) (g := φ.1) inferInstance
  haveI : IsIso (Functor.Fiber.homMk q A.left φ.1) :=
    CategoryTheory.IsFibredInGroupoids.hom_isIso (p := q) A.left
      (Functor.Fiber.homMk q A.left φ.1)
  haveI : IsIso φ.1 := by
    simpa using
      (inferInstance :
        IsIso
          ((Functor.Fiber.fiberInclusion : q.Fiber A.left ⥤ S).map
            (Functor.Fiber.homMk q A.left φ.1)))
  let e := asIso φ.1
  -- The inverse of a vertical isomorphism is vertical over the same identity map.
  haveI : p'.IsHomLift (𝟙 A) e.inv := by
    simpa [e] using (IsHomLift.lift_id_inv_isIso (p := p') A φ.1)
  refine ⟨⟨⟨e.inv, inferInstance⟩, ?_, ?_⟩⟩
  · -- The fiber inverse has the expected underlying composite in `S`.
    apply Functor.Fiber.hom_ext
    change φ.1 ≫ e.inv = 𝟙 X.1
    simp [e]
  · -- The other composite is handled by the underlying inverse in `S`.
    apply Functor.Fiber.hom_ext
    change e.inv ≫ φ.1 = 𝟙 Y.1
    simp [e]

/-- Helper for Lemma 4.35.13: each fiber of `p'` is a groupoid once the fibers of the composed
functor `p' ⋙ Over.forget U` are groupoids. -/
instance fiber_isGroupoid_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] (A : Over U) :
    IsGroupoid (p'.Fiber A) where
  all_isIso := fiber_hom_isIso_of_comp_over_forget p' A

/-- Lemma 4.35.13: if a functor `p' : S ⥤ Over U` becomes fibred in groupoids after composing with
the forgetful functor `Over.forget U : Over U ⥤ C`, then `p'` is itself fibred in groupoids over
`Over U`. Equivalently, if a category fibred in groupoids over `C` factors through the slice
category `C/U`, then the induced functor to `C/U` is fibred in groupoids. -/
theorem isFibredInGroupoids_of_comp_over_forget {U : C} (p' : S ⥤ Over U)
    [IsFibredInGroupoids (p' ⋙ Over.forget U)] :
    IsFibredInGroupoids p' := by
  -- Route correction: follow the textbook proof through fiberedness plus groupoid fibers.
  have hp : p'.IsFibered := isFibered_of_comp_over_forget p'
  -- Each slice fiber inherits its groupoid structure from the corresponding underlying fiber.
  have hfiber : ∀ A : Over U, IsGroupoid (p'.Fiber A) := fun A ↦ by infer_instance
  -- Lemma 4.35.2 packages these two ingredients into the desired fibred-in-groupoids structure.
  exact CategoryTheory.isFibredInGroupoids_of_isFibered_and_fiber_groupoid p' hp hfiber

instance {U : C} (p' : S ⥤ Over U) [IsFibredInGroupoids (p' ⋙ Over.forget U)] :
    IsFibredInGroupoids p' :=
  isFibredInGroupoids_of_comp_over_forget p'

end CategoryTheory.Functor
