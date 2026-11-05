module

public import stacks_project.Chap04.Lemma_4_34_1

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open BasedCategory
open BasedFunctor
open FibredCategoryMor

variable {C : Type u} [Category.{v} C]

namespace FibredCategoryOver

/- Domain-style sampling for `4.34.2.1`:
- primary domain: categories fibred over a fixed base `C` and the relative/absolute inertia
  attached to a morphism of fibred categories.
- inspected owner declarations:
  `FibredCategoryOver`,
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.toFunctor`,
  `CategoryTheory.relativeInertiaProjection`,
  `CategoryTheory.relativeInertiaProjection_isFibered`.
- best owner abstraction: `FibredCategoryOver C`; the underlying `CategoryOver C` object is a
  derived view, not the main owner.
- primitive-vs-derived split: the source-facing fibred owner here is
  `relativeInertiaOver F`; the absolute inertia is exposed at the `Cat/C` bridge/view layer, where
  the structure morphism to the base has the required owner universe.

Source/core/bridge triage:
- `source-facing`: `FibredCategoryOver.relativeInertiaOver`;
- `core/canonical`: `FibredCategoryOver.ofFunctor`, `FibredCategoryMor.toFunctor`,
  `relativeInertiaProjection`, and `relativeInertiaProjection_isFibered`;
- `bridge/view`: the `CategoryOver` views of those owners and
  `CategoryOver.relativeInertiaStructureMap`. -/

-- Proof sketch: unpack the identity functor over `C`; the chosen lift of `f` is just `f`,
-- and the universal property is the ordinary categorical uniqueness for identities.
/-- Helper for 4.34.2.1: the identity functor of `C` sends every arrow to a strongly cartesian
lift of itself. -/
private theorem idFunctor_isStronglyCartesian {R T : C} (f : R ⟶ T) :
    Functor.IsStronglyCartesian (𝟭 C) f f where
  -- The displayed arrow is tautologically a lift of itself for the identity functor.
  toIsHomLift := by
    simpa using
      (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map f) f from inferInstance)
  universal_property' := by
    intro a g φ hφ
    -- Any competing lift over `g ≫ f` is definitionally the same composite.
    subst_hom_lift (𝟭 C) (g ≫ f) φ
    refine ⟨g, ?_, ?_⟩
    · constructor
      · simpa using
          (show Functor.IsHomLift (𝟭 C) ((𝟭 C).map g) g from inferInstance)
      · rfl
    · intro π hπ
      -- Uniqueness reduces to the fact that a lift over `g` for the identity functor is just `g`.
      let _ := hπ.1
      subst_hom_lift (𝟭 C) g π
      rfl

/-- Helper for 4.34.2.1: the identity functor of the base category is fibered. -/
private instance idFunctor_isFibered : (𝟭 C).IsFibered := by
  -- For a base arrow `f`, choose `f` itself as the strongly cartesian lift.
  apply Functor.IsFibered.of_exists_isStronglyCartesian
  intro a R f
  exact ⟨R, f, idFunctor_isStronglyCartesian f⟩

-- Proof sketch: a fibred category projection preserves its own strongly cartesian arrows by
-- definition, so the structure morphism to the base fibred category is cartesian-preserving.
/-- Helper for 4.34.2.1: the projection of a fibred category over `C` preserves strongly
cartesian morphisms. -/
theorem toBase_preservesStronglyCartesian
    (X : FibredCategoryOver C) :
    PreservesStronglyCartesian (X.toBasedCategory.toBase) := by
  intro a b φ hφ
  -- After applying the base projection, the target functor is the identity on `C`.
  simpa [BasedCategory.toBase] using idFunctor_isStronglyCartesian (X.p.map φ)

/-- The canonical morphism from a fibred category over `C` to the base fibred category
`(C, 𝟭 C)`. -/
abbrev toBase (X : FibredCategoryOver C) :
    X ⟶ FibredCategoryOver.ofFunctor (𝟭 C) :=
  ofBasedFunctor X.toBasedCategory.toBase
    (toBase_preservesStronglyCartesian X)

variable {X Y : FibredCategoryOver C}

/-- The relative inertia over `C` attached to a morphism of fibred categories
`F : X ⟶ Y`. -/
abbrev relativeInertiaOver (F : X ⟶ Y) :
    FibredCategoryOver C :=
  FibredCategoryOver.ofFunctor
    (relativeInertiaProjection (toFunctor F) X.p)

end FibredCategoryOver

namespace CategoryOver

variable {X Y : CategoryOver C}

/-- The relative inertia over `C`, packaged directly in `Cat/C`. -/
abbrev relativeInertiaOver (F : X ⥤ᵇ Y) :
    CategoryOver C :=
  BasedCategory.ofFunctor (relativeInertiaProjection F.toFunctor X.p)

/-- The absolute inertia over `C`, packaged directly in `Cat/C`. -/
abbrev absoluteInertiaOver (X : CategoryOver C) :
    CategoryOver C :=
  relativeInertiaOver X.toBase

/-- 4.34.2.1: the relative inertia `\mathcal I_{\mathcal X / \mathcal Y}` has its canonical
`Cat/\mathcal C` bridge to `\mathcal X`, obtained by packaging
`relativeInertiaStructureFunctor F.toFunctor` over `C`. -/
abbrev relativeInertiaStructureMap (F : X ⥤ᵇ Y) :
    relativeInertiaOver F ⥤ᵇ X :=
  { toFunctor := relativeInertiaStructureFunctor F.toFunctor
    w := rfl }

-- Proof sketch: unfold the bundled based functor defining the relative inertia structure map.
/-- The relative inertia structure map has the expected underlying forgetful functor. -/
theorem relativeInertiaStructureMap_toFunctor (F : X ⥤ᵇ Y) :
    (relativeInertiaStructureMap F).toFunctor =
      relativeInertiaStructureFunctor F.toFunctor := by
  -- The packaged morphism was defined with this underlying functor.
  rfl

end CategoryOver

end CategoryTheory
