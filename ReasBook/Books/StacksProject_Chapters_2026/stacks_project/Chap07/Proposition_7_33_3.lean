module

public import Mathlib.CategoryTheory.Functor.TypeValuedFlat
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf


@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits

universe w v

namespace CategoryTheory

variable {C : Type w} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable [HasFiniteLimits C]

/- Domain-style sampling for Proposition 7.33.3:
- primary domain: points of Grothendieck sites and the characterization of their underlying
  set-valued fiber functors;
- sampled owner declarations:
  `GrothendieckTopology.Point`,
  `GrothendieckTopology.Point.jointly_surjective`,
  `GrothendieckTopology.Point.isCofiltered`,
  `Functor.isCofiltered_elements`;
- source/core/bridge triage:
  `source-facing`: a set-valued functor `u` satisfying finite-limit preservation and the
    covering-sieve lifting condition;
  `core/canonical`: the owner abstraction `J.Point`, whose primitive data are the fiber functor,
    cofilteredness/initial smallness of its category of elements, and covering surjectivity;
  `bridge/view`: the equivalence below between existence of a point with fiber `u` and the two
    source-facing conditions on `u`.

The primitive source data are the functor `u` and the covering-sieve lifting condition. The point
itself should remain the canonical mathlib owner `GrothendieckTopology.Point`; the covering
condition is factored only to keep the proposition atomic and reusable.
-/
/-- A set-valued functor satisfies the covering-sieve lifting condition used to construct a
point of a Grothendieck site. -/
def CoversLiftToFunctorFibers (u : C ⥤ Type (max w v)) : Prop :=
  ∀ {X : C} (R : Sieve X), R ∈ J X → ∀ x : u.obj X,
    ∃ (Y : C) (f : Y ⟶ X), R f ∧ ∃ y : u.obj Y, u.map f y = x

-- Proof sketch: for `p : J.Point`, finite-limit preservation is the canonical instance on
-- `p.fiber`, and covering-surjectivity is exactly `p.jointly_surjective`. Conversely, use
-- `Functor.isCofiltered_elements` and the lifting condition to build the point structure.
/-- Proposition 7.33.3: a set-valued functor on a site with finite limits underlies a point
exactly when it preserves finite limits and every covering sieve acts jointly surjectively on its
fibers. This is the canonical covering-sieve formulation of the source statement. -/
theorem exists_point_with_fiber_iff_preservesFiniteLimits_and_covering_jointlySurjective
    (u : C ⥤ Type (max w v)) :
    (∃ p : GrothendieckTopology.Point.{max w v} J, p.fiber = u) ↔
      PreservesFiniteLimits u ∧ CoversLiftToFunctorFibers J u := by
  constructor
  · -- Unpack the point witness so the fiber functor is literally `p.fiber`.
    rintro ⟨p, rfl⟩
    constructor
    · -- A point fiber preserves finite limits by the canonical mathlib instance.
      infer_instance
    · -- The covering-lift condition is exactly the `jointly_surjective` field.
      intro X R hR x
      simpa [CoversLiftToFunctorFibers] using p.jointly_surjective R hR x
  · rintro ⟨hu, hcover⟩
    -- Build the cofiltered category of elements from finite-limit preservation.
    letI : PreservesFiniteLimits u := hu
    -- Package the source data into the canonical `Point` structure.
    refine ⟨{
      fiber := u
      isCofiltered := Functor.isCofiltered_elements u
      initiallySmall := initiallySmall_of_essentiallySmall u.Elements
      jointly_surjective := ?_
    }, rfl⟩
    intro X R hR x
    obtain ⟨Y, f, hf, y, hy⟩ := hcover R hR x
    exact ⟨Y, f, hf, y, hy⟩

end CategoryTheory
