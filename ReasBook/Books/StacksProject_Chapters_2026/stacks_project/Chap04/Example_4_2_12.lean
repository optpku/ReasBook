module

public import Mathlib.CategoryTheory.SingleObj
public import Mathlib.Algebra.Category.Grp.EpiMono
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace MonoidHom

variable {M N : Type u} [Monoid M] [Monoid N]

/-
Domain-style sampling for Example 4.2.12:
- primary domain: one-object categories attached to monoids, together with the owner equivalence
  `SingleObj.mapHom` and its user-facing bridge `MonoidHom.toFunctor`; the second statement then
  specializes this monoid-level owner to groups and compares it with `GrpCat.ofHom`;
- sampled owner-level declarations:
  `SingleObj.mapHom`,
  `MonoidHom.toFunctor`,
  `Functor.Faithful.map_injective`,
  `Functor.FullyFaithful.nonempty_iff_map_bijective`,
  `ConcreteCategory.isIso_iff_bijective`;
- best owner abstraction: the owner equivalence `SingleObj.mapHom`; for the source-facing example,
  the relevant specialization is its bridge value `p.toFunctor : SingleObj G ⥤ SingleObj H`;
- primitive data: only the monoid homomorphism `p : M →* N`, since the unique object and unique
  hom-set family in `SingleObj M` are derived from the owner abstraction; the group assumptions
  enter only for the `GrpCat` isomorphism comparison in the second statement;
- derived API: the injective and bijective specializations of the owner functor criteria on the
  unique hom-set, together with the comparison to `IsIso (GrpCat.ofHom p)`.

Source/core/bridge triage:
- `source-facing`: the example-level faithfulness and full-faithfulness criteria for the induced
  one-object-category functor, with a group-level comparison to `GrpCat`;
- `core/canonical`: the owner equivalence `SingleObj.mapHom`, the functor-property predicates
  `p.toFunctor.Faithful` and `Nonempty p.toFunctor.FullyFaithful`, and `IsIso (GrpCat.ofHom p)`;
- `bridge/view`: the specialization of the owner-level functor theorems to the unique object
  `SingleObj.star`. -/

/-- Example 4.2.12 (1): for a monoid homomorphism `p : M →* N`, the induced functor
`p.toFunctor : SingleObj M ⥤ SingleObj N` is faithful exactly when `p` is injective. -/
-- Proof sketch: faithfulness means injectivity on each hom-set; for a single-object category this
-- is exactly injectivity of the underlying monoid homomorphism.
theorem toFunctor_faithful_iff_injective (p : M →* N) :
    p.toFunctor.Faithful ↔ Function.Injective p := by
  constructor
  · intro hp a b hab
    -- Evaluate faithfulness on the unique hom-set of the one-object category.
    exact hp.map_injective (X := SingleObj.star M) (Y := SingleObj.star M) hab
  · intro hp
    refine ⟨?_⟩
    intro X Y f g hfg
    -- After collapsing the objects of `SingleObj`, the map on morphisms is exactly `p`.
    cases X
    cases Y
    exact hp hfg

variable {G H : Type u} [Group G] [Group H]

/-- Helper for Example 4.2.12: the family of hom-set maps induced by `p.toFunctor` is bijective
exactly when the original group homomorphism `p` is bijective. -/
private theorem singleObj_toFunctor_map_bijective_iff (p : G →* H) :
    (∀ X Y : SingleObj G,
      Function.Bijective
        (p.toFunctor.map : (X ⟶ Y) → (p.toFunctor.obj X ⟶ p.toFunctor.obj Y))) ↔
      Function.Bijective p := by
  constructor
  · intro h
    -- Read the universal hom-set criterion on the unique object of `SingleObj G`.
    simpa using h (SingleObj.star G) (SingleObj.star G)
  · intro hp X Y
    -- Every hom-set in `SingleObj G` is the same unique hom-set, so the map is just `p`.
    cases X
    cases Y
    simpa using hp

/-- Example 4.2.12 (2): for a group homomorphism `p : G →* H`, the induced functor
`p.toFunctor : SingleObj G ⥤ SingleObj H` is fully faithful exactly when the corresponding
morphism `GrpCat.ofHom p` is an isomorphism in `GrpCat`. -/
-- Proof sketch: by `Functor.FullyFaithful.nonempty_iff_map_bijective`, full faithfulness of the
-- one-object functor is equivalent to bijectivity of `p`; for group morphisms this is equivalent
-- to `GrpCat.ofHom p` being an isomorphism by `ConcreteCategory.isIso_iff_bijective`.
theorem toFunctor_fullyFaithful_iff_isIso (p : G →* H) :
    Nonempty p.toFunctor.FullyFaithful ↔ IsIso (GrpCat.ofHom p) := by
  -- Reduce full faithfulness to bijectivity on every hom-set of the one-object category.
  rw [Functor.FullyFaithful.nonempty_iff_map_bijective]
  rw [singleObj_toFunctor_map_bijective_iff]
  -- For morphisms in `GrpCat`, being an isomorphism is equivalent to being bijective.
  simpa using (ConcreteCategory.isIso_iff_bijective (GrpCat.ofHom p)).symm

end MonoidHom
