module

public import Mathlib.CategoryTheory.Limits.Filtered
public import stacks_project.Chap06.Lemma_6_15_4

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

/- Domain-style sampling for algebraic-structure factorization and commutative squares:
- primary domain: factorization of morphisms in a type of algebraic structure from injectivity of
  the underlying map and containment of underlying ranges, with the result presented as a
  commutative square;
- sampled owner API:
  `morphism_factors_through_of_range_subset_of_injective`,
  `subobject_factors_of_range_subset`,
  `CategoryTheory.CommSq`,
  `CommSq.mk`;
- best owner abstraction:
  `morphism_factors_through_of_range_subset_of_injective` for the factorization itself, with
  `CommSq` as the canonical square-shaped surface;
- primitive data:
  the composite `ab ≫ bd`, the morphism `cd`, injectivity of `F.map cd`, and the range inclusion
  for `F.map (ab ≫ bd)`;
- derived API:
  the existential square witness below is only the specialization `f := ab ≫ bd`, `g := cd` of
  that owner theorem;
- layer:
  `bridge/view`, not a second owner theorem.

The target declaration should therefore reuse the owner theorem directly and only restate its
conclusion in the canonical `CommSq` form.
-/

section

variable {𝒞 : Type u} [Category.{v} 𝒞] (F : 𝒞 ⥤ Type w) [IsAlgebraicStructure 𝒞 F]
variable {A B C D : 𝒞} (ab : A ⟶ B) (bd : B ⟶ D) (cd : C ⟶ D)

-- Proof sketch: apply
-- `morphism_factors_through_of_range_subset_of_injective` to the composite `ab ≫ bd` and the map
-- `cd`; the resulting factorization `ab ≫ bd = t ≫ cd` is exactly the commutativity condition for
-- the square with top edge `ab`, left edge `t`, right edge `bd`, and bottom edge `cd`.
/-- Example 6.15.5: if `C ⟶ D` is injective on underlying sets and the image of the composite
`A ⟶ B ⟶ D` is contained in the image of `C ⟶ D`, then there exists a morphism `A ⟶ C` making
the resulting square commute. -/
theorem exists_commSq_of_composite_range_subset_of_injective
    (hg_injective : Function.Injective (F.map cd))
    (hfg : Set.range (F.map (ab ≫ bd)) ⊆ Set.range (F.map cd)) :
    ∃ t : A ⟶ C, CommSq ab t bd cd := by
  -- First factor the composite `A ⟶ B ⟶ D` through `cd` using the range criterion.
  rcases morphism_factors_through_of_range_subset_of_injective
      F (ab ≫ bd) cd hg_injective hfg with ⟨t, ht⟩
  refine ⟨t, ?_⟩
  -- The factorization equality is exactly the commutativity condition for the square.
  exact CommSq.mk ht

end
