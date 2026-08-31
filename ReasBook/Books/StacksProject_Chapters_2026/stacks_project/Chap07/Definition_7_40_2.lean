module

public import stacks_project.Chap07.Lemma_7_40_1
public import stacks_project.Chap07.Lemma_7_12_5
@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory.GrothendieckTopology

open Opposite

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/- Domain-style sampling for Definition 7.40.2:
- primary domain: Grothendieck topologies and source-facing cover conditions on objects;
- sampled owner API:
  `GrothendieckTopology.Cover`,
  `GrothendieckTopology.Cover.Arrow`,
  `GrothendieckTopology.IsWeaklyContractible`,
  `Sheaf.IsLocallySurjective`;
- source-facing layer: `HasEnoughObjectsWithProperty`, which records that every object admits a
  cover by objects satisfying a given predicate;
- core/canonical owners reused here: the cover owner `J.Cover U` and the predicate owner
  `J.IsWeaklyContractible U`;
- bridge/view layer: the weakly-contractible specialization of
  `J.HasEnoughObjectsWithProperty` and its source-facing unpacking in terms of surjectivity on
  sections.

Primitive data are only the cover `S : J.Cover U` and the predicate on its members. The
surjectivity-on-sections formulation is derived from the owner predicate
`J.IsWeaklyContractible U`, so the public theorem below should reuse that owner theorem instead of
re-expanding the class field by hand. The specialization to weakly contractible objects is just the
owner `J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible)`, so a parallel abbreviation would
be duplicate surface API rather than new mathematics.
-/

/-- A site has enough weakly contractible objects exactly when every object admits a covering whose
members are weakly contractible in the surjectivity-on-sections sense of Definition 7.40.2 (1). -/
theorem hasEnoughWeaklyContractibleObjects_iff :
    J.HasEnoughObjectsWithProperty (J.IsWeaklyContractible) ↔
      ∀ U : C, ∃ S : J.Cover U, ∀ I : S.Arrow,
        ∀ ⦃ℱ 𝒢 : Sheaf J (Type (max u v))⦄
          (π : ℱ ⟶ 𝒢) (_ : Sheaf.IsLocallySurjective π),
            Function.Surjective (π.hom.app (op I.Y)) := by
  simp [HasEnoughObjectsWithProperty, isWeaklyContractible_iff_surjective_sections]

end CategoryTheory.GrothendieckTopology
