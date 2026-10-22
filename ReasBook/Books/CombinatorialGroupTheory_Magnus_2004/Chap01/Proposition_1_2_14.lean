/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_28

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {F G : Type u} [Group F] [IsFreeGroup F] [Group G] [IsFreeGroup G]

/-- Proposition 1-2-14: a surjective homomorphism from a finitely generated free group onto a free
group splits the domain as free factors `F₁ * F₂`, with the restriction to `F₁` bijective and the
restriction to `F₂` trivial. The source's finite-rank hypothesis is redundant for this owner-level
splitting statement, so it is not exposed in the refined API. Unpacking
`Subgroup.AreFreeFactors F₁ F₂` recovers the textbook basis partition `Z = Z₁ ⊔ Z₂`. -/
-- Layer triage:
-- `source-facing`: the decomposition of `F` into the part seen by `φ` and the part killed by `φ`.
-- `core/canonical`: `Subgroup.AreFreeFactors`, together with the restricted homomorphisms
-- `φ.comp F₁.subtype` and `φ.comp F₂.subtype`.
-- `bridge/view`: unpacking `Subgroup.AreFreeFactors F₁ F₂` yields disjoint generating subsets
-- `Z₁`, `Z₂` whose union is a free basis of `F`.
--
-- Domain sampling:
-- 1. `Subgroup.AreFreeFactors` from Definition `1-2-28` is the chapter owner abstraction for a
--    free-product decomposition inside `F`.
-- 2. `Subgroup.exists_complement_iff_exists_leftInverse` is the owner bridge from a split
--    inclusion to a complementary free factor.
-- 3. `Subgroup.subtype_isSplitMono_iff_exists_leftInverse` is the retract-subgroup owner
--    criterion used to pass from a section of `φ` to a free-factor decomposition.
-- 4. `projective_group_iff_free_group` and `group_projective_iff_lifts_along_surjective` identify
--    freeness of `G` with the existence of a section of `φ`.
--
-- Primitive vs. derived:
-- the primitive source data are only `φ` and its surjectivity. The basis subsets from the
-- textbook formulation are derived witnesses obtained by unpacking the owner relation
-- `Subgroup.AreFreeFactors`.
-- Proof sketch: because `G` is free, it is projective, so the surjection `φ` admits a section.
-- The image of that section is therefore a retract subgroup of the free group `F`, hence a free
-- factor by `Subgroup.exists_complement_iff_exists_leftInverse`. The induced idempotent
-- endomorphism of `F` fixes the first factor pointwise and kills the complementary factor, giving
-- the stated restricted-map properties.
theorem exists_free_factor_decomposition_of_surjective_to_free (φ : F →* G)
    (hφ : Function.Surjective φ) :
    ∃ F₁ F₂ : Subgroup F,
      Subgroup.AreFreeFactors F₁ F₂ ∧
        Function.Bijective (φ.comp F₁.subtype) ∧
        φ.comp F₂.subtype = 1 := sorry

/-- Companion bridge: unpacking the owner-level free-factor decomposition yields the textbook
basis partition from Proposition 1-2-14. -/
-- Proof sketch: apply
-- `exists_free_factor_decomposition_of_surjective_to_free`, then unpack
-- `Subgroup.AreFreeFactors` to obtain disjoint basis subsets `Z₁`, `Z₂` with
-- `Subgroup.closure Z₁ = F₁` and `Subgroup.closure Z₂ = F₂`.
theorem exists_basis_partition_of_surjective_to_free (φ : F →* G) (hφ : Function.Surjective φ) :
    ∃ Z₁ Z₂ : Set F,
      Disjoint Z₁ Z₂ ∧
        IsFreeGroupBasis (Z₁ ∪ Z₂) ∧
        Function.Bijective (φ.comp (Subgroup.closure Z₁).subtype) ∧
        φ.comp (Subgroup.closure Z₂).subtype = 1 := sorry
