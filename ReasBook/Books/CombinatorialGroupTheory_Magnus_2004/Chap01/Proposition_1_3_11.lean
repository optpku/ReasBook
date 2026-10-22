/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_28

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open CategoryTheory

section

variable {F : Type u} [Group F] [IsFreeGroup F]
variable (A : Finset F) (H : Subgroup F)

/-- Proposition 1-3-11: if `F` is a free group, `A` is a finite subset of `F`, and `H` is a
finitely generated subgroup of `F` disjoint from `A`, then there exists a finite-index subgroup
`G ≤ F` that is still disjoint from `A` and in which `H` is a free factor. -/
-- Layer triage:
-- `source-facing`: the existential overgroup `G : Subgroup F` of finite index and disjoint from
-- `A`.
-- `core/canonical`: the chapter owner predicate `Subgroup.IsFreeFactorOf`.
-- `bridge/view`: the textbook phrase "H is a free factor of G" is unpacked by
-- `Subgroup.isFreeFactorOf_iff` into the overgroup relation `H ≤ G` together with a
-- complementary free factor for `H.subgroupOf G` inside `G`.
--
-- Domain sampling:
-- 1. `Subgroup.IsFreeFactorOf` in Definition `1-2-28` is the chapter owner abstraction for the
--    source phrase “`H` is a free factor of `G`”.
-- 2. `Subgroup.AreFreeFactors` remains the underlying two-factor decomposition owner inside the
--    ambient overgroup `G`.
-- 3. `Subgroup.IsFreeFactorOf.isSplitMono` packages the split-inclusion bridge for the subgroup
--    inclusion into the overgroup.
-- 4. `Subgroup.subtype_isSplitMono_iff_exists_leftInverse` is the chapter owner criterion for a
--    retract subgroup.
--
-- Primitive vs. derived:
-- the primitive source data are only the finite subset `A`, the subgroup `H`, its finite
-- generation, and disjointness from `A`. The complementary subgroup inside the overgroup and the
-- resulting split inclusion are derived owner-level consequences and should not be repackaged as
-- additional primitive data.
-- Proof sketch: apply Hall's finite-index extension argument to the explicit finite-generation
-- hypothesis `hfg : H.FG` to obtain an overgroup `G` of `H` that avoids `A`, then invoke the
-- Nielsen-Schreier free-basis construction inside `G` to split the embedded subgroup
-- `H.subgroupOf G` off as a free factor.
theorem exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor
    (hfg : H.FG) (hA : Disjoint (A : Set F) (H : Set F)) :
    ∃ G : Subgroup F,
      G.FiniteIndex ∧
        Disjoint (A : Set F) (G : Set F) ∧
        H.IsFreeFactorOf G := sorry

/-- Owner-level bridge for Proposition 1-3-11: the same finite-index overgroup can be chosen so
that the transported inclusion of `H` into `G` is split. -/
-- Layer triage:
-- `bridge/view`: this is the canonical retract-subgroup reformulation of the source-facing
-- free-factor conclusion, obtained from `Subgroup.IsFreeFactorOf.isSplitMono`.
theorem exists_finiteIndex_overgroup_disjoint_from_finset_with_split_subtype
    (hfg : H.FG) (hA : Disjoint (A : Set F) (H : Set F)) :
    ∃ G : Subgroup F,
      G.FiniteIndex ∧
        Disjoint (A : Set F) (G : Set F) ∧
        IsSplitMono (GrpCat.ofHom (H.subgroupOf G).subtype) := by
  rcases exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor A H hfg hA with
    ⟨G, hG, hdisj, hfree⟩
  exact ⟨G, hG, hdisj, hfree.isSplitMono⟩

end
