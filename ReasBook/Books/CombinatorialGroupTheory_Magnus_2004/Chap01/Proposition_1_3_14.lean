/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_11

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-14: the intersection of two finitely generated subgroups of a free group is
itself finitely generated. -/
-- Layer triage:
-- `source-facing`: two finitely generated subgroups `H, K : Subgroup F` of the ambient free group.
-- `core/canonical`: the subgroup lattice infimum `H ⊓ K`, the finite-generation predicate
-- `Subgroup.FG`, Hall's finite-index split-subtype enlargement theorem
-- `exists_finiteIndex_overgroup_disjoint_from_finset_with_split_subtype`, the subgroup-owner view
-- `Subgroup.subgroupOf`, and Schreier's finite-generation owner `Subgroup.fg_of_index_ne_zero`.
-- `bridge/view`: the textbook phrase “intersection of subgroups” is expressed directly by `H ⊓ K`;
-- any retract data needed in the proof should be handled through the existing chapter owner API
-- `Subgroup.subtype_isSplitMono_iff_exists_leftInverse`, not by a parallel local finite-generation
-- wrapper.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the owner predicate for subgroup finite
--    generation.
-- 2. `exists_finiteIndex_overgroup_disjoint_from_finset_with_split_subtype` in Proposition
--    `1-3-11` is the chapter owner theorem that upgrades a finitely generated subgroup to a
--    finite-index overgroup with split inclusion.
-- 3. `Subgroup.subgroupOf` in `Mathlib/Algebra/Group/Subgroup/Map` is the canonical owner for
--    transporting intersections into an overgroup.
-- 4. `Subgroup.fg_of_index_ne_zero` in `Mathlib/GroupTheory/Schreier` is the canonical owner
--    theorem that finite-index subgroups of finitely generated groups are finitely generated.
--
-- Best owner abstraction:
-- the theorem belongs directly at the subgroup-owner level `Subgroup F`, with `H ⊓ K` as the
-- canonical intersection object. Any split-inclusion or retract argument in the proof is derived
-- bridge data and should reuse the existing owner-level chapter API rather than introducing a
-- second local owner for finitely generated retracts.
--
-- Primitive vs. derived:
-- the primitive public data are only `H`, `K`, and the two hypotheses `hH : H.FG`, `hK : K.FG`.
-- Any finite-index overgroup, restricted subgroup transport, or left inverse used to descend
-- finite generation to `H ⊓ K` is derived proof input, not public data.
theorem fg_inf_of_fg (H K : Subgroup F) (hH : H.FG) (hK : K.FG) : (H ⊓ K).FG := sorry

end
