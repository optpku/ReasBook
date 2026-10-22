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

/-- Proposition 1-3-12: a finitely generated subgroup of a free group that contains a nontrivial
normal subgroup of the ambient free group has finite index. -/
-- Layer triage:
-- `source-facing`: a finitely generated subgroup `H : Subgroup F` together with a nontrivial
-- ambient-normal subgroup `N : Subgroup F` contained in `H`.
-- `core/canonical`: the subgroup owner `Subgroup F` with the canonical predicates
-- `Subgroup.FG`, `Subgroup.Normal`, and `Subgroup.FiniteIndex`, together with the order relation
-- `N ≤ H`.
-- `bridge/view`: the textbook phrase “`H` contains a non-trivial normal subgroup of `F`” is
-- expressed directly by the witness `N` and the atomic hypotheses `N ≤ H`, `N.Normal`, and
-- `N ≠ ⊥`; no extra wrapper around contained normal subgroups is introduced.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the canonical owner predicate for
--    finite index.
-- 3. `Subgroup.AreFreeFactors` in Definition `1-2-28` is the chapter owner abstraction for the
--    free-factor decomposition produced by Hall's theorem.
-- 4. `exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor` in Proposition `1-3-11`
--    is the chapter owner theorem that supplies the finite-index overgroup in which `H` becomes a
--    free factor.
--
-- Best owner abstraction:
-- the public statement should stay at the subgroup-owner level. The free-factor overgroup from
-- Proposition `1-3-11` is derived proof input, not additional primitive public data for this
-- proposition.
--
-- Primitive vs. derived:
-- the primitive source data are exactly `H`, `N`, finite generation of `H`, containment `N ≤ H`,
-- normality of `N`, and nontriviality of `N`. The auxiliary finite-index overgroup and its
-- complementary free factor are derived from Proposition `1-3-11`, so they should remain inside
-- the proof architecture rather than being exposed as a parallel wrapper API.
-- Proof sketch: apply Proposition 1-3-11 to enlarge `H` to a finite-index subgroup `G` in which
-- `H` is a free factor. If `H` had infinite index, the complementary free factor in `G` would be
-- nontrivial. Conjugating a nontrivial element of `N` by an element of that complement produces an
-- element of `N` that cannot lie in the free factor `H`, contradicting `N ≤ H`.
theorem finiteIndex_of_fg_of_contains_nontrivial_normal (H N : Subgroup F) (hfg : H.FG)
    (hN_le : N ≤ H) (hN_normal : N.Normal) (hN : N ≠ ⊥) : H.FiniteIndex := sorry

end
