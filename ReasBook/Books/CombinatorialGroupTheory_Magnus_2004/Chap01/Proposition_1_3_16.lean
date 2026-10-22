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

/-- Proposition 1-3-16: a finitely generated subgroup of a free group that is contained in no
overgroup of infinite rank has finite index. -/
-- Layer triage:
-- `source-facing`: a subgroup `H : Subgroup F` and the hypothesis that every overgroup `K ≥ H`
-- has finite rank.
-- `core/canonical`: `Subgroup.FG`, `Subgroup.FiniteIndex`, and the order relation `H ≤ K` on
-- the subgroup lattice.
-- `bridge/view`: in a free group, “infinite rank” is expressed as failure of finite generation for
-- a subgroup, since every subgroup is itself free.
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the canonical owner predicate for
--    finite index.
-- 3. `subgroupIsFreeOfIsFree` in
--    `Mathlib/GroupTheory/FreeGroup/NielsenSchreier` is the owner theorem that lets the source
--    phrase “infinite rank” be expressed through subgroup finite generation.
-- 4. `exists_finiteIndex_overgroup_disjoint_from_finset_with_free_factor` in Proposition `1-3-11`
--    is the chapter owner theorem for the finite-index free-factor enlargement used in the proof
--    architecture.
-- Best owner abstraction:
-- the proposition is intrinsically about the subgroup owner `H : Subgroup F` and the lattice of
-- its overgroups. The finite-index conclusion belongs directly at that owner level; free-factor
-- enlargements and basis choices are derived proof input, not primitive public data.
-- Primitive vs. derived:
-- the primitive public data are exactly `H` and the source-faithful overgroup condition that
-- every `K` with `H ≤ K` is finitely generated. The source phrase “`H` is finitely generated” is
-- derived already by taking `K = H`, so it should not remain as a redundant public binder. Any
-- free-basis witness for a subgroup, any complementary factor in a Hall overgroup, and any
-- infinite-rank basis extracted from a counterexample are all derived bridge data and should
-- remain internal to the proof.
-- Proof sketch: first derive `H.FG` by applying `hover` to the tautological overgroup `H ≤ H`.
-- Proposition `1-3-11` with `A = ∅` then gives a finite-index overgroup `G` of `H` in which
-- `H` is a free factor. A proper Hall free-factor enlargement of `H` inside `G` would yield an
-- overgroup of `H` that is not finitely generated, contradicting `hover`. Hence that enlargement
-- is trivial, so `H = G` and therefore `H` has finite index.
theorem finiteIndex_of_all_overgroups_fg (H : Subgroup F)
    (hover : ∀ ⦃K : Subgroup F⦄, H ≤ K → K.FG) :
    H.FiniteIndex := by
  have hfg : H.FG := hover le_rfl
  sorry

end
