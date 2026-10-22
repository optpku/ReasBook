/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {F : Type u} [Group F]
variable [IsFreeGroup F]

/-- Proposition 1-3-1: a free group of rank greater than `1` contains a subgroup that is not
finitely generated, equivalently a free subgroup of infinite rank. -/
-- Layer triage:
-- `source-facing`: existence of a subgroup of infinite rank inside a free group of rank `> 1`.
-- `core/canonical`: the subgroup owner `H : Subgroup F`, its finite-generation predicate `H.FG`,
-- and the chosen generator type `IsFreeGroup.Generators F`.
-- `bridge/view`: for free groups, "infinite rank" is expressed here by failure of finite
-- generation of the subgroup owner, since every subgroup of a free group is itself free.
-- Domain sampling:
-- 1. `Subgroup.FG` from `Mathlib/GroupTheory/Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `subgroupIsFreeOfIsFree` from `Mathlib/GroupTheory/FreeGroup/NielsenSchreier` is the
--    canonical owner theorem saying that subgroups of free groups are free.
-- 3. `FreeGroupBasis ι G` from `Mathlib/GroupTheory/FreeGroup/IsFreeGroup` is the canonical owner
--    for an explicit free basis of a group.
-- 4. `IsFreeGroup.basis F` is the ambient chosen-basis owner used to read the source hypothesis
--    "rank greater than `1`" as the explicit input
--    `hRank : Nontrivial (IsFreeGroup.Generators F)` without introducing a parallel local rank
--    wrapper.
-- Primitive vs. derived:
-- the primitive public data are only the ambient free group `F` and the subgroup owner
-- `H : Subgroup F`; the infinite-basis formulation is derived bridge API, not primitive data.
-- Proof sketch: choose distinct free generators `x` and `y` of `F`. The conjugates
-- `y ^ (-n) * x * y ^ n` for `n : ℤ` form a countably infinite Nielsen-reduced family, hence a
-- free basis of the subgroup they generate. A subgroup with such a basis cannot be finitely
-- generated.
theorem exists_non_fg_subgroup_of_rank_gt_one
    (hRank : Nontrivial (IsFreeGroup.Generators F)) : ∃ H : Subgroup F, ¬ H.FG := by
  let _ : Nontrivial (IsFreeGroup.Generators F) := hRank
  sorry

/-- Companion bridge for Proposition 1-3-1: under the same hypothesis, one can express the
textbook phrase "a free subgroup of infinite rank" directly through the canonical owner
`FreeGroupBasis`. -/
-- Proof sketch: apply the source-facing theorem to obtain a subgroup `H ≤ F` that is not
-- finitely generated. Nielsen-Schreier gives `IsFreeGroup H`. Choosing a basis of `H`, the
-- indexing type cannot be finite, since a finite basis would make `H` finitely generated.
theorem exists_subgroup_with_infinite_free_basis_of_rank_gt_one
    (hRank : Nontrivial (IsFreeGroup.Generators F)) :
    ∃ (H : Subgroup F) (ι : Type u), Infinite ι ∧ Nonempty (FreeGroupBasis ι H) := by
  let _ : Nontrivial (IsFreeGroup.Generators F) := hRank
  sorry
