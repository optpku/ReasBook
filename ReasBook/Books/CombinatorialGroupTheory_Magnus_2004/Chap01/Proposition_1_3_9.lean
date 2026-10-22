/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

/-- Proposition 1-3-9: a finite-index subgroup `H` of a finite-rank free group `F` satisfies the
exact Schreier rank-index formula
`Group.rank H - 1 = H.index * (Group.rank F - 1)`. -/
-- Layer triage:
-- `source-facing`: Schreier's rank formula for a specific finite-index subgroup `H ≤ F`.
-- `core/canonical`: `Group.rank` and `Subgroup.index`.
-- `bridge/view`: the ambient assumptions `[IsFreeGroup F] [Group.FG F]` encode the source phrase
-- “finite-rank free group”, while freeness and finite generation of `H` are derived through
-- owner instances rather than stored as primitive data.
-- Domain sampling:
-- 1. `Group.rank` in `Mathlib/GroupTheory/Rank` is the owner invariant for finite generator rank.
-- 2. `Subgroup.rank_le_index_mul_rank` in `Mathlib/GroupTheory/Schreier` is the general
--    finite-index Schreier inequality.
-- 3. `subgroupIsFreeOfIsFree` in
--    `Mathlib/GroupTheory/FreeGroup/NielsenSchreier` is the owner theorem giving freeness of `H`.
-- 4. `Subgroup.fg_of_index_ne_zero` in `Mathlib/GroupTheory/Schreier` is the owner instance
--    deriving `[Group.FG H]` from `[Group.FG F] [H.FiniteIndex]`.
-- Best owner abstraction: the proposition should be stated directly in terms of the intrinsic pair
-- `Group.rank` and `Subgroup.index`, not via a chosen Schreier basis or a separate finite-rank
-- wrapper for `H`.
-- Primitive vs. derived:
-- the primitive public data are only the subgroup `H : Subgroup F` and the finite-index instance
-- `[H.FiniteIndex]`; freeness and finite generation of `H` are derived API coming from the owner
-- abstractions above.
theorem finiteIndex_subgroup_rank_sub_one_eq (H : Subgroup F) [H.FiniteIndex] :
    Group.rank H - 1 = H.index * (Group.rank F - 1) := sorry

end
