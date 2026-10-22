/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F] [Group.FG F]

/-- Proposition 1-3-17: if `H` is a finite-index subgroup of a free group `F` of rank greater
than `1`, then any overgroup `G` of `H` with rank at least that of `H` must already equal `H`. -/
-- Layer triage:
-- `source-facing`: rigidity of a finite-index free subgroup against proper overgroups of equal or
-- greater rank.
-- `core/canonical`: `Group.rank`, `Subgroup.index_strictAnti`, and the chapter's canonical
-- Schreier-formula theorem `finiteIndex_subgroup_rank_sub_one_eq`.
-- `bridge/view`: the textbook comparison “rank of the overgroup versus rank of the subgroup” is
-- expressed directly by the owner invariant `Group.rank`, while finiteness of `G.index` is derived
-- from `H ≤ G` and `[H.FiniteIndex]`.
-- Domain sampling:
-- 1. `Subgroup.index_strictAnti` in `Mathlib/GroupTheory/Index` is the owner monotonicity theorem
--    for proper inclusions of finite-index subgroups.
-- 2. `Subgroup.finiteIndex_of_le` in `Mathlib/GroupTheory/Index` is the owner bridge turning the
--    overgroup relation `H ≤ G` into the derived finite-index instance on `G`.
-- 3. `finiteIndex_subgroup_rank_sub_one_eq` in `Proposition_1_3_9` is the chapter owner theorem
--    converting subgroup index inequalities into rank inequalities in finite-rank free groups.
-- Primitive vs. derived:
-- the primitive public inputs are the subgroups `H`, `G`, the finite-index hypothesis on `H`, the
-- inclusion `H ≤ G`, and the rank comparison; the finite-index structure on `G` is derived API.
-- Proof sketch: if `H < G`, then `G` also has finite index and `Subgroup.index_strictAnti` gives
-- `G.index < H.index`. Multiplying by the positive factor `Group.rank F - 1` preserves the strict
-- inequality, and Schreier's formula rewrites it as `Group.rank G - 1 < Group.rank H - 1`. This
-- contradicts the assumed inequality `Group.rank H ≤ Group.rank G`.
theorem eq_of_le_of_rank_ge_of_finiteIndex_subgroup (hF_rank : 1 < Group.rank F)
    {H G : Subgroup F} [H.FiniteIndex] (hHG : H ≤ G) [Group.FG G]
    (h_rank : Group.rank H ≤ Group.rank G) : G = H := by
  haveI : G.FiniteIndex := Subgroup.finiteIndex_of_le hHG
  by_contra hGH
  have hlt : H < G := lt_of_le_of_ne hHG (fun h ↦ hGH h.symm)
  have hrank_sub : Group.rank G - 1 < Group.rank H - 1 := by
    simpa [finiteIndex_subgroup_rank_sub_one_eq G, finiteIndex_subgroup_rank_sub_one_eq H] using
      Nat.mul_lt_mul_of_pos_right (Subgroup.index_strictAnti hlt) (Nat.sub_pos_of_lt hF_rank)
  omega

end
