/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]
variable [Group.FG F]

namespace MulAut

/-- Proposition 1-4-4: if `F` is a free group of finite rank greater than `1`, then `Aut(F)` is
complete, meaning that its center is trivial and every automorphism of `Aut(F)` is inner. -/
-- Layer triage:
-- `source-facing`: completeness of the automorphism group of a finitely generated free group of
-- rank `> 1`, expressed through the intrinsic chapter owner `Group.rank`.
-- `core/canonical`: the owner group `MulAut F`, its center `Subgroup.center (MulAut F)`, the
-- chapter owner subgroup `innerAutomorphismSubgroup (MulAut F)` of inner automorphisms of
-- `Aut(F)`, and `Group.rank`.
-- `bridge/view`: the textbook phrase “every automorphism is inner” is expressed by the owner
-- equality `innerAutomorphismSubgroup (MulAut F) = ⊤`.
-- Domain sampling:
-- 1. `innerAutomorphismSubgroup` in `Proposition_1_4_5` is the chapter owner for the subgroup
--    of inner automorphisms, already defined as the range of `MulAut.conj`.
-- 2. `MulAut.conj` in `Mathlib/Algebra/Group/End` remains the primitive canonical map behind
--    that owner subgroup.
-- 3. `Subgroup.center` in `Mathlib/GroupTheory/Subgroup/Center` is the canonical center
--    construction for a group.
-- 4. `eq_of_le_of_rank_ge_of_finiteIndex_subgroup` in `Proposition_1_3_17` shows the chapter
--    owner style for the hypothesis “rank greater than `1`”: use `1 < Group.rank F`.
-- Primitive vs. derived:
-- the primitive owner-side public content is split into the atomic statements
-- `Subgroup.center (MulAut F) = ⊥` and `innerAutomorphismSubgroup (MulAut F) = ⊤`, under
-- the intrinsic rank hypothesis `1 < Group.rank F`; the source-facing textbook completeness
-- statement is the conjunction of those two owner facts. The underlying range description in
-- terms of `MulAut.conj` is derived API and is omitted from the public surface.
-- Proof sketch: by Burnside's observation it is enough to show that the subgroup of inner
-- automorphisms of `F` is characteristic in `Aut(F)`. Dyer and Formanek prove this for finitely
-- generated free groups of rank `> 1`, from which triviality of the center and surjectivity of
-- the inner-automorphism map on `Aut(F)` follow.
theorem center_eq_bot_of_fg_and_rank_gt_one (h_rank : 1 < Group.rank F) :
    Subgroup.center (MulAut F) = ⊥ := sorry

/-- For a finitely generated free group of rank greater than `1`, every automorphism of `Aut(F)`
is inner. -/
theorem innerAutomorphismSubgroup_eq_top_of_fg_and_rank_gt_one
    (h_rank : 1 < Group.rank F) : innerAutomorphismSubgroup (MulAut F) = ⊤ := sorry

/-- Proposition 1-4-4: if `F` is a free group of finite rank greater than `1`, then `Aut(F)` is
complete, meaning that its center is trivial and every automorphism of `Aut(F)` is inner. -/
theorem complete_of_fg_and_rank_gt_one (h_rank : 1 < Group.rank F) :
    Subgroup.center (MulAut F) = ⊥ ∧ innerAutomorphismSubgroup (MulAut F) = ⊤ :=
  ⟨center_eq_bot_of_fg_and_rank_gt_one h_rank,
    innerAutomorphismSubgroup_eq_top_of_fg_and_rank_gt_one h_rank⟩

end MulAut

end
