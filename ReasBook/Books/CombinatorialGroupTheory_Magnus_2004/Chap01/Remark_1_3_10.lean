/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_9

-- Declarations for this item will be appended below by the statement pipeline.

-- Layer triage:
-- `source-facing`: the forward-looking textbook remark that interprets Schreier's rank-index
-- formula geometrically and relates it to the Riemann-Hurwitz formula.
-- `core/canonical`: the preceding chapter theorem `finiteIndex_subgroup_rank_sub_one_eq`, whose
-- owner invariants are `Group.rank` and `Subgroup.index`.
-- `bridge/view`: this file contributes only prose context around that theorem, so the canonical
-- refinement is a direct recall rather than a parallel local restatement.
-- Domain sampling:
-- 1. `Group.rank` in `Mathlib/GroupTheory/Rank` is the owner invariant for finite generator rank.
-- 2. `Subgroup.index` in `Mathlib/GroupTheory/Index` is the owner invariant for subgroup index.
-- 3. `Subgroup.rank_le_index_mul_rank` in `Mathlib/GroupTheory/Schreier` is the upstream
--    Schreier inequality on the same owner abstractions.
-- 4. `finiteIndex_subgroup_rank_sub_one_eq` in Proposition `1-3-9` is already the exact
--    source-faithful chapter theorem recalled by this remark.
-- Primitive vs. derived:
-- this remark introduces no new primitive mathematical data; the only relevant public content is
-- the previously established theorem itself.

/- Remark 1-3-10: the Schreier rank-index formula from the preceding proposition has a geometric
interpretation, and this interpretation is closely related to the Riemann-Hurwitz formula.

This source item is a forward-looking prose remark rather than a standalone theorem. To keep the
formalization source-faithful without inventing a surrogate proposition, the file keeps only a
direct recall of the preceding chapter theorem that already states Schreier's rank-index formula
in the canonical owner variables `Group.rank` and `Subgroup.index`. -/
#check finiteIndex_subgroup_rank_sub_one_eq
