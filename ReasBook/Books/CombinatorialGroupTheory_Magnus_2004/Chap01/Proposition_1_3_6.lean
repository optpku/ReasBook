/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Subgroup

section

variable {F : Type u} [Group F] [IsFreeGroup F]
variable (H : ℕ →o Subgroup F)

omit [IsFreeGroup F] in
private theorem group_fg_of_subgroup_fg {K : Subgroup F} (hK : K.FG) : Group.FG K :=
  (Group.fg_iff_subgroup_fg K).2 hK

/-- Proposition 1-3-6 (Takahasi): an ascending chain of free subgroups of uniformly bounded finite
rank in a free group eventually stabilizes. -/
-- Layer triage:
-- `source-facing`: an ascending chain `H : ℕ →o Subgroup F` in an ambient free group whose stages
-- have rank at most `r`.
-- `core/canonical`: the ambient owner hypothesis `[IsFreeGroup F]`, the order-hom owner for the
-- chain, the subgroup owner `Subgroup.FG`, the rank owner `Group.rank`, and equality in the
-- subgroup lattice.
-- `bridge/view`: the stabilized union `⨆ n, H n` is a derived consequence, not the main
-- source-facing statement.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib.GroupTheory.Finiteness` is the canonical owner predicate for
--    finite generation of a subgroup.
-- 2. `Group.rank` in `Mathlib.GroupTheory.Rank` is the canonical owner invariant for “generated
--    by at most `r` elements”, so bounded rank should be stated through it rather than through a
--    displayed family of finite generating sets.
-- 3. `subgroupIsFreeOfIsFree` is the canonical owner theorem deriving stagewise freeness from the
--    ambient free-group hypothesis, so `[∀ n, IsFreeGroup (H n)]` is duplicate wheel data here.
-- 4. `ℕ →o Subgroup F` is mathlib's canonical owner abstraction for an ascending subgroup chain,
--    so the monotonicity proof should be primitive data of the chain rather than a separate public
--    argument.
-- 5. `iSup_le` and `le_iSup` are the lattice owners used to pass from eventual constancy to the
--    union statement.
--
-- Primitive vs. derived:
-- the primitive public data are the ambient free group `F`, the order-hom chain `H`, the bound
-- `r`, and the owner-level bounded-rank hypotheses that each stage is finitely generated and has
-- `Group.rank` at most `r`. Stagewise freeness, a stabilizing stage, and the equality
-- `(⨆ n, H n) = H N` are derived API and should be exposed as separate companion declarations.
--
-- Proof sketch: Takahasi's argument shows that in a free group a proper inclusion between
-- finitely generated free subgroups forces the rank to increase. Since the rank of each `H n` is
-- bounded by `r`, only finitely many strict inclusions can occur, so the chain becomes constant.
theorem exists_stabilizing_index_of_bounded_rank (r : ℕ)
    (hfg : ∀ n, (H n).FG)
    (hrank :
      ∀ n,
        letI : Group.FG (H n) := group_fg_of_subgroup_fg (hfg n)
        Group.rank (H n) ≤ r) :
    ∃ N, ∀ n, N ≤ n → H n = H N := sorry

/-- Companion reformulation of Proposition `1-3-6`: once the bounded-rank ascending chain
stabilizes, its union is already one of its stages. -/
theorem exists_iSup_eq_of_bounded_rank (r : ℕ)
    (hfg : ∀ n, (H n).FG)
    (hrank :
      ∀ n,
        letI : Group.FG (H n) := group_fg_of_subgroup_fg (hfg n)
        Group.rank (H n) ≤ r) :
    ∃ N, (⨆ n, H n) = H N := by
  have hstab : ∃ N, ∀ n, N ≤ n → H n = H N :=
    exists_stabilizing_index_of_bounded_rank H r hfg hrank
  rcases hstab with ⟨N, hN⟩
  refine ⟨N, le_antisymm ?_ (le_iSup H N)⟩
  refine iSup_le fun n ↦ ?_
  by_cases hn : n ≤ N
  · exact H.monotone hn
  · exact (hN n (Nat.le_of_not_ge hn)).le

end

end Subgroup
