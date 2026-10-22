/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_16

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-3-18: a finitely generated subgroup of a free group that meets every nontrivial
normal subgroup nontrivially has finite index. -/
-- Layer triage:
-- `source-facing`: a subgroup `H : Subgroup F` with the intersection property against every
-- nontrivial normal subgroup `N`.
-- `core/canonical`: Proposition 1-3-16, whose owner abstraction is the absence of infinite-rank
-- overgroups, together with `Subgroup.FG`, `Subgroup.Normal`, `Subgroup.FiniteIndex`, and the
-- lattice intersection `H ⊓ N`.
-- `bridge/view`: the textbook phrase “has non-trivial intersection with” is encoded as
-- `H ⊓ N ≠ ⊥`, and this intersection hypothesis is used only to rule out infinite-rank overgroups
-- so that Proposition 1-3-16 applies.
--
-- Domain sampling:
-- 1. `Subgroup.FG` in `Mathlib/GroupTheory/Finiteness` is the owner predicate for finite
--    generation of a subgroup.
-- 2. `Subgroup.FiniteIndex` in `Mathlib/GroupTheory/Index` is the owner predicate for finite
--    index.
-- 3. `finiteIndex_of_fg_of_contains_nontrivial_normal` in Proposition `1-3-12` is the earlier
--    chapter owner theorem for the stronger containment hypothesis `N ≤ H`.
-- 4. `finiteIndex_of_all_overgroups_fg` in Proposition `1-3-16` is the best owner
--    abstraction for the present item, because the source intersection hypothesis is used only to
--    derive the finite-generation of every overgroup of `H`.
--
-- Best owner abstraction:
-- Proposition `1-3-16` is the canonical owner theorem. The present proposition should therefore
-- stay source-facing only in its hypothesis, and translate that hypothesis to the owner condition
-- “every overgroup of `H` is finitely generated” rather than introducing a parallel wrapper API.
--
-- Primitive vs. derived:
-- the primitive source data are `H`, `hfg`, and the normal-intersection hypothesis `hinter`.
-- The overgroup finite-generation statement needed by Proposition `1-3-16` is derived bridge API,
-- so it is discharged locally inside the proof rather than exposed as a parallel local theorem.
--
-- Proof sketch: if an overgroup `K ≥ H` had infinite rank, Hall's finite-index free-factor
-- enlargement argument inside `K` would produce a nontrivial normal subgroup of `F` disjoint from
-- `H`, contradicting the hypothesis. Thus every overgroup of `H` has finite rank, and Proposition
-- 1-3-16 gives finite index.
theorem finiteIndex_of_fg_of_inf_ne_bot_with_every_nontrivial_normal (H : Subgroup F)
    (hfg : H.FG)
    (hinter :
      ∀ N : Subgroup F, N.Normal → N ≠ ⊥ → H ⊓ N ≠ ⊥) :
    H.FiniteIndex := by
  refine finiteIndex_of_all_overgroups_fg H ?_
  intro K hHK
  sorry

end
