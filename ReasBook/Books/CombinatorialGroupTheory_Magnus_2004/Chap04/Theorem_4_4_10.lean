/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {G : Type u} [Group G] [Group.FG G] [Group.ResiduallyFinite G]

-- Layer triage:
-- `source-facing`: a finitely generated residually finite group `G` and the automorphism group
-- `Aut(G)`.
-- `core/canonical`: `Group.FG G`, `Group.ResiduallyFinite G`, `FiniteIndexNormalSubgroup`, and
-- `MulAut G`.
-- `bridge/view`: the textbook notation `Aut(G)` is the canonical multiplicative automorphism group
-- `MulAut G`; residual finiteness is stated directly via the mathlib class on that owner.
-- Domain sampling:
-- 1. `Group.ResiduallyFinite` is mathlib's owner predicate for residual finiteness.
-- 2. `Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup` is the owner-level separation
--    criterion for residual finiteness.
-- 3. `Subgroup.exists_characteristic_le_of_finiteIndex` from Theorem `4-4-9` is the chapter's
--    canonical bridge from an arbitrary finite-index subgroup to a characteristic one.
-- 4. `MulAut G` is the canonical group of automorphisms of `G`.
--
-- Primitive vs. derived:
-- the primitive public content is only the owner instance
-- `Group.ResiduallyFinite (MulAut G)`. The separating finite-index normal subgroup of `MulAut G`
-- used in the textbook argument is derived owner-level data, so it should not be promoted to a
-- separate wrapper or existentially chosen public definition.

-- Proof sketch: for a nontrivial automorphism `α`, choose `c : G` moved by `α`, so
-- `α c * c⁻¹ ≠ 1`. By
-- `Group.residuallyFinite_iff_exists_finiteIndexNormalSubgroup`, choose a finite-index normal
-- subgroup of `G` missing that element, then apply Theorem `4-4-9` to refine it to a
-- characteristic finite-index subgroup `K`. Every automorphism of `G` then descends to `G ⧸ K`,
-- yielding a homomorphism `MulAut G →* MulAut (G ⧸ K)` into a finite group that does not kill
-- `α`.
/-- Theorem 4-4-10: if `G` is finitely generated and residually finite, then its automorphism
group `Aut(G)` is residually finite. -/
instance residuallyFinite_mulAut_of_fg_residuallyFinite :
    Group.ResiduallyFinite (MulAut G) where
  iInf_eq_bot := sorry

end
