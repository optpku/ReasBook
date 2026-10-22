/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Corollary 1-4-13: for a free group `F`, the quotient of `IA(F)` by its inner automorphism
subgroup is torsion free. -/
-- Layer triage:
-- `source-facing`: the IA-subgroup `MulAut.IA F` of automorphisms acting trivially on the
-- abelianization, together with the quotient by inner automorphisms.
-- `core/canonical`: `MulAut.IA F`, the inner automorphism owner subgroup
-- `MulAut.innerAutomorphismSubgroup F`, the subgroup-in-subgroup construction
-- `Subgroup.subgroupOf`, and the torsion-free predicate `IsMulTorsionFree`.
-- `bridge/view`: the textbook quotient `IA(F) / JA(F)` is rendered as the quotient of the subgroup
-- `MulAut.IA F` by the inner automorphism subgroup viewed inside it via `Subgroup.subgroupOf`.
-- Domain sampling:
-- 1. `MulAut.IA F` from Proposition `1-4-5` is the project owner abstraction for automorphisms
--    acting trivially on the abelianization.
-- 2. `MulAut.innerAutomorphismSubgroup F` is the chapter owner abstraction for the subgroup of
--    inner automorphisms of `F`.
-- 3. `Subgroup.subgroupOf` is mathlib's owner API for viewing that subgroup inside `MulAut.IA F`.
-- 4. `IsMulTorsionFree` is the canonical torsion-free predicate on the resulting quotient group.
-- Primitive vs. derived:
-- the primitive public datum is only the ambient free group `F`; the subgroup quotient is the
-- canonical derived object attached to the IA-subgroup and the inner automorphism subgroup.
-- Proof sketch: let `q` be a finite-order element of the quotient and choose `α ∈ IA(F)`
-- representing it. Some positive power `α ^ N` lies in the inner automorphism subgroup, so
-- Proposition `1-4-12` implies that `α` itself is inner. Therefore `q` is trivial, and the
-- quotient is torsion free.
theorem ia_quotient_inner_isMulTorsionFree :
    IsMulTorsionFree
      (MulAut.IA F ⧸ (JA(F)).subgroupOf (MulAut.IA F)) :=
  sorry

end
