/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_25

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group with all of its subgroups, together with the trichotomy
-- that each subgroup either contains a free subgroup of rank `2`, or else lies in the solvable /
-- cyclic / infinite-dihedral exceptional families.
-- `core/canonical`: `PresentedGroup (Set.singleton r)` for one-relator groups,
-- `Subgroup` for subgroup owners, the direct existential
-- `∃ K : Subgroup Q, K ≤ H ∧ Nonempty (K ≃* FreeGroup (Fin 2))` for the rank-two free branch,
-- `IsSolvable`, `IsCyclic`, and `DihedralGroup 0` for the exceptional subgroup types.
-- `bridge/view`: no extra public bridge is needed; the source phrase “contains a free subgroup of
-- rank `2`” is already expressed directly at the subgroup owner level.
--
-- Domain sampling / owner abstraction:
-- 1. `PresentedGroup (Set.singleton r)` is the established project owner for one-relator
--    groups in this chapter.
-- 2. `FreeGroup (Fin 2)` is the canonical owner for the free group of rank `2`, while any
--    `FreeGroupBasis (Fin 2) K` is only bridge data exhibiting a concrete basis.
-- 3. `IsSolvable` and `IsCyclic` are mathlib's owner predicates for the solvable and cyclic
--    alternatives.
-- 4. `DihedralGroup 0` is mathlib's canonical infinite dihedral group.
--
-- Primitive vs. derived:
-- the public primitive data are the relator `r`, a subgroup `H` of the one-relator quotient, and
-- in the torsion case a nontrivial finite-order element of the ambient quotient. The subgroup
-- alternatives are derived conclusions, so the free rank-two branch is stated directly rather than
-- through a parallel predicate.

variable {X : Type u}
variable (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)

/-- Proposition 2-5-26 (1): every subgroup of a one-relator group either contains a free subgroup
of rank `2` or is solvable. -/
-- Proof sketch: this is the standard subgroup theorem for one-relator groups. Apply the
-- Freiheitssatz / JSJ-style analysis of subgroups of one-relator groups: a non-solvable subgroup
-- must contain a nonabelian free subgroup, and in the one-relator setting this can be chosen of
-- rank `2`; otherwise the subgroup lies in the solvable exceptional case.
theorem subgroup_of_oneRelator_contains_rankTwoFree_or_isSolvable
    (H : Subgroup Q) :
    (∃ K : Subgroup Q, K ≤ H ∧ Nonempty (K ≃* FreeGroup (Fin 2))) ∨ IsSolvable H := sorry

/-- Proposition 2-5-26 (2): if a one-relator group has a nontrivial finite-order element, then
every subgroup either contains a free subgroup of rank `2`, is cyclic, or is infinite dihedral. -/
-- Proof sketch: first apply clause `(1)`. If `H` already contains a free subgroup of rank `2`,
-- there is nothing to prove. Otherwise `H` is solvable, and Proposition `2-5-25 (2)` classifies
-- solvable subgroups of a torsion one-relator group as cyclic or infinite dihedral.
theorem subgroup_of_torsion_oneRelator_contains_rankTwoFree_or_isCyclic_or_isInfiniteDihedral
    (htorsion : ∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g)
    (H : Subgroup Q) :
    (∃ K : Subgroup Q, K ≤ H ∧ Nonempty (K ≃* FreeGroup (Fin 2))) ∨
      IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0) := by
  rcases subgroup_of_oneRelator_contains_rankTwoFree_or_isSolvable r H with hfree | hsolv
  · exact Or.inl hfree
  · exact Or.inr <|
      solvable_subgroup_of_one_relator_group_with_torsion_classification r htorsion H hsolv

end
