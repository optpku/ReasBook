/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `PresentedGroup ({r} : Set (FreeGroup X))` together with an
-- abelian subgroup or, in the torsion clause, a solvable subgroup.
-- `core/canonical`: `PresentedGroup` for the ambient one-relator group, `Subgroup.FG` and
-- `IsCyclic` for local cyclicity, `Multiplicative (FreeAbelianGroup (Fin 2))` for the free
-- abelian rank-two alternative, the explicit predicate `IsMulCommutative H` for the subgroup
-- abelianity hypothesis, `IsSolvable` for the solvable-subgroup hypothesis, and `DihedralGroup 0`
-- for the infinite dihedral group.
-- `bridge/view`: the textbook phrase “locally cyclic” is rendered directly as “every finitely
-- generated subgroup is cyclic”, while “with torsion” is rendered by the existence of a
-- nontrivial finite-order element in the ambient one-relator quotient.
-- Domain sampling:
-- 1. Nearby Chapter II items already use `PresentedGroup ({r} : Set (FreeGroup X))` as the
--    canonical owner for one-relator groups.
-- 2. `Subgroup.FG` and `IsCyclic` are mathlib's standard finite-generation and cyclicity
--    predicates for subgroup types.
-- 3. Nearby Proposition `2-5-23` records the “free abelian of rank `2`” alternative directly as
--    `Nonempty (H ≃* Multiplicative (FreeAbelianGroup (Fin 2)))`, so that is the best candidate
--    owner abstraction here as well.
-- 4. `IsMulCommutative H` is mathlib's canonical owner predicate for saying that the subgroup
--    `H` is abelian without introducing subgroup-specific instance plumbing.
-- 5. Nearby Proposition `2-5-24` is the chapter's owner theorem for one-relator subgroups
--    satisfying a nontrivial law, so the torsion/solvable clause here should specialize that
--    theorem rather than restate a parallel classification owner.
-- Primitive vs. derived:
-- the primitive public data are the relator `r`, the chosen subgroup `H`, and the abelian or
-- solvable hypotheses on `H`; the classification alternatives are derived conclusions, so no new
-- wrapper structure for one-relator groups or for the classification is introduced, and the
-- rank-two free-abelian branch is stated directly in the chapter's canonical owner form.

variable {X : Type u} (r : FreeGroup X)

local notation "Q" => PresentedGroup (Set.singleton r)
local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

/-- Proposition 2-5-25 (1): if `H` is an abelian subgroup of a one-relator group, then either
every finitely generated subgroup of `H` is cyclic and each nontrivial element of `H` is a `p`th
power for only finitely many primes `p`, or `H` is free abelian of rank `2`. -/
-- Proof sketch: apply the classical classification of abelian subgroups of one-relator groups.
-- The non-free-abelian case is precisely the locally cyclic alternative together with the finite
-- prime-root condition, while the remaining possibility is that the subgroup is the canonical
-- rank-two free abelian group from Proposition `2-5-23`.
theorem abelian_subgroup_of_one_relator_group_classification
    (H : Subgroup Q) (hab : IsMulCommutative H) :
    ((∀ K : Subgroup H, K.FG → IsCyclic K) ∧
        (∀ g : H, g ≠ 1 →
          Set.Finite {p : ℕ | Nat.Prime p ∧ ∃ x : H, x ^ p = g})) ∨
      Nonempty (H ≃* RankTwoFreeAbelian) := sorry

/-- Proposition 2-5-25 (2): if a one-relator group has torsion, then every solvable subgroup is
either cyclic or infinite dihedral. -/
-- Proof sketch: use the one-relator-with-torsion structure theorem for solvable subgroups. The
-- torsion hypothesis rules out the torsion-free branches that occur in the general classification,
-- leaving only the cyclic case and the subgroup type isomorphic to the infinite dihedral group.
theorem solvable_subgroup_of_one_relator_group_with_torsion_classification
    (htorsion : ∃ g : Q, g ≠ 1 ∧ IsOfFinOrder g) (H : Subgroup Q)
    (hsolv : IsSolvable H) :
    IsCyclic H ∨ Nonempty (H ≃* DihedralGroup 0) := by
  let _ : IsSolvable H := hsolv
  exact
    (subgroup_with_nontrivial_law_classification_in_one_relator_group r H
      (SatisfiesNontrivialLaw.of_isSolvable H)).2 htorsion

end
