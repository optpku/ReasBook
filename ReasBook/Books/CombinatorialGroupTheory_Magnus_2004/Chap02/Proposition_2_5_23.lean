/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped commutatorElement

universe u v

noncomputable section

section

variable {X : Type u}

local notation "RankTwoFreeAbelian" => Multiplicative (FreeAbelianGroup (Fin 2))

-- Layer triage:
-- `source-facing`: the one-relator group `PresentedGroup ({r} : Set (FreeGroup X))` and the
-- hypothesis that it is abelian.
-- `core/canonical`: `PresentedGroup ({r} : Set (FreeGroup X))`, `IsMulCommutative`, `IsCyclic`,
-- `RankTwoFreeAbelian`, and the chapter's canonical generator-cardinality layer `Cardinal.mk X`.
-- `bridge/view`: only part (2) needs a chosen basis `basis : FreeGroupBasis X F` of an ambient
-- free group `F`, because the source there compares the abstract relator in `F` with the
-- canonical rank-two normal forms `b` and `⁅a, b⁆`.
--
-- Domain sampling:
-- 1. `PresentedGroup ({w} : Set (FreeGroup X))` is the chapter's canonical owner for the
--    one-relator quotient with defining relator `w`.
-- 2. `center_eq_bot_of_oneRelator_card_ge_three` from Proposition `2-5-21` is the preceding
--    owner-side obstruction behind part (1).
-- 3. `abelian_subgroup_of_one_relator_group_classification` from Proposition `2-5-25` is the
--    later owner-side classification result living at the same one-relator owner level as part
--    (3).
-- 4. `Cardinal.mk X` is the chapter's owner abstraction for generator cardinality, already used in
--    Proposition `2-5-21`.
-- 5. `IsMulCommutative`, `IsCyclic`, and `RankTwoFreeAbelian` give the library-facing
--    formulations of the textbook abelianity hypothesis and the alternatives
--    “cyclic” and “free abelian of rank `2`”.
--
-- Primitive vs. derived:
-- for parts (1) and (3), the primitive public data are only the relator `r : FreeGroup X` and
-- the abelianity assumption on the corresponding one-relator quotient. Part (2) additionally uses
-- a chosen basis `basis : FreeGroupBasis X F` to compare an abstract relator in an ambient free
-- group with the canonical rank-two model.

/-- Proposition 2-5-23 (1): if the one-relator quotient defined by the relator `r` is abelian,
then `X` has at most two generators. -/
-- Proof sketch: combine the previous proposition on centers of one-relator groups with the fact
-- that an abelian group is equal to its center. A one-relator quotient with at least three
-- generators would then have trivial center, contradicting abelianity unless the number of
-- generators is at most `2`.
theorem card_le_two_of_abelian_presentedGroup
    (r : FreeGroup X)
    (hab : IsMulCommutative (PresentedGroup ({r} : Set (FreeGroup X)))) :
    Cardinal.mk X ≤ 2 := sorry

/-- Proposition 2-5-23 (3): an abelian one-relator quotient is either cyclic or free abelian of
rank `2`. -/
-- Proof sketch: first apply the cardinal bound to reduce to the cases of one or two generators.
-- In rank one, the quotient is cyclic. In rank two, the basis-dependent normal-form theorem below
-- reduces the relator to either a basis element, giving a cyclic quotient, or the commutator,
-- giving `RankTwoFreeAbelian`.
theorem presentedGroup_isCyclic_or_freeAbelian_rank_two_of_abelian
    (r : FreeGroup X)
    (hab : IsMulCommutative (PresentedGroup ({r} : Set (FreeGroup X)))) :
    IsCyclic (PresentedGroup ({r} : Set (FreeGroup X))) ∨
      Nonempty (PresentedGroup ({r} : Set (FreeGroup X)) ≃* RankTwoFreeAbelian) := sorry

end

section

variable {X : Type u}
variable {F : Type v} [Group F]
variable (basis : FreeGroupBasis X F) {r : F}

local notation "rels" => ({basis.repr r} : Set (FreeGroup X))
local notation "G" => PresentedGroup rels

/-- Proposition 2-5-23 (2): if the basis has exactly two generators and the corresponding
one-relator quotient is abelian, then some rank-two basis `{a, b}` of `F` makes the relator equal
to either `b` or the commutator `⁅a, b⁆`. -/
-- Proof sketch: after a Nielsen change of basis, arrange that the exponent sum of one basis
-- element in `r` is zero. Rewrite `r` in the standard Magnus basis of the normal closure of the
-- other basis element and apply the one-relator consequences theorem used in Proposition `2-5-16`.
-- The abelianity hypothesis then forces the resulting normal form to be a basis element or the
-- basic commutator.
theorem exists_rankTwoBasis_relator_eq_basisElement_or_commutator_of_abelian_presentedGroup
    (hcard : Cardinal.mk X = 2) (hab : IsMulCommutative G) :
    ∃ basis2 : FreeGroupBasis (Fin 2) F, r = basis2 1 ∨ r = ⁅basis2 0, basis2 1⁆ := sorry

end
