/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_9
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_5
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_5

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

variable {F : Type u} [Group F] [IsFreeGroup F]

-- Primary domain: automorphisms of a rank-two free group and the induced action on its
-- abelianization.
-- Domain sampling:
-- 1. `MulAut F` is the canonical owner abstraction for `Aut(F)`.
-- 2. `MulAut.abelianization F` from Proposition `1-4-5` is the owner map to the automorphism
--    group of the abelianization.
-- 3. `MulAut.IA F` and `MulAut.innerAutomorphismSubgroup F` are the chapter owner subgroups for
--    the kernel and the inner automorphisms.
-- 4. `Group.rank` from `Mathlib/GroupTheory/Rank` is the intrinsic chapter owner for the source
--    phrase “free group of rank `2`”, while `FreeGroupBasis (Fin 2) F` is only auxiliary proof
--    data used to compare the abelianization with `GL (Fin 2) ℤ`.
-- Layer triage:
-- `source-facing`: the intrinsic rank-two hypothesis `Group.rank F = 2` and the textbook
-- statement that the kernel of the abelianization action equals the subgroup of inner
-- automorphisms.
-- `core/canonical`: `MulAut.abelianization F`, `MulAut.IA F`,
-- `MulAut.innerAutomorphismSubgroup F`, and the owner invariant `Group.rank`.
-- `bridge/view`: a chosen basis `basis : FreeGroupBasis (Fin 2) F` is internal bridge data used
-- to identify the abelianization with the free abelian group on `Fin 2`.
-- Primitive vs. derived:
-- the source-facing primitive datum is the rank hypothesis `Group.rank F = 2`; any chosen
-- `FreeGroupBasis (Fin 2) F` realizing that rank is derived bridge data and should not appear in
-- the public API.

/-- Core/canonical rank-two form of Proposition 1-4-6, expressed relative to a chosen basis so the
abelianization action can later be identified with `GL (Fin 2) ℤ`. -/
-- Proof sketch: use `basis` to identify `Abelianization F` with the free abelian group on
-- `Fin 2`. Proposition `1-4-5` gives surjectivity of `MulAut.abelianization F`, and Nielsen's
-- rank-two computation shows that its kernel is exactly the subgroup of inner automorphisms.
private theorem ia_eq_inner_of_basis (basis : FreeGroupBasis (Fin 2) F) :
    MulAut.IA F = MulAut.innerAutomorphismSubgroup F := sorry

section

variable [Group.FG F]

private theorem rank_freeGroup_eq_nat_card (α : Type u) [Finite α] :
    Group.rank (FreeGroup α) = Nat.card α := by
  letI : Fintype α := Fintype.ofFinite α
  letI : DecidableEq α := Classical.decEq α
  letI : DecidableEq (FreeGroup α) := Classical.decEq _
  let basis : FreeGroupBasis α (FreeGroup α) := .ofFreeGroup α
  have hle : Group.rank (FreeGroup α) ≤ Fintype.card α := by
    calc
      Group.rank (FreeGroup α) ≤ (Finset.univ.image basis).card :=
        Group.rank_le <| by
          have hset :
              ((Finset.univ.image basis : Finset (FreeGroup α)) : Set (FreeGroup α)) =
                Set.range basis := by
            ext x
            simp
          have hrange : Set.range basis = Set.range (FreeGroup.of : α → FreeGroup α) := by
            ext x
            simp [basis]
          rw [hset]
          rw [hrange]
          exact FreeGroup.closure_range_of α
      _ = Fintype.card α := by
        rw [Finset.card_image_of_injOn]
        · simp
        · exact basis.injective.injOn
  have hge : Fintype.card α ≤ Group.rank (FreeGroup α) := by
    obtain ⟨S, hS, hgenS⟩ := Group.rank_spec (FreeGroup α)
    exact hS ▸ fintype_card_le_card_of_generating_finset basis S hgenS
  rw [Nat.card_eq_fintype_card]
  exact le_antisymm hle hge

private theorem rank_eq_nat_card_generators :
    Group.rank F = Nat.card (IsFreeGroup.Generators F) := by
  letI : Finite (IsFreeGroup.Generators F) := IsFreeGroup.finite_generators F
  calc
    Group.rank F = Group.rank (FreeGroup (IsFreeGroup.Generators F)) := by
      simpa using Group.rank_congr (IsFreeGroup.toFreeGroup F)
    _ = Nat.card (IsFreeGroup.Generators F) := rank_freeGroup_eq_nat_card (IsFreeGroup.Generators F)

/-- A rank-two finitely generated free group admits a basis indexed by `Fin 2`. This bridge
converts the intrinsic rank statement `Group.rank F = 2` into the basis owner used by the
chapter's basis-dependent automorphism results. -/
theorem exists_basis_fin_two_of_rank_eq_two (h_rank : Group.rank F = 2) :
    Nonempty (FreeGroupBasis (Fin 2) F) := by
  letI : Finite (IsFreeGroup.Generators F) := IsFreeGroup.finite_generators F
  have hcard : Group.rank F = Nat.card (IsFreeGroup.Generators F) :=
    rank_eq_nat_card_generators
  exact ⟨(IsFreeGroup.basis F).reindex <| Finite.equivFinOfCardEq <| hcard.symm.trans h_rank⟩

/-- Proposition 1-4-6: if `F` is a free group of rank `2`, then the kernel of the natural map
from `Aut(F)` to the automorphism group of its abelianization is the subgroup of inner
automorphisms. Via a basis of `Abelianization F`, the target identifies with `GL(2, ℤ)`. -/
-- Proof sketch: convert the intrinsic rank hypothesis `Group.rank F = 2` to a private chosen
-- basis `FreeGroupBasis (Fin 2) F`, then apply the private bridge theorem
-- `ia_eq_inner_of_basis`.
theorem ia_eq_inner_of_rank_eq_two (h_rank : Group.rank F = 2) :
    MulAut.IA F = MulAut.innerAutomorphismSubgroup F := by
  rcases exists_basis_fin_two_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using ia_eq_inner_of_basis basis

end

end
