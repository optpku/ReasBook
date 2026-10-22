/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_9
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {F : Type u} [Group F] [IsFreeGroup F]

-- Primary domain: finite-order automorphisms and their conjugacy classes in a rank-two free group.
-- Domain sampling:
-- 1. `MulAut F` is the canonical owner abstraction for `Aut(F)`.
-- 2. `IsOfFinOrder α` is mathlib's owner predicate for finite-order automorphisms.
-- 3. `ConjClasses (MulAut F)` together with `ConjClasses.mk` is the owner abstraction for
--    conjugacy classes in `Aut(F)`.
-- 4. `Group.rank` is the intrinsic owner for the source phrase “rank-two free group”, while
--    `FreeGroupBasis (Fin 2) F` with `basis.toGL : MulAut F →* GL (Fin 2) ℤ` is auxiliary proof
--    data used internally for the matrix classification.
-- Layer triage:
-- `source-facing`: finite-order elements of `Aut(F)` and their conjugacy classes in a free group
-- of intrinsic rank `2`.
-- `core/canonical`: `FreeGroupBasis (Fin 2) F`, `Group.rank`, `MulAut F`, `IsOfFinOrder`,
-- `orderOf`, `ConjClasses (MulAut F)`, and `ConjClasses.mk`.
-- `bridge/view`: a chosen basis `basis : FreeGroupBasis (Fin 2) F` obtained from
-- `exists_basis_fin_two_of_rank_eq_two h_rank` is internal bridge data used to pass to
-- `basis.toGL`; the basis-relative classification lemmas below stay private because the public
-- textbook content is the intrinsic rank-two statement.

/-- Private basis-relative bridge for Proposition 1-4-7. -/
-- Proof sketch: transport the automorphism through `basis.toGL`, classify finite-order elements in
-- `GL (Fin 2) ℤ`, and use `basis.orderOf_toGL_eq` from Corollary `1-4-16` to bring the
-- order statement back to `MulAut F`.
private theorem orderOf_eq_one_or_two_or_three_or_four_of_finite_order_basis
    (basis : FreeGroupBasis (Fin 2) F)
    {α : MulAut F} (hα : IsOfFinOrder α) :
    orderOf α = 1 ∨ orderOf α = 2 ∨ orderOf α = 3 ∨ orderOf α = 4 := sorry

/-- Private basis-relative involution count bridge for Proposition 1-4-7. -/
-- Proof sketch: classify involutions in `GL (Fin 2) ℤ` up to conjugacy, then use the basis bridge
-- to lift those classes back to `Aut(F)`.
private theorem orderTwo_conjClasses_encard_basis (basis : FreeGroupBasis (Fin 2) F) :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 2 }).encard = 4 := sorry

/-- Private basis-relative order-`3` conjugacy-class count bridge for Proposition 1-4-7. -/
-- Proof sketch: classify order-`3` matrices in `GL (Fin 2) ℤ`, then transport the unique
-- conjugacy class back through `basis.toGL`.
private theorem orderThree_conjClasses_encard_basis (basis : FreeGroupBasis (Fin 2) F) :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 3 }).encard = 1 := sorry

/-- Private basis-relative order-`4` conjugacy-class count bridge for Proposition 1-4-7. -/
-- Proof sketch: as in the order-`3` case, classify order-`4` matrices in `GL (Fin 2) ℤ` and
-- transport the unique conjugacy class back through `basis.toGL`.
private theorem orderFour_conjClasses_encard_basis (basis : FreeGroupBasis (Fin 2) F) :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 4 }).encard = 1 := sorry

section

variable [Group.FG F]

variable (h_rank : Group.rank F = 2)

include h_rank

/-- Proposition 1-4-7: in the automorphism group of a rank-two free group, every finite-order
automorphism has order `1`, `2`, `3`, or `4`. -/
-- Proof sketch: use `exists_basis_fin_two_of_rank_eq_two` to obtain a basis
-- `FreeGroupBasis (Fin 2) F`, then apply the basis-dependent owner theorem above. Its proof uses
-- the canonical bridge `basis.toGL` from Corollary `1-4-16`.
theorem orderOf_eq_one_or_two_or_three_or_four_of_finite_order
    {α : MulAut F} (hα : IsOfFinOrder α) :
    orderOf α = 1 ∨ orderOf α = 2 ∨ orderOf α = 3 ∨ orderOf α = 4 := by
  rcases exists_basis_fin_two_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderOf_eq_one_or_two_or_three_or_four_of_finite_order_basis basis hα

/-- The conjugacy classes in `Aut(F)` represented by involutions of a rank-two free group form a
four-element set. -/
-- Proof sketch: use `exists_basis_fin_two_of_rank_eq_two` and then apply the
-- basis-dependent count theorem, whose proof uses the canonical bridge `basis.toGL`.
theorem orderTwo_conjClasses_encard :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 2 }).encard = 4 := by
  rcases exists_basis_fin_two_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderTwo_conjClasses_encard_basis basis

/-- The conjugacy classes in `Aut(F)` represented by elements of order `3` in a rank-two free
group form a singleton. -/
-- Proof sketch: use `exists_basis_fin_two_of_rank_eq_two` and then apply the
-- basis-dependent count theorem, whose proof uses the canonical bridge `basis.toGL`.
theorem orderThree_conjClasses_encard :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 3 }).encard = 1 := by
  rcases exists_basis_fin_two_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderThree_conjClasses_encard_basis basis

/-- The conjugacy classes in `Aut(F)` represented by elements of order `4` in a rank-two free
group form a singleton. -/
-- Proof sketch: use `exists_basis_fin_two_of_rank_eq_two` and then apply the
-- basis-dependent count theorem, whose proof uses the canonical bridge `basis.toGL`.
theorem orderFour_conjClasses_encard :
    (ConjClasses.mk '' { α : MulAut F | orderOf α = 4 }).encard = 1 := by
  rcases exists_basis_fin_two_of_rank_eq_two h_rank with ⟨basis⟩
  simpa using orderFour_conjClasses_encard_basis basis

omit h_rank

end

end
