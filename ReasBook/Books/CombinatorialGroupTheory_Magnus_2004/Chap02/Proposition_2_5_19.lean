/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Basic
import CombinatorialGroupTheory_Magnus_2004.Chap02.Proposition_2_5_17

-- Declarations for this item will be appended below by the statement pipeline.

open scoped commutatorElement

universe u

section

-- Layer triage:
-- `source-facing`: a one-relator group `G = (X; r)` whose defining relator is the commutator
-- `r = ⁅u, v⁆` of two words in the ambient free group on `X`.
-- `core/canonical`: Proposition `2-5-17`, namely
-- `isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower`, which is the chapter's
-- owner theorem turning a non-proper-power relator into torsion-freeness of the quotient.
-- `bridge/view`: this file specializes that owner theorem to the commutator relator `⁅u, v⁆`.
-- The nontrivial commutator case is handled by the commutator-specific non-proper-power input,
-- while the trivial commutator case is reduced to the canonical quotient `PresentedGroup ({1})`,
-- which is identified with the ambient free group.
-- Domain sampling:
-- 1. `PresentedGroup R` is mathlib's owner abstraction for a group defined by generators and
--    relators.
-- 2. `⁅u, v⁆` from the commutator API is the canonical owner notation for the relator `[u, v]`.
-- 3. `isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower` from Proposition
--    `2-5-17` is the chapter's owner theorem for torsion-freeness of a one-relator quotient.
-- 4. `Subgroup.normalClosure`, `Subgroup.closure_singleton_one`, and
--    `QuotientGroup.quotientBot` are the canonical owner APIs for rewriting the trivial-relator
--    quotient to `FreeGroup X`.
-- Primitive vs. derived:
-- the primitive data are only the generator type `X` and the words `u v : FreeGroup X`; the
-- commutator relator `⁅u, v⁆`, the one-relator quotient, and its torsion-free property are all
-- derived canonically from those data together with the owner theorem from Proposition `2-5-17`
-- and the canonical identification of the trivial-relator quotient with `FreeGroup X`.

private theorem isMulTorsionFree_presentedGroup_singleton_one (X : Type u) :
    IsMulTorsionFree (PresentedGroup ({1} : Set (FreeGroup X))) :=
  by
    let e : PresentedGroup ({1} : Set (FreeGroup X)) ≃* FreeGroup X :=
      (QuotientGroup.quotientMulEquivOfEq (by
        rw [← Subgroup.normalClosure_closure_eq_normalClosure, Subgroup.closure_singleton_one,
          Subgroup.normalClosure_eq_self])).trans QuotientGroup.quotientBot
    exact Function.Injective.isMulTorsionFree e.toMonoidHom e.injective

private theorem commutatorRelator_not_properPower_of_ne_one
    {X : Type u} {u v : FreeGroup X} (hcomm : ⁅u, v⁆ ≠ 1) :
    ¬ IsProperPower (⁅u, v⁆) := by
  sorry

/-- Proposition 2-5-19: if the one-relator group `G = (X; r)` has defining relator
`r = [u, v] = ⁅u, v⁆` for some words `u` and `v`, then `G` is torsion free. -/
-- Proof sketch: apply the torsion theorem for one-relator groups. Torsion in a one-relator
-- quotient can occur only when the defining relator is a proper power in the ambient free group.
-- If `⁅u, v⁆ ≠ 1`, then the commutator relator is not a proper power, so Proposition `2-5-17`
-- applies directly. If `⁅u, v⁆ = 1`, then the presentation has the trivial relator, so the
-- quotient is canonically the free group on `X`, hence torsion free.
theorem presentedGroup_commutatorRelator_isMulTorsionFree
    {X : Type u} (u v : FreeGroup X) :
    IsMulTorsionFree (PresentedGroup ({⁅u, v⁆} : Set (FreeGroup X))) := by
  by_cases hcomm : ⁅u, v⁆ = 1
  · rw [hcomm]
    exact isMulTorsionFree_presentedGroup_singleton_one X
  · exact isMulTorsionFree_presentedGroup_singleton_of_relator_not_properPower _ <|
      commutatorRelator_not_properPower_of_ne_one hcomm

end
