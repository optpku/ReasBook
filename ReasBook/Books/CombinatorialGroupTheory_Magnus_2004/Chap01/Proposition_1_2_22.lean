/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_2_21

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {F : Type u} [Group F] [IsFreeGroup F]

/-- Proposition 1-2-22 (2): given two elements of a free group, it is decidable whether they
commute. -/
-- Layer: source-facing decidability statement for the owner relation `Commute`.
-- `core/canonical`: the relation `Commute`.
-- `bridge/view`: equip the chosen generators with decidable equality, transport `DecidableEq`
-- from the canonical free group along `IsFreeGroup.toFreeGroup`, then use `commute_iff_eq`.
noncomputable instance decidableCommuteOfIsFreeGroup : DecidableRel (Commute : F → F → Prop) :=
  by
    let _ : DecidableEq (IsFreeGroup.Generators F) := Classical.decEq _
    let _ : DecidableEq F := (IsFreeGroup.toFreeGroup F).injective.decidableEq
    intro x y
    exact decidable_of_iff (x * y = y * x) (commute_iff_eq x y).symm

/-- Proposition 1-2-22 (1): given two elements of a free group, it is decidable whether they are
powers of a common element. -/
-- Layer: source-facing textbook decidability statement.
-- `core/canonical`: the owner relation `Commute`.
-- `bridge/view`: the equivalence
-- `commute_iff_exists_common_zpowers_generator`.
noncomputable def common_zpowers_generator_decidable (x y : F) :
    Decidable (∃ z : F, x ∈ Subgroup.zpowers z ∧ y ∈ Subgroup.zpowers z) :=
  decidable_of_iff
    (Commute x y)
    (commute_iff_exists_common_zpowers_generator x y)

end
