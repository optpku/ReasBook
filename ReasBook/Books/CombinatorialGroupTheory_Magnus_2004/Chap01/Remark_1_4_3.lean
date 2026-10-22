/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_4_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open FreeGroup

noncomputable section

variable {F : Type u} [Group F] {X : Type v}

-- Layer triage:
-- `source-facing`: the contrast between the cardinalities of `Aut(F)` and the subgroup
-- `Aut_f(F)` attached to a countably infinite basis `basis : FreeGroupBasis X F`.
-- `core/canonical`: `MulAut F`, the chosen-basis owner `FreeGroupBasis X F`, and the basis-owned
-- finite-support subgroup `basis.finiteMovedSubgroup`.
-- `bridge/view`: Proposition `1-4-2` identifies `Aut_f(F)` with that owner subgroup, while
-- permutations of the basis index type transport through `basis.repr` into `MulAut F` for the
-- uncountability argument.
-- Domain sampling:
-- 1. `FreeGroupBasis X F` in `Mathlib/GroupTheory/FreeGroup/IsFreeGroup` is the owner
--    abstraction for a chosen free basis of `F`.
-- 2. `MulAut F` is the canonical automorphism group of `F`.
-- 3. `FreeGroupBasis.finiteMovedSubgroup` from Proposition `1-4-2` is the chapter owner for the
--    finite-support subgroup on a chosen basis.
-- 4. `elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup` is the source-to-owner bridge
--    identifying `Aut_f(F)` with that finite-support subgroup, and `basis.repr` together with
--    `freeGroupCongr` gives the canonical permutation action used below.
-- Primitive/derived split:
-- the primitive public data are the ambient group `F` and an explicit basis
-- `basis : FreeGroupBasis X F`; the finite-support subgroup `basis.finiteMovedSubgroup` and the
-- source-facing subgroup `basis.elementaryNielsenAutomorphismSubgroup` are derived owner-level
-- constructions, while infinitude and countability of `X` enter only in the cardinality theorems.

/-- Distinct permutations of the basis indices induce distinct automorphisms of `F`. -/
private theorem basisReindexMulAut_injective (basis : FreeGroupBasis X F) :
    Function.Injective
      (fun σ : Equiv.Perm X ↦ (basis.repr.trans (freeGroupCongr σ)).trans basis.repr.symm) := by
  -- Proof sketch: compare the induced automorphisms on the basis elements `basis x`; if the
  -- induced automorphisms agree, transport through `basis.repr` to conclude that the underlying
  -- permutations agree on every index.
  sorry

/-- The automorphism group of a free group with infinite basis `basis` is uncountable. -/
-- Proof sketch: the canonical map
-- `fun σ : Equiv.Perm X ↦ (basis.repr.trans (freeGroupCongr σ)).trans basis.repr.symm`
-- injects the symmetric group on the basis index type into `MulAut F`, and the permutation group
-- of an infinite set is uncountable.
theorem automorphismGroup_uncountable_of_infiniteBasis
    (basis : FreeGroupBasis X F) [Infinite X] :
    Uncountable (MulAut F) := sorry

section CountableBasis

variable [Countable X]

/-- The basis-owned finite-support subgroup is countable when the basis index type is countable. -/
-- Proof sketch: an element of `basis.finiteMovedSubgroup` is determined by a finite subset of the
-- countable basis index type together with a permutation on that finite support,
-- so the subgroup is a countable union of finite-symmetry data.
theorem finiteMovedSubgroup_countable (basis : FreeGroupBasis X F) :
    Countable ↥(basis.finiteMovedSubgroup) := sorry

/-- The subgroup `Aut_f(F)` attached to `basis` is countable when the basis index type is
countable. -/
theorem elementaryNielsenAutomorphismSubgroup_countable (basis : FreeGroupBasis X F) :
    Countable ↥(basis.elementaryNielsenAutomorphismSubgroup) := by
  have h : Countable ↥(basis.finiteMovedSubgroup) :=
    finiteMovedSubgroup_countable basis
  simpa [basis.elementaryNielsenAutomorphismSubgroup_eq_finiteMovedSubgroup] using h

/-- Remark 1-4-3: if a free group has a countably infinite basis, then its full automorphism group
is uncountable, while the subgroup `Aut_f(F)` attached to that basis is countable. -/
-- Proof sketch: embed the symmetric group on the basis index type into `MulAut F` to obtain
-- uncountability, and pass from the canonical finite-support subgroup
-- `basis.finiteMovedSubgroup` back to `Aut_f(F)` using Proposition `1-4-2`.
theorem automorphism_group_cardinality_contrast
    (basis : FreeGroupBasis X F) [Infinite X] :
    Uncountable (MulAut F) ∧
      Countable ↥(basis.elementaryNielsenAutomorphismSubgroup) := by
  exact ⟨automorphismGroup_uncountable_of_infiniteBasis basis,
    elementaryNielsenAutomorphismSubgroup_countable basis⟩

end CountableBasis
