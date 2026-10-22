/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_28
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_3_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

variable {F : Type u} [Group F]
variable {H G : Subgroup F}

-- Primary domain: subgroup index and free-factor structure in finite-rank free groups.

/-- Owner-level core of Proposition 1-3-23: in a finite-rank free group of rank greater than `1`,
if `G` is a finite-index overgroup of `H` and `H` is a free factor of `G`, then `H` has finite
index in the ambient group exactly when `H = G`. -/
-- Layer triage:
-- `core/canonical`: the canonical finite-index predicates, `Group.rank`, and the chapter owner
-- relation `Subgroup.IsFreeFactorOf`.
-- `bridge/view`: the source Schreier equalities are derived by combining this equality criterion
-- with the intrinsic index formula for `G` and the canonical basis-cardinality bridges below.
-- Domain sampling:
-- 1. `Subgroup.index` in `Mathlib/GroupTheory/Index` is the owner abstraction for subgroup size.
-- 2. `Subgroup.IsFreeFactorOf` in `Definition_1_2_28` is the chapter owner abstraction for the
--    source phrase “`H` is a free factor of `G`”, and
--    `Subgroup.IsFreeFactorOf.rank_le` is its derived rank-monotonicity API.
-- 3. `eq_of_le_of_rank_ge_of_finiteIndex_subgroup` in `Proposition_1_3_17` is the chapter owner
--    rigidity theorem turning equality of rank into equality of overgroups.
-- Primitive vs. derived:
-- the primitive public data are only the finite-index hypothesis on `G`, the rank hypothesis on
-- `F`, and the owner-level free-factor-overgroup witness. Chosen bases and
-- transversal cardinalities are derived source-facing views and should not remain primitive in the
-- core API.
-- Proof sketch: `Subgroup.IsFreeFactorOf.rank_le` converts the free-factor hypothesis to the owner
-- rank inequality `Group.rank H ≤ Group.rank G`. If `H` also has finite index in `F`, Proposition
-- `1-3-17` forces `G = H`. The converse is immediate from `[G.FiniteIndex]`.
theorem finite_index_iff_eq_of_free_factor_overgroup [IsFreeGroup F] [Group.FG F]
    (hF_rank : 1 < Group.rank F) [G.FiniteIndex] (hFreeFactor : H.IsFreeFactorOf G) :
    H.FiniteIndex ↔ H = G := by
  constructor
  · intro hH
    letI : H.FiniteIndex := hH
    letI : Group.FG H := inferInstance
    letI : Group.FG G := inferInstance
    simpa using
      (eq_of_le_of_rank_ge_of_finiteIndex_subgroup (F := F) (H := H) (G := G)
        hF_rank hFreeFactor.le hFreeFactor.rank_le).symm
  · intro hHG
    subst hHG
    infer_instance

end

section

variable {F : Type u} [Group F]
variable {X : Type v} {U : Type w}
variable [Finite X] [Finite U]
variable {H G : Subgroup F}

/-- Source-facing basis-cardinality form of Proposition 1-3-23: under the Hall-Schreier setup with
finite bases `basisX` of `F` and `basisU` of `H`, the subgroup `H` has finite index in `F`
exactly when Schreier's formula holds with the intrinsic owner quantity `G.index`. -/
-- Layer triage:
-- `source-facing`: the chosen finite bases `basisX` of `F` and `basisU` of `H`.
-- `core/canonical`: `finite_index_iff_eq_of_free_factor_overgroup`.
-- `bridge/view`: the displayed cardinality equation is obtained by translating the owner equality
-- criterion through the intrinsic subgroup-index formula and the canonical equality between basis
-- cardinality and group rank.
-- Domain sampling:
-- 1. `FreeGroupBasis.cardinal_eq` in `Corollary_1_1_3` is the chapter owner bridge from a chosen
--    basis to the intrinsic rank of a free group.
-- 2. `finiteIndex_subgroup_rank_sub_one_eq` in `Proposition_1_3_9` is the chapter owner
--    Schreier formula in the canonical variables `Group.rank` and `Subgroup.index`.
-- 3. `finite_index_iff_eq_of_free_factor_overgroup` is the core equality criterion this
--    source-facing basis formula is translating.
-- The ambient nondegeneracy hypothesis `1 < Nat.card X` is essential: when `Nat.card X = 1`, the
-- subtraction in Schreier's formula collapses and the converse direction can fail for proper free
-- factors of infinite index.
theorem finite_index_iff_schreier_index_formula (basisX : FreeGroupBasis X F)
    (hX : 1 < Nat.card X) [G.FiniteIndex] (basisU : FreeGroupBasis U H)
    (hFreeFactor : H.IsFreeFactorOf G) :
    H.FiniteIndex ↔ (Nat.card X - 1) * G.index = Nat.card U - 1 := sorry

/-- Proposition 1-3-23: any right transversal of `G` realizes the source Schreier-cardinality
formula, and under the same Hall-Schreier hypotheses `H` has finite index in `F` exactly when that
formula holds. -/
-- `source-facing`: the textbook uses a finite right transversal of the ambient finite-index
-- overgroup `G`; finiteness is already automatic from `[G.FiniteIndex]`, so only the cardinality
-- equation remains in the public conclusion.
-- `bridge/view`: this is obtained from the owner statement above by rewriting the transversal
-- cardinality with `Subgroup.IsComplement.card_right`.
theorem finite_index_iff_schreier_cardinality_formula
    (basisX : FreeGroupBasis X F) (hX : 1 < Nat.card X) [G.FiniteIndex]
    (basisU : FreeGroupBasis U H) (hFreeFactor : H.IsFreeFactorOf G)
    (T : G.RightTransversal) :
    H.FiniteIndex ↔ (Nat.card X - 1) * Nat.card (T : Set F) = Nat.card U - 1 := by
  rw [T.2.card_right]
  exact finite_index_iff_schreier_index_formula basisX hX basisU hFreeFactor

end
