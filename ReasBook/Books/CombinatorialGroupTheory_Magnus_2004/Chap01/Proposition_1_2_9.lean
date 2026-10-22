/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_1_3
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open scoped Cardinal

section

variable {F : Type u} [Group F]

-- Primary domain: finite-rank free groups and finite generating sets.
-- `source-facing`: a finite generating subset of a free group with chosen finite basis.
-- `core/canonical`: `FreeGroupBasis ι F`, `Group.rank`, and `IsFreeGroupBasis`.
-- `bridge/view`: a finite generating set `U : Finset F` is recorded by
-- `Subgroup.closure (↑U : Set F) = ⊤`.
--
-- Domain sampling:
-- 1. `FreeGroupBasis.cardinal_eq` is the chapter owner theorem equating the cardinalities of two
--    free bases of the same group.
-- 2. `Subgroup.rank_closure_finset_le_card` is mathlib's owner inequality bounding the rank of a
--    finitely generated subgroup by the size of a chosen finite generating set.
-- 3. `Group.rank` is the canonical owner for finite generation rank, so finite-generator
--    inequalities should pass through it rather than through ad hoc local wrapper data.
-- 4. `IsFreeGroupBasis` is the chapter's source-facing owner for “this displayed subset itself is
--    a basis”.
--
-- Primitive vs. derived:
-- the primitive public data are a chosen finite basis `basis : FreeGroupBasis ι F` and a finite
-- subset `U : Finset F`. The rank bound and the criterion that `U` itself is a basis are derived
-- API and belong at the owner level; the specialized `Fin n` formulations below are source-facing
-- wrappers around those owner declarations.

/-- Owner criterion for finite generating sets in a finite-rank free group: a finite subset is a
free basis exactly when it has the same cardinality as the chosen basis and generates the ambient
group. -/
-- Layer triage:
-- `core/canonical`: this is the owner-level finite-rank criterion organized around
-- `FreeGroupBasis ι F`, `Fintype.card ι`, and `IsFreeGroupBasis`.
-- `bridge/view`: the source-facing `Fin n` statements below are immediate specializations.
theorem finset_isFreeGroupBasis_iff_card_and_closure_eq_top {ι : Type*}
    (basis : FreeGroupBasis ι F) [Fintype ι] (U : Finset F) :
    IsFreeGroupBasis (U : Set F) ↔
      U.card = Fintype.card ι ∧ Subgroup.closure (U : Set F) = ⊤ := sorry

/-- Owner inequality for finite generating sets in a finite-rank free group. -/
-- Layer triage:
-- `core/canonical`: `FreeGroupBasis ι F` and `Fintype.card ι`.
-- `bridge/view`: `rank_le_card_of_generating_finset` is the specialized `Fin n` source wrapper.
theorem fintype_card_le_card_of_generating_finset {ι : Type*}
    (basis : FreeGroupBasis ι F) [Fintype ι] (U : Finset F)
    (hgen : Subgroup.closure (U : Set F) = ⊤) :
    Fintype.card ι ≤ U.card := sorry

variable {n : ℕ}

/-- Proposition 1-2-9 (1): if a free group `F` has a basis indexed by `Fin n`, then any finite
generating set of `F` has at least `n` elements. -/
-- Layer triage:
-- `source-facing`: the minimal-number-of-generators statement for a free group of rank `n`.
-- `core/canonical`: `fintype_card_le_card_of_generating_finset`.
-- `bridge/view`: specialize the owner theorem to the basis indexed by `Fin n`.
theorem rank_le_card_of_generating_finset (basis : FreeGroupBasis (Fin n) F) (U : Finset F)
    (hgen : Subgroup.closure (U : Set F) = ⊤) :
    n ≤ U.card := by
  simpa using fintype_card_le_card_of_generating_finset basis U hgen

/-- Proposition 1-2-9 (2): if a free group `F` has rank `n`, then any generating set of exactly
`n` elements is a free basis of `F`. -/
-- Layer triage:
-- `source-facing`: the given generating set `U` itself is a basis of `F`.
-- `core/canonical`: `finset_isFreeGroupBasis_iff_card_and_closure_eq_top`.
-- `bridge/view`: specialize the owner theorem to the textbook rank-`n` formulation.
theorem isFreeGroupBasis_of_generating_finset_card_eq_rank
    (basis : FreeGroupBasis (Fin n) F) (U : Finset F)
    (hgen : Subgroup.closure (U : Set F) = ⊤) (hcard : U.card = n) :
    IsFreeGroupBasis (U : Set F) := by
  exact
    (finset_isFreeGroupBasis_iff_card_and_closure_eq_top basis U).2
      ⟨by simpa using hcard, hgen⟩

end
