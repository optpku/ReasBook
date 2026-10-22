/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_1_12
import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup

section

variable {X : Type u} [DecidableEq X]

/-- Proposition 1-2-7: if a subset `U` of a free group satisfies Nielsen's conditions `(N0)`
through `(N2)`, then the subgroup `Gp(U) = Subgroup.closure U` is free with basis given by the
elements of `U` viewed inside `Subgroup.closure U`. -/
-- Layer triage:
-- `source-facing`: the textbook free-basis conclusion for an `N`-reduced subset.
-- `core/canonical`: `IsFreeGroupBasis` and the owner abstraction `FreeGroup.IsNReduced`.
-- `bridge/view`: the reduced-word bridge
-- `closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word`; the Nielsen length estimate
-- `FreeGroup.IsNReduced.norm_list_prod_ge_length` is only the internal route to that bridge.
-- Primitive data are only `U` and the Nielsen-reduced hypothesis `hU`; the basis conclusion is
-- derived API.
theorem closure_preimage_isFreeGroupBasis_of_isNReduced
    (U : Set (FreeGroup X))
    (hU : FreeGroup.IsNReduced U) :
    IsFreeGroupBasis {x : Subgroup.closure U | (x : FreeGroup X) ∈ U} := by
  rw [closure_preimage_isFreeGroupBasis_iff_no_trivial_reduced_word]
  intro w hw hred
  sorry

end
