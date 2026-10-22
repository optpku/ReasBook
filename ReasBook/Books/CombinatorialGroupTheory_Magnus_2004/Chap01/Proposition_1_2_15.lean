/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_3
import CombinatorialGroupTheory_Magnus_2004.Chap01.Corollary_1_2_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup
open scoped Pointwise Symmetrization

section

variable {α : Type u} [DecidableEq α]

namespace FreeGroup.IsNReduced

variable {U : Set (FreeGroup α)}

/-- In a noncancelling product of elements of `U^{±1}` coming from an `N`-reduced set, the reduced
length of the total product dominates the reduced length of each factor. -/
theorem norm_le_norm_list_prod_of_mem (hU : FreeGroup.IsNReduced U) (w : List (FreeGroup α))
    (hwU : ∀ u ∈ w, u ∈ U^{±1})
    (hchain : List.IsChain (fun u v ↦ u * v ≠ 1) w)
    {u : FreeGroup α} (hu : u ∈ w) :
    norm u ≤ norm w.prod := by
  sorry

end FreeGroup.IsNReduced

/-- Proposition 1-2-15: if `w` is a product of factors from `U^{±1}` with no adjacent inverse
cancellation and `U` is `N`-reduced, then the reduced length of the product is at least the number
of factors and dominates the reduced length of every factor. -/
-- Layer: source-facing theorem built from the owner abstraction `FreeGroup.IsNReduced`.
-- Primitive data are the Nielsen-reduced structure `hU`, the membership hypothesis `hwU`, and the
-- no-cancellation chain `hchain`; the displayed norm inequalities are derived API supplied by the
-- owner theorems `FreeGroup.IsNReduced.norm_list_prod_ge_length` and
-- `FreeGroup.IsNReduced.norm_le_norm_list_prod_of_mem`.
theorem nielsen_reduced_prod_norm_bounds
    {U : Set (FreeGroup α)} (hU : FreeGroup.IsNReduced U) (w : List (FreeGroup α))
    (hwU : ∀ u ∈ w, u ∈ U^{±1})
    (hchain : List.IsChain (fun u v ↦ u * v ≠ 1) w) :
    w.length ≤ norm w.prod ∧ ∀ u ∈ w, norm u ≤ norm w.prod := by
  refine ⟨hU.norm_list_prod_ge_length w hwU hchain, ?_⟩
  intro u hu
  exact hU.norm_le_norm_list_prod_of_mem w hwU hchain hu

end
