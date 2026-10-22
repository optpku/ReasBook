/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open FreeGroup
open scoped Pointwise Symmetrization

section

variable {X : Type u} [DecidableEq X]

namespace FreeGroup.IsNReduced

variable {U : Set (FreeGroup X)}

local notation "mk" => FreeGroup.mk
local notation "NoCancellation" => List.IsChain (fun u v : FreeGroup X ↦ u * v ≠ 1)

/-- Proposition 1-2-5: if `U` satisfies Nielsen's conditions `(N0)` through `(N2)`, then one can
associate to each `u ∈ U^{±1}` a prefix word `a u` and a nontrivial middle segment `m u` whose
letters survive in reduced products with no adjacent inverse cancellation. -/
-- Layer triage:
-- `source-facing`: the existence of the prefix and middle-segment functions appearing in the
-- textbook statement.
-- `core/canonical`: the owner abstraction `FreeGroup.IsNReduced` together with the reduced-word
-- API `toWord`.
-- `bridge/view`: the concrete functions `a` and `m` extracted from the Nielsen-reduced hypothesis.
-- Primitive data are only `U` and `hU`; the functions `a` and `m` and their survival properties
-- are derived output, so there is no separate public owner structure here.
-- Proof sketch: define `a u` as the longest initial segment of `u` that cancels in a nontrivial
-- product `v * u` with `v ∈ U^{±1}`. Condition `(N2)` forces the complementary middle segment to
-- be nonempty, and the cancellation pattern for a product with no adjacent inverse cancellation
-- shows that each chosen middle segment survives in the final reduced word. The chosen occurrence
-- is expressed source-faithfully by a list split `w = s ++ u :: t`, rather than raw index
-- arithmetic on `w`.
theorem exists_prefix_middle_segments
    (hU : IsNReduced U) :
    ∃ a m : FreeGroup X → List (X × Bool),
      (∀ ⦃u : FreeGroup X⦄, u ∈ U^{±1} → m u ≠ []) ∧
      (∀ ⦃u : FreeGroup X⦄, u ∈ U^{±1} →
        u.toWord = a u ++ m u ++ invRev (a u⁻¹)) ∧
      ∀ (s t : List (FreeGroup X)) (u : FreeGroup X),
        (∀ v ∈ s ++ u :: t, v ∈ U^{±1}) →
        NoCancellation (s ++ u :: t) →
        (s ++ u :: t).prod.toWord =
          ((s.prod * mk (a u)).toWord ++
            m u ++
            (mk (invRev (a u⁻¹)) * t.prod).toWord) := sorry

end FreeGroup.IsNReduced

end
