/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_1_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Proposition_1_1_9

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Corollary 1-1-10: For any set `X`, the canonical generators of `FreeGroup X` form a basis of
the free group on `X`. -/
theorem free_group_on_has_basis (X : Type u) :
    IsFreeGroupBasis (Set.range (FreeGroup.of : X → FreeGroup X)) :=
  (FreeGroupBasis.ofFreeGroup X).isFreeGroupBasis_range
