/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_1
import CombinatorialGroupTheory_Magnus_2004.Chap01.Definition_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {X : Type u} [DecidableEq X]

/-- Proposition 1-2-4: Every finite list of words in a free group can be carried by a Nielsen
transformation to an `N`-reduced list. -/
-- Layer triage:
-- `source-facing`: a finite Nielsen transformation carrying `U` to an `N`-reduced finite list.
-- `core/canonical`: `FreeGroup.IsNReduced` on subsets of the ambient free group.
-- `bridge/view`: the finite target list `V` is viewed directly as the set of its entries
-- `Set.range V.get`, matching the chapter's list-based Nielsen interface.
-- Proof sketch: induct on the total word length of the list, first using multiplication moves and
-- deletion of trivial entries to force `(N1)` and `(N0)`, and then apply the lexicographic
-- refinement from the textbook to eliminate the remaining violations of `(N2)`.
theorem exists_nielsen_transform_to_n_reduced (U : List (FreeGroup X)) :
    ∃ V, nielsen_transforms_to U V ∧ FreeGroup.IsNReduced (Set.range V.get) := by
  sorry

end
