/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/- Text 1.0.43: in the Hausdorff setting of the text, compactness of a subset `C` is formalized by
the canonical predicate `IsCompact C`. -/
recall IsCompact {X : Type u} [TopologicalSpace X] (C : Set X) : Prop

/- Its canonical open-cover characterization is the theorem
`isCompact_iff_finite_subcover`. -/
recall isCompact_iff_finite_subcover {X : Type u} [TopologicalSpace X] {s : Set X} :
    IsCompact s ↔
      ∀ {ι : Type u} (U : ι → Set X),
        (∀ i, IsOpen (U i)) → s ⊆ ⋃ i, U i → ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i
