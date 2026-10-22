/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set TopologicalSpace

/-- Text 1.0.48: the usual topology on `ℝ` has as a basis the family of open intervals
`(a, b)` with `a < b`. -/
-- Proof sketch: apply `isTopologicalBasis_of_isOpen_of_nhds`; openness of each interval is
-- `isOpen_Ioo`, and the neighborhood basis condition is exactly
-- `mem_nhds_iff_exists_Ioo_subset`.
theorem real_isTopologicalBasis_Ioo :
    TopologicalSpace.IsTopologicalBasis { s : Set ℝ | ∃ a b, a < b ∧ s = Ioo a b } := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact isOpen_Ioo
  · intro x s hx hs
    rcases mem_nhds_iff_exists_Ioo_subset.1 (hs.mem_nhds hx) with ⟨a, b, hxIoo, hIoo⟩
    exact ⟨Ioo a b, ⟨a, b, hxIoo.1.trans hxIoo.2, rfl⟩, hxIoo, hIoo⟩
