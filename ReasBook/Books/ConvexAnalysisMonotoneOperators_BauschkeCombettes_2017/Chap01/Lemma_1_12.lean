/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Lemma 1.12: a compact subset of a Hausdorff topological space is closed. -/
theorem isClosed_of_isCompact
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} :
    IsCompact C → IsClosed C :=
  IsCompact.isClosed
