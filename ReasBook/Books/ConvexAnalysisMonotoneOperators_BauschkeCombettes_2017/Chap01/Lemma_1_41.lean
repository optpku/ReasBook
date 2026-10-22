/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [MetricSpace X] {C : Set X}

/-- Lemma 1.41: a compact subset of a metric space is closed and bounded. -/
theorem isClosed_and_isBounded_of_isCompact (hC : IsCompact C) :
    IsClosed C ∧ Bornology.IsBounded C := by
  exact ⟨hC.isClosed, hC.isBounded⟩
