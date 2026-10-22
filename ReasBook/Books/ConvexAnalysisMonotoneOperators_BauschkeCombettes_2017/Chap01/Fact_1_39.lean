/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [MetricSpace X]

/-- Fact 1.39: a subset of a metric space is compact if and only if it is sequentially compact. -/
-- Proof sketch: metric spaces are pseudometrizable, so this is the canonical mathlib theorem
-- `isCompact_iff_isSeqCompact` specialized to the subset `C`.
theorem isCompact_iff_isSeqCompact_of_metricSpace (C : Set X) :
    IsCompact C ↔ IsSeqCompact C := by
  simpa using (isCompact_iff_isSeqCompact : IsCompact C ↔ IsSeqCompact C)
