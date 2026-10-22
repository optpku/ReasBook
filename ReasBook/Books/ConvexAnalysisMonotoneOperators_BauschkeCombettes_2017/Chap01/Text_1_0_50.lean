/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Text 1.0.50 (1): the real line with its usual metric topology is Hausdorff. -/
theorem real_t2Space : T2Space ℝ := inferInstance

/-- Text 1.0.50 (2): the real line with its usual topology is not compact. -/
theorem real_not_compact : ¬ CompactSpace ℝ := by
  simpa [not_compactSpace_iff] using (inferInstance : NoncompactSpace ℝ)
