/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

/-- Example 1.48: the textbook estimate (1.67) is the pointwise form of the canonical
`1`-Lipschitz estimate for `x ↦ Metric.infDist x C`; the book's nonemptiness hypothesis is
unnecessary for this inequality. -/
theorem abs_infDist_sub_infDist_le_dist {α : Type u} [PseudoMetricSpace α] {C : Set α} (x y : α) :
    |Metric.infDist x C - Metric.infDist y C| ≤ dist x y := by
  simpa [Real.dist_eq, one_mul] using (Metric.lipschitz_infDist_pt C).dist_le_mul x y
