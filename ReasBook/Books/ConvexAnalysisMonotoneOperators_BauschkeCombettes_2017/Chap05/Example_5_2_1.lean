/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

-- Proof sketch: if `c ≥ sSup (range x)`, then
-- `x n ≤ x (n + 1) ≤ sSup (range x) ≤ c`, so `x (n + 1)` lies in the interval `[x n, c]`.
-- The distance to the right endpoint of a real interval decreases as one moves inside the interval.
/-- Example 5.2.1 (1): an increasing real sequence bounded above is Fejér monotone with respect
to the closed ray starting at the supremum of its range. -/
theorem fejerMonotone_Ici_sSup_range_of_monotone {x : ℕ → ℝ}
    (hx_mono : Monotone x) (hx_bdd : BddAbove (range x)) :
    FejerMonotone (Ici (sSup (range x))) x := by
  intro c hc n
  apply Real.dist_right_le_of_mem_uIcc
  exact Icc_subset_uIcc
    ⟨hx_mono (Nat.le_succ n), (le_csSup hx_bdd (mem_range_self (n + 1))).trans hc⟩

-- Proof sketch: if `c ≤ sInf (range x)`, then
-- `c ≤ sInf (range x) ≤ x (n + 1) ≤ x n`, so `x (n + 1)` lies in the interval `[c, x n]`.
-- The distance to the left endpoint of a real interval decreases as one moves inside the interval.
/-- Example 5.2.1 (2): a decreasing real sequence bounded below is Fejér monotone with respect
to the closed ray ending at the infimum of its range. -/
theorem fejerMonotone_Iic_sInf_range_of_antitone {x : ℕ → ℝ}
    (hx_anti : Antitone x) (hx_bdd : BddBelow (range x)) :
    FejerMonotone (Iic (sInf (range x))) x := by
  intro c hc n
  simpa [dist_comm] using Real.dist_left_le_of_mem_uIcc
    (Icc_subset_uIcc
      ⟨hc.trans (csInf_le hx_bdd (mem_range_self (n + 1))), hx_anti (Nat.le_succ n)⟩)
