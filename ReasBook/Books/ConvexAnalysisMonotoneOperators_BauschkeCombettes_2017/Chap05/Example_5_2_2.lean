/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap05.Example_5_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open Set

/-- Helper for Example 5.2.2: on `ℝ`, the one-step metric inequality from Fejér monotonicity is
the textbook absolute-value inequality. -/
theorem abs_sub_le_abs_sub_of_fejer_step {C : Set ℝ} {x : ℕ → ℝ}
    (hx_fejer : FejerMonotone C x) {c : ℝ} (hc : c ∈ C) (n : ℕ) :
    |x (n + 1) - c| ≤ |x n - c| := by
  -- Rewrite the abstract metric step into the absolute-value form used in the chapter.
  simpa [dist_eq_norm, Real.norm_eq_abs] using hx_fejer.step c hc n

-- Proof sketch: if `x` is monotone and `c ≥ sSup (range x)`, then
-- `x n ≤ x (n + 1) ≤ sSup (range x) ≤ c`; both absolute values therefore simplify to
-- differences from `c`, and the desired inequality follows from monotonicity.
/-- Example 5.2.2 (1): for an increasing real sequence bounded above, the one-step distance to any
point of the closed ray starting at the supremum of its range does not increase. -/
theorem abs_sub_le_abs_sub_of_mem_Ici_sSup_range_of_monotone {x : ℕ → ℝ}
    (hx_mono : Monotone x) (hx_bdd : BddAbove (range x)) {c : ℝ}
    (hc : c ∈ Ici (sSup (range x))) (n : ℕ) :
    |x (n + 1) - c| ≤ |x n - c| := by
  -- Specialize the Fejér-monotonicity theorem from Example 5.2.1 at the chosen point `c`.
  exact abs_sub_le_abs_sub_of_fejer_step
    (fejerMonotone_Ici_sSup_range_of_monotone hx_mono hx_bdd) hc n

-- Proof sketch: if `x` is antitone and `c ≤ sInf (range x)`, then
-- `c ≤ sInf (range x) ≤ x (n + 1) ≤ x n`; both absolute values simplify to differences from
-- `c`, and antitonicity gives the required inequality.
/-- Example 5.2.2 (2): for a decreasing real sequence bounded below, the one-step distance to any
point of the closed ray ending at the infimum of its range does not increase. -/
theorem abs_sub_le_abs_sub_of_mem_Iic_sInf_range_of_antitone {x : ℕ → ℝ}
    (hx_anti : Antitone x) (hx_bdd : BddBelow (range x)) {c : ℝ}
    (hc : c ∈ Iic (sInf (range x))) (n : ℕ) :
    |x (n + 1) - c| ≤ |x n - c| := by
  -- The decreasing case follows by the same specialization-rewrite pattern.
  exact abs_sub_le_abs_sub_of_fejer_step
    (fejerMonotone_Iic_sInf_range_of_antitone hx_anti hx_bdd) hc n
