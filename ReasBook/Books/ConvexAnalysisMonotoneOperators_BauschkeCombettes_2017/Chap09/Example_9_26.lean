/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Example_9_25

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

-- Proof sketch: this is the probability-measure specialization of the chapter's finite-measure
-- owner theorem `lp_norm_le_measure_univ_rpow_mul_lq_norm`; the factor
-- `((P Set.univ).toReal) ^ (1 / p - 1 / q)` simplifies to `1` because `P` is a probability
-- measure.
/-- Example 9.26: on a probability space, the `L^p` norm of a real-valued random variable is
bounded above by its `L^q` norm whenever `0 < p < q`. This is the probability-space
specialization of `lp_norm_le_measure_univ_rpow_mul_lq_norm` to `H = ℝ`. -/
theorem lp_norm_le_lq_norm_of_isProbabilityMeasure
    [IsProbabilityMeasure P] {p q : ℝ} (hp : 0 < p) (hpq : p < q) {X : Ω → ℝ}
    (hX : MemLp X (ENNReal.ofReal q) P) :
    (∫ ω, |X ω| ^ p ∂P) ^ (1 / p) ≤ (∫ ω, |X ω| ^ q ∂P) ^ (1 / q) := by
  simpa [Real.norm_eq_abs, measure_univ] using
    lp_norm_le_measure_univ_rpow_mul_lq_norm hp hpq hX
