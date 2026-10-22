/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Definition_3_8
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap20.Proposition_20_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: let `u ∈ P[C] x` and `v ∈ P[C] y`. Unfold
-- `mem_setValuedProjector_iff` to obtain
-- `‖x - u‖ = Metric.infDist x C ≤ ‖x - v‖` and `‖y - v‖ = Metric.infDist y C ≤ ‖y - u‖`, then
-- apply the square-norm characterization of monotonicity from Proposition 20.2 and simplify.
/-- Example 20.12: the set-valued projector `P[C]` onto a subset of a real Hilbert space is
monotone. -/
theorem setValuedProjector_isMonotone (C : Set H) :
    (P[C]).IsMonotone := by
  rw [SetValuedOperator.isMonotone_iff_four_point_sq_norm_inequality]
  intro x u y v hu hv
  rcases mem_setValuedProjector_iff.mp hu with ⟨huC, hu_dist⟩
  rcases mem_setValuedProjector_iff.mp hv with ⟨hvC, hv_dist⟩
  have hxu : ‖x - u‖ ≤ ‖x - v‖ := by
    have hdist : dist x u ≤ dist x v := by
      rw [hu_dist]
      exact Metric.infDist_le_dist_of_mem hvC
    simpa [dist_eq_norm] using hdist
  have hyv : ‖y - v‖ ≤ ‖y - u‖ := by
    have hdist : dist y v ≤ dist y u := by
      rw [hv_dist]
      exact Metric.infDist_le_dist_of_mem huC
    simpa [dist_eq_norm] using hdist
  have hxu_sq : ‖x - u‖ ^ 2 ≤ ‖x - v‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hxu
  have hyv_sq : ‖y - v‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hyv
  simpa [add_comm, add_left_comm, add_assoc] using add_le_add hxu_sq hyv_sq
