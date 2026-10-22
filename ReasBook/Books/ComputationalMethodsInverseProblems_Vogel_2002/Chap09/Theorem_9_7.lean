/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_6.Projection
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

open scoped EuclideanProjection

/-- Theorem 9.7 (1). If `C ⊆ EuclideanSpace ℝ (Fin n)` is nonempty, closed, and convex, then
for every `x` there is a unique point of `C` minimizing the distance `‖x - y‖`; this is the
well-definedness of the operator `P_C` from `(9.15)`. -/
theorem existsUniqueMetricProjection
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC_nonempty : C.Nonempty)
    (hC : Set.ClosedConvex C) (x : EuclideanSpace ℝ (Fin n)) :
    ∃! y, y ∈ C ∧ IsMinOn (fun z ↦ ‖x - z‖) C y := by
  simpa using EuclideanProjection.existsUnique_proj C hC_nonempty hC x

/-- Theorem 9.7 (2). If `C ⊆ EuclideanSpace ℝ (Fin n)` is nonempty, closed, and convex, then
the metric projection operator `P_{C | hC_nonempty, hC}` from `(9.15)` is
continuous. -/
theorem continuousMetricProjection
    {n : ℕ} (C : Set (EuclideanSpace ℝ (Fin n))) (hC_nonempty : C.Nonempty)
    (hC : Set.ClosedConvex C) :
    Continuous (P_{C | hC_nonempty, hC}) := by
  simpa using EuclideanProjection.continuous_proj C hC_nonempty hC
