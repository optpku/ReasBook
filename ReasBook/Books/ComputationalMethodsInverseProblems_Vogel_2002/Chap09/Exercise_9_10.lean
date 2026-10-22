/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Exercise_9_10.LeastSquares

public section

noncomputable section

/-! Exercise 9.10. Source-facing projected-gradient benchmark specialization.

The reusable `§9.4.1` least-squares benchmark owners live in the item-local
foundation module `Book.Ch9.Exercise_9_10.LeastSquares`. This file stays thin
and source-facing by re-exporting those owners and recording the intended
exercise-level specializations through `#check`.
-/

/- Source-facing check for the `§9.4.1` specialization of the regularized
least-squares functional `(9.2)`. -/
#check Exercise910.objective
#check Exercise910.objective_def

namespace Exercise910

/-- Exercise 9.10. Apply Algorithm 9.3.1 to the `§9.4.1` benchmark data by
specializing the projected-gradient iterate family to the regularized
least-squares functional `(9.2)`, while keeping the concrete projector,
step-size sequence, forward operator, datum, regularization parameter, and
initial iterate explicit. -/
abbrev benchmarkIterates
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) :=
  iterates n projector941 stepSizes941 forwardOperator941 data941
    regularization941 initialIterate941

/-- Helper for Exercise 9.10: this source-facing bridge rewrites the benchmark
trajectory to the generic projected-gradient iterate owner specialized to the
regularized least-squares functional `(9.2)`. -/
theorem benchmarkIterates_eq
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) :
    iterates n projector941 stepSizes941 forwardOperator941 data941
        regularization941 initialIterate941 =
      GradientProjection.iterates projector941
        (objective n forwardOperator941 data941 regularization941)
        stepSizes941 initialIterate941 := by
  -- This source-facing theorem just exposes the benchmark specialization.
  rfl

end Exercise910

/- Source-facing check for the benchmark-specialized projected-gradient
trajectory from Exercise 9.10.

Apply Algorithm 9.3.1 to minimize the regularized
least-squares functional `(9.2)` using the `§9.4.1` benchmark data and
parameters.

The concrete `§9.4.1` forward operator, datum, projector, step-size sequence,
and initial iterate remain explicit parameters at this source-facing surface,
while the reusable mathematical owners stay
`ContinuousLinearMap.tikhonovFunctional` and
`GradientProjection.iterates`. -/
#check Exercise910.benchmarkIterates_eq
#check Exercise910.iterates
#check Exercise910.iterates_zero
#check Exercise910.iterates_succ

/- Source-facing check for the exact line-search clause attached to the
benchmark-specialized Algorithm 9.3.1 trajectory. -/
#check Exercise910.isExactLineSearch
#check Exercise910.isExactLineSearch_iff

/- Backend owners used by the Exercise 9.10 source-facing bridge. -/
#check GradientProjection.iterates
#check GradientProjection.IsExactLineSearch
#check ContinuousLinearMap.tikhonovFunctional
