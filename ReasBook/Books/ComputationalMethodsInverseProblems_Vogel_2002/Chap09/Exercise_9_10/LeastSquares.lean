/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Notation_2_4
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Algorithm_9_3_1.Iterates
public import Mathlib.Analysis.InnerProductSpace.PiL2

public section

noncomputable section

/-! Reusable Exercise 9.10 least-squares benchmark owners.

This item-owned foundation module contains the `§9.4.1` benchmark
specializations for the regularized least-squares objective `(9.2)`, its
projected-gradient trajectory, and the corresponding exact line-search
predicate. Later files can import this module directly without importing the
full source-facing `Book.Ch9.Exercise_9_10` item.
-/

namespace Exercise910

/-- The regularized least-squares objective `(9.2)` specialized to the `§9.4.1`
benchmark data. -/
abbrev objective
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  forwardOperator941.toEuclideanLin.toContinuousLinearMap.tikhonovFunctional
    ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
    data941 regularization941

/-- The Exercise 9.10 benchmark objective is exactly the displayed
regularized least-squares functional `(9.2)`. -/
@[simp] theorem objective_def
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    objective n forwardOperator941 data941 regularization941 f =
      ‖Matrix.toEuclideanLin forwardOperator941 f - data941‖ ^ 2 / 2 +
        (regularization941 / 2) * ‖f‖ ^ 2 := by
  rw [objective, ContinuousLinearMap.tikhonovFunctional_def]
  change
    ‖Matrix.toEuclideanLin forwardOperator941 f - data941‖ ^ 2 / 2 +
        regularization941 * inner ℝ ((1 / 2 : ℝ) • f) f =
      ‖Matrix.toEuclideanLin forwardOperator941 f - data941‖ ^ 2 / 2 +
        (regularization941 / 2) * ‖f‖ ^ 2
  rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring_nf

/-- Exercise 9.10. The gradient projection iterates of Algorithm 9.3.1 for the
regularized least-squares functional `(9.2)`, specialized to the `§9.4.1`
benchmark data, projector, step sizes, and initial iterate. -/
abbrev iterates
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) :
    ℕ → EuclideanSpace ℝ (Fin n) :=
  GradientProjection.iterates projector941
    (objective n forwardOperator941 data941 regularization941)
    stepSizes941 initialIterate941

/-- Helper for Exercise 9.10: the benchmark trajectory is the generic
projected-gradient iterate sequence specialized to the benchmark objective. -/
@[simp] theorem iterates_def
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
  -- This bridge simply unfolds the benchmark abbreviation to the backend owner.
  rfl

/-- The zeroth Exercise 9.10 benchmark iterate is the prescribed initial
iterate. -/
@[simp] theorem iterates_zero
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) :
    iterates n projector941 stepSizes941 forwardOperator941 data941
        regularization941 initialIterate941 0 =
      initialIterate941 :=
  GradientProjection.iterates_zero _ _ _ _

/-- The successor Exercise 9.10 benchmark iterate is the projected-gradient
update with the benchmark objective `(9.2)` and step size `τ v`. -/
@[simp] theorem iterates_succ
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n))
    (v : ℕ) :
    iterates n projector941 stepSizes941 forwardOperator941 data941
        regularization941 initialIterate941 (v + 1) =
      GradientProjection.update projector941
        (objective n forwardOperator941 data941 regularization941)
        (stepSizes941 v)
        (iterates n projector941 stepSizes941 forwardOperator941 data941
          regularization941 initialIterate941 v) :=
  GradientProjection.iterates_succ _ _ _ _ _

/-- The exact line-search condition for the Exercise 9.10 benchmark trajectory
generated by Algorithm 9.3.1 on the regularized least-squares objective
`(9.2)`. -/
abbrev isExactLineSearch
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) : Prop :=
  GradientProjection.IsExactLineSearch projector941
    (objective n forwardOperator941 data941 regularization941)
    stepSizes941 initialIterate941

/-- Helper for Exercise 9.10: the benchmark exact line-search predicate is the
backend predicate specialized to the benchmark objective and iterate family. -/
@[simp] theorem isExactLineSearch_def
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) :
    isExactLineSearch n projector941 stepSizes941 forwardOperator941
        data941 regularization941 initialIterate941 =
      GradientProjection.IsExactLineSearch projector941
        (objective n forwardOperator941 data941 regularization941)
        stepSizes941 initialIterate941 := by
  -- This bridge exposes the exact line-search abbreviation as the owner API.
  rfl

/-- `Exercise910.isExactLineSearch` is the pointwise minimizer condition from
`GradientProjection.IsExactLineSearch`, specialized to the benchmark objective
`(9.2)` and trajectory from Exercise 9.10. -/
theorem isExactLineSearch_iff
    (n : ℕ)
    (projector941 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (stepSizes941 : ℕ → ℝ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (regularization941 : ℝ)
    (initialIterate941 : EuclideanSpace ℝ (Fin n)) :
    isExactLineSearch n projector941 stepSizes941 forwardOperator941
        data941 regularization941 initialIterate941 ↔
      ∀ v,
        IsMinOn
          (LineSearch.profile
            (objective n forwardOperator941 data941 regularization941 ∘
              projector941)
            (iterates n projector941 stepSizes941 forwardOperator941 data941
              regularization941 initialIterate941 v)
            (GradientProjection.direction
              (objective n forwardOperator941 data941 regularization941)
              (iterates n projector941 stepSizes941 forwardOperator941 data941
                regularization941 initialIterate941 v)))
          (Set.Ioi (0 : ℝ))
          (stepSizes941 v) :=
  GradientProjection.isExactLineSearch_iff _ _ _ _

end Exercise910
