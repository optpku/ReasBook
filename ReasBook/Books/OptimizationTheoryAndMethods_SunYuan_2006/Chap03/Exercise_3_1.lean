/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.Rayleigh
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Hermitian
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_2_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Definition_3_2_extra_1

open Matrix

-- Domain sampling:
-- * `IsExactLineSearchStepOnNonnegativeRay` is the Chapter 2 source-facing owner for exact
--   line search on the nonnegative ray, built on mathlib's minimizer owner `IsMinOn`.
-- * `steepestDescentDirection` and `steepestDescentStep` are the Chapter 3 owners for the
--   steepest-descent direction and update.
-- * `IsNewtonDirectionAt` is the Chapter 3 source-facing owner for Newton directions;
--   `newtonDirection` and `newtonNextIterate` are the explicit inverse-form bridge
--   declarations under nonsingularity.
-- This exercise keeps only the concrete quadratic data source-facing and states the update
-- results through those existing owners.

noncomputable section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- The quadratic objective
`x ↦ (3 / 2) * x₀^2 + (1 / 2) * x₁^2 - x₀ * x₁ - 2 * x₀`
from Exercise 3.1. -/
def chapter03Exercise31Objective (x : Point) : ℝ :=
  (3 / 2 : ℝ) * (x 0) ^ (2 : ℕ) + (1 / 2 : ℝ) * (x 1) ^ (2 : ℕ) - x 0 * x 1 - 2 * x 0

/-- The initial point `(-2, 4)` used in Exercise 3.1. -/
def chapter03Exercise31InitialPoint : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(-2 : ℝ), 4]

/-- The minimizer candidate `(1, 1)` for `chapter03Exercise31Objective`. -/
def chapter03Exercise31Minimizer : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(1 : ℝ), 1]

/-- The exact first steepest-descent step size `5 / 17` used from `(-2, 4)`. -/
def chapter03Exercise31SteepestDescentStepSize : ℝ :=
  5 / 17

/-- The first steepest-descent iterate `(26 / 17, 38 / 17)` reported in Exercise 3.1. -/
def chapter03Exercise31SteepestDescentFirstIterate : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(26 / 17 : ℝ), 38 / 17]

/-- The Hessian matrix `[[3, -1], [-1, 1]]` of `chapter03Exercise31Objective`. -/
def chapter03Exercise31Hessian : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(3 : ℝ), -1; -1, 1]

/-- The linear term vector `(-2, 0)` in the coordinate gradient formula. -/
def chapter03Exercise31LinearTermVector : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(-2 : ℝ), 0]

/-- Helper for Chapter03 Exercise 3.1: the constant Hessian matrix is symmetric. -/
theorem chapter03Exercise31Hessian_isSymm :
    chapter03Exercise31Hessian.IsSymm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chapter03Exercise31Hessian]

/-- Helper for Chapter03 Exercise 3.1: the quadratic core with Hessian
`chapter03Exercise31Hessian` has Fréchet derivative `chapter03Exercise31Hessian x`. -/
theorem chapter03Exercise31Objective_hasFDerivAt_quadratic_core
    (x : Point) :
    HasFDerivAt
      (fun y : Point ↦
        (1 / 2 : ℝ) * dotProduct y (Matrix.toEuclideanLin chapter03Exercise31Hessian y))
      (InnerProductSpace.toDual ℝ Point (Matrix.toEuclideanLin chapter03Exercise31Hessian x))
      x := by
  have hHermitian : chapter03Exercise31Hessian.IsHermitian := by
    simpa [Matrix.isHermitian_iff_isSymm] using chapter03Exercise31Hessian_isSymm
  let T : Point →L[ℝ] Point :=
    (Matrix.toEuclideanCLM : Matrix (Fin 2) (Fin 2) ℝ ≃⋆ₐ[ℝ] Point →L[ℝ] Point)
      chapter03Exercise31Hessian
  have hT : (T : Point →ₗ[ℝ] Point) = Matrix.toEuclideanLin chapter03Exercise31Hessian := by
    simpa [T] using
      (Matrix.coe_toEuclideanCLM_eq_toEuclideanLin chapter03Exercise31Hessian)
  have hSymmLin0 : chapter03Exercise31Hessian.toEuclideanLin.IsSymmetric := by
    exact (Matrix.isSymmetric_toEuclideanLin_iff (A := chapter03Exercise31Hessian)).2 hHermitian
  have hSymmLin : (T : Point →ₗ[ℝ] Point).IsSymmetric := by
    simpa [hT] using hSymmLin0
  -- Use the symmetric-operator quadratic derivative once so later coordinate proofs can reuse it.
  have hCore :
      HasStrictFDerivAt
        (fun y : Point ↦ T.reApplyInnerSelf y)
        (2 • (innerSL ℝ (T x)))
        x :=
    hSymmLin.hasStrictFDerivAt_reApplyInnerSelf x
  have hScaled :
      HasFDerivAt
        (fun y : Point ↦ (1 / 2 : ℝ) * T.reApplyInnerSelf y)
        ((1 / 2 : ℝ) • (2 • (innerSL ℝ (T x))))
        x :=
    hCore.hasFDerivAt.const_mul (1 / 2 : ℝ)
  -- Rewrite the abstract quadratic core back into the explicit `dotProduct` form.
  refine (hScaled.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext y
    simpa [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply] using
      congrArg (fun S : Point →ₗ[ℝ] Point ↦ inner ℝ (S x) y) hT
  · filter_upwards with y
    calc
      (1 / 2 : ℝ) * dotProduct y (Matrix.toEuclideanLin chapter03Exercise31Hessian y)
          = (1 / 2 : ℝ) * inner ℝ y (T y) := by
              congr 1
              simpa [hT] using
                (Matrix.inner_toEuclideanCLM chapter03Exercise31Hessian y y).symm
      _ = (1 / 2 : ℝ) * T.reApplyInnerSelf y := by
            simp [ContinuousLinearMap.reApplyInnerSelf_apply, real_inner_comm]

/-- Helper for Chapter03 Exercise 3.1: before rewriting coordinates, the gradient is the
matrix-vector affine form `H x + (-2, 0)`. -/
theorem chapter03Exercise31Objective_hasGradientAt_matrix_form
    (x : Point) :
    HasGradientAt
      chapter03Exercise31Objective
      (Matrix.toEuclideanLin chapter03Exercise31Hessian x + chapter03Exercise31LinearTermVector)
      x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have hQuadratic := chapter03Exercise31Objective_hasFDerivAt_quadratic_core x
  have hLinear :
      HasFDerivAt
        (fun y : Point ↦
          (InnerProductSpace.toDual ℝ Point chapter03Exercise31LinearTermVector) y)
        (InnerProductSpace.toDual ℝ Point chapter03Exercise31LinearTermVector)
        x := by
    -- The affine term is the continuous linear functional induced by `(-2, 0)`.
    exact (InnerProductSpace.toDual ℝ Point chapter03Exercise31LinearTermVector).hasFDerivAt
  -- Assemble the quadratic, linear, and constant pieces before converting to coordinates.
  let hSum :=
    hQuadratic.add (hLinear.add (hasFDerivAt_const (0 : ℝ) x))
  refine
    (hSum.congr_fderiv ?_).congr_of_eventuallyEq ?_
  · ext y
    simp [chapter03Exercise31LinearTermVector, InnerProductSpace.toDual_apply_apply]
  · filter_upwards with y
    simp [chapter03Exercise31Objective, chapter03Exercise31Hessian,
      chapter03Exercise31LinearTermVector, InnerProductSpace.toDual_apply_apply,
      EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, pow_two,
      sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_add]
    ring_nf

/-- Helper for Chapter03 Exercise 3.1: the objective has the explicit coordinate gradient used
in the steepest-descent and Newton computations. -/
theorem chapter03Exercise31Objective_hasGradientAt
    (x : Point) :
    HasGradientAt
      chapter03Exercise31Objective
      ((EuclideanSpace.equiv (Fin 2) ℝ).symm ![(3 * x 0 - x 1 - 2 : ℝ), x 1 - x 0])
      x := by
  have hMatrix := chapter03Exercise31Objective_hasGradientAt_matrix_form x
  have hcoord :
      Matrix.toEuclideanLin chapter03Exercise31Hessian x + chapter03Exercise31LinearTermVector =
        (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(3 * x 0 - x 1 - 2 : ℝ), x 1 - x 0] := by
    ext i
    fin_cases i
    · simp only [chapter03Exercise31Hessian, chapter03Exercise31LinearTermVector, Fin.zero_eta,
        Fin.isValue, PiLp.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ofLp_toLpLin,
        toLin'_apply,
        PiLp.continuousLinearEquiv_symm_apply, cons_val_zero]
      norm_num
      ring_nf
    · simp only [chapter03Exercise31Hessian, chapter03Exercise31LinearTermVector, Fin.mk_one,
        Fin.isValue, PiLp.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, ofLp_toLpLin,
        toLin'_apply,
        PiLp.continuousLinearEquiv_symm_apply, cons_val_one, cons_val_fin_one]
      norm_num
      ring_nf
  rw [← hcoord]
  exact hMatrix

/-- Helper for Chapter03 Exercise 3.1: the gradient of the objective is the explicit affine map
`x ↦ (3 x₀ - x₁ - 2, x₁ - x₀)`. -/
theorem chapter03Exercise31Objective_gradient_eq
    (x : Point) :
    gradient chapter03Exercise31Objective x =
      (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(3 * x 0 - x 1 - 2 : ℝ), x 1 - x 0] :=
  (chapter03Exercise31Objective_hasGradientAt x).gradient

/-- Helper for Chapter03 Exercise 3.1: completing the square around `(1, 1)` rewrites the
objective as its minimum value `-1` plus two nonnegative error terms. -/
theorem chapter03Exercise31Objective_eq_min_value_add_error
    (x : Point) :
    chapter03Exercise31Objective x =
      (-1 : ℝ) + (x 0 - 1) ^ (2 : ℕ) +
        (1 / 2 : ℝ) * ((x 0 - 1) - (x 1 - 1)) ^ (2 : ℕ) := by
  -- Expand the completed square once so the minimizer proof can use only square nonnegativity.
  simp [chapter03Exercise31Objective, pow_two]
  ring

/-- The Hessian matrix from Exercise 3.1 is positive definite. -/
theorem chapter03Exercise31Hessian_posDef :
    chapter03Exercise31Hessian.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ ?_
  · simpa [Matrix.isHermitian_iff_isSymm] using chapter03Exercise31Hessian_isSymm
  · intro x hx
    change 0 < dotProduct x (chapter03Exercise31Hessian.mulVec x)
    have hrewrite :
        dotProduct x (chapter03Exercise31Hessian.mulVec x) =
          (x 0 - x 1) ^ (2 : ℕ) + 2 * (x 0) ^ (2 : ℕ) := by
      simp [chapter03Exercise31Hessian, dotProduct, Fin.sum_univ_two, pow_two]
      ring
    rw [hrewrite]
    by_cases hx0 : x 0 = 0
    · have hx1 : x 1 ≠ 0 := by
        intro hx1
        apply hx
        ext i
        fin_cases i <;> simp [hx0, hx1]
      have hsq : 0 < (x 0 - x 1) ^ (2 : ℕ) := by
        have hne : x 0 - x 1 ≠ 0 := by simp [hx0, hx1]
        exact sq_pos_of_ne_zero hne
      nlinarith
    · have hsq : 0 < 2 * (x 0) ^ (2 : ℕ) := by
        have hx0sq : 0 < (x 0) ^ (2 : ℕ) := sq_pos_of_ne_zero hx0
        nlinarith
      have hother : 0 ≤ (x 0 - x 1) ^ (2 : ℕ) := sq_nonneg (x 0 - x 1)
      nlinarith

/-- The Newton direction `(3, -3)` reported at the initial point `(-2, 4)`. -/
def chapter03Exercise31NewtonDirectionAtInitialPoint : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm ![(3 : ℝ), (-3 : ℝ)]

/-- The quadratic objective from Exercise 3.1 is minimized on `Set.univ` at `(1, 1)`. -/
theorem chapter03Exercise31Objective_isMinOn :
    IsMinOn chapter03Exercise31Objective Set.univ chapter03Exercise31Minimizer := by
  rw [isMinOn_univ_iff]
  intro x
  -- Rewrite both objective values by the completed-square identity and compare the nonnegative
  -- remainder terms.
  have hmin : chapter03Exercise31Objective chapter03Exercise31Minimizer = -1 := by
    rw [chapter03Exercise31Objective_eq_min_value_add_error]
    norm_num [chapter03Exercise31Minimizer]
  rw [hmin, chapter03Exercise31Objective_eq_min_value_add_error]
  have hsq0 : 0 ≤ (x 0 - 1) ^ (2 : ℕ) := sq_nonneg (x 0 - 1)
  have hsq1 : 0 ≤ ((x 0 - 1) - (x 1 - 1)) ^ (2 : ℕ) := sq_nonneg ((x 0 - 1) - (x 1 - 1))
  nlinarith [hsq0, hsq1]

/-- Helper for Chapter03 Exercise 3.1: the exact steepest-descent line-search profile from
`(-2, 4)` is a positive multiple of a square centered at `5 / 17`. -/
theorem chapter03Exercise31_line_search_profile_eq_completed_square
    (α : ℝ) :
    lineSearchObjective
      chapter03Exercise31Objective
      chapter03Exercise31InitialPoint
      (steepestDescentDirection chapter03Exercise31Objective chapter03Exercise31InitialPoint)
      α =
      (-8 / 17 : ℝ) + 306 * (α - 5 / 17) ^ (2 : ℕ) := by
  -- Replace the steepest-descent direction by the explicit initial gradient and expand.
  rw [lineSearchObjective_apply, steepestDescentDirection, chapter03Exercise31Objective_gradient_eq]
  simp [chapter03Exercise31Objective, chapter03Exercise31InitialPoint, pow_two]
  ring

/-- The exact steepest-descent line-search step from `(-2, 4)` along the steepest descent
direction is `5 / 17`. -/
theorem chapter03Exercise31_steepestDescentLineSearch :
    IsExactLineSearchStepOnNonnegativeRay
      chapter03Exercise31Objective
      chapter03Exercise31InitialPoint
      (steepestDescentDirection
        chapter03Exercise31Objective chapter03Exercise31InitialPoint)
      chapter03Exercise31SteepestDescentStepSize := by
  rw [isExactLineSearchStepOnNonnegativeRay_iff]
  refine ⟨by norm_num [chapter03Exercise31SteepestDescentStepSize], ?_⟩
  intro α hα
  -- The completed-square profile turns exact line search into the nonnegativity of one square.
  rw [chapter03Exercise31SteepestDescentStepSize,
    chapter03Exercise31_line_search_profile_eq_completed_square,
    chapter03Exercise31_line_search_profile_eq_completed_square]
  have hsq : 0 ≤ (α - 5 / 17) ^ (2 : ℕ) := sq_nonneg (α - 5 / 17)
  nlinarith [hsq]

/-- Chapter03 Exercise 3.1 (1): the exact steepest-descent update from `(-2, 4)` is
`(26 / 17, 38 / 17)`. -/
theorem chapter03Exercise31_steepestDescentMethod :
    steepestDescentStep
        chapter03Exercise31Objective
        chapter03Exercise31InitialPoint
        chapter03Exercise31SteepestDescentStepSize =
      chapter03Exercise31SteepestDescentFirstIterate := by
  -- Rewrite the steepest-descent update as `x - α ∇f(x)` and simplify the two coordinates.
  rw [steepestDescentStep_eq, chapter03Exercise31Objective_gradient_eq]
  ext i
  fin_cases i
  · norm_num [chapter03Exercise31InitialPoint, chapter03Exercise31SteepestDescentStepSize,
      chapter03Exercise31SteepestDescentFirstIterate]
  · norm_num [chapter03Exercise31InitialPoint, chapter03Exercise31SteepestDescentStepSize,
      chapter03Exercise31SteepestDescentFirstIterate]

/-- Helper for Chapter03 Exercise 3.1: the reported vector `(3, -3)` already solves the Newton
linear system at the initial point. -/
theorem chapter03Exercise31_reported_newton_direction_is_newton_direction_at_initial :
    IsNewtonDirectionAt
      chapter03Exercise31Objective
      chapter03Exercise31InitialPoint
      (fun _ ↦ chapter03Exercise31Hessian)
      chapter03Exercise31NewtonDirectionAtInitialPoint := by
  refine ⟨chapter03Exercise31Hessian_posDef.isUnit, ?_⟩
  -- Check the two Newton-system coordinates directly against the explicit gradient formula.
  ext i
  fin_cases i
  · norm_num [chapter03Exercise31Hessian, chapter03Exercise31NewtonDirectionAtInitialPoint,
      chapter03Exercise31InitialPoint, chapter03Exercise31Objective_gradient_eq]
  · norm_num [chapter03Exercise31Hessian, chapter03Exercise31NewtonDirectionAtInitialPoint,
      chapter03Exercise31InitialPoint, chapter03Exercise31Objective_gradient_eq]

/-- The Newton direction at `(-2, 4)` is the reported vector `(3, -3)`. -/
theorem chapter03Exercise31_newtonDirection :
    newtonDirection
        chapter03Exercise31Objective
        chapter03Exercise31InitialPoint
        (fun _ ↦ chapter03Exercise31Hessian) =
      chapter03Exercise31NewtonDirectionAtInitialPoint := by
  have hEq :
      chapter03Exercise31NewtonDirectionAtInitialPoint =
        newtonDirection
          chapter03Exercise31Objective
          chapter03Exercise31InitialPoint
          (fun _ ↦ chapter03Exercise31Hessian) := by
    exact
      (isNewtonDirectionAt_iff_eq_newtonDirection
          chapter03Exercise31Objective
          chapter03Exercise31InitialPoint
          (fun _ ↦ chapter03Exercise31Hessian)
          chapter03Exercise31Hessian_posDef.isUnit
          chapter03Exercise31NewtonDirectionAtInitialPoint).mp
        chapter03Exercise31_reported_newton_direction_is_newton_direction_at_initial
  simpa using hEq.symm

/-- The reported vector `(3, -3)` is a Newton direction for Exercise 3.1 at `(-2, 4)`. -/
theorem chapter03Exercise31_newtonDirection_solves :
    IsNewtonDirectionAt
      chapter03Exercise31Objective
      chapter03Exercise31InitialPoint
      (fun _ ↦ chapter03Exercise31Hessian)
      chapter03Exercise31NewtonDirectionAtInitialPoint :=
  chapter03Exercise31_reported_newton_direction_is_newton_direction_at_initial

/-- Chapter03 Exercise 3.1 (2): the Newton update from `(-2, 4)` reaches the minimizer `(1, 1)`
in one step. -/
theorem chapter03Exercise31_newtonMethod :
    newtonNextIterate
        chapter03Exercise31Objective
        chapter03Exercise31InitialPoint
        (fun _ ↦ chapter03Exercise31Hessian) =
      chapter03Exercise31Minimizer := by
  -- Replace the Newton update by `x + s` and use the explicit reported Newton direction.
  rw [newtonNextIterate_eq_add_direction, chapter03Exercise31_newtonDirection]
  ext i
  fin_cases i
  · norm_num [chapter03Exercise31InitialPoint, chapter03Exercise31NewtonDirectionAtInitialPoint,
      chapter03Exercise31Minimizer]
  · norm_num [chapter03Exercise31InitialPoint, chapter03Exercise31NewtonDirectionAtInitialPoint,
      chapter03Exercise31Minimizer]
