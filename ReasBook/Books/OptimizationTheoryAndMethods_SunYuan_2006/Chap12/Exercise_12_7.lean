/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.EqualityConstrainedProblem
import OptimizationTheoryAndMethods_SunYuan_2006.Chap12.Theorem_12_8_1

open Filter

section

local notation "Point" => LagrangeNewtonPoint 2
local notation "Multiplier" => LagrangeNewtonMultiplier 1
local notation "Reduced" => LagrangeNewtonPoint 1

-- Domain sampling for this refine pass:
-- * primary domain: Chapter 12 reduced-Hessian iterations for equality-constrained problems;
-- * sampled owner declarations:
--   `EqualityConstrainedProblem.constraintVector`,
--   `EqualityConstrainedProblem.constraintGradientMatrix`,
--   the single-constraint companion pattern from `Exercise_12_5`,
--   `IsReducedNullMap` and `IsReducedHessianStep` from `Theorem_12_8_1`,
--   `HasSuperlinearlyConvergentStep` from `Definition_12_3_extra_1`,
--   and mathlib's `=O[atTop]`;
-- * source-facing layer kept here: the concrete Exercise 12.7 objective, scalar constraint,
--   its denominator-safe domain, the iterate recursion, and the one-fast-one-slow convergence
--   conclusion;
-- * core/canonical layer reused here: the chapter owners `EqualityConstrainedProblem` and
--   `IsReducedHessianStep`, mathlib's `gradient`, and the standard gradient-matrix owner
--   `exercise127Problem.constraintGradientMatrix` viewed through `Matrix.toEuclideanLin`;
-- * primitive data vs derived API:
--   primitive/source data are the concrete objective, scalar equality constraint, denominator
--   domain, iterate recursion, and solution;
--   derived API are the concrete owner `exercise127Problem` and its single-constraint vector
--   and gradient-matrix views `exercise127Problem.constraintVector` and
--   `exercise127Problem.constraintGradientMatrix`;
-- * bridge/view layer here: the equality-constrained owner's canonical gradient matrix viewed
--   as a Euclidean linear map through `Matrix.toEuclideanLin`.

/-- The linear gap `x₂ - x₁` occurring repeatedly in the Exercise 12.7 formulas. -/
def exercise127LinearGap (x : Point) : ℝ :=
  x 1 - x 0

/-- The nonlinear gap `x₁ - x₂^2` occurring repeatedly in the Exercise 12.7 formulas. -/
def exercise127NonlinearGap (x : Point) : ℝ :=
  x 0 - (x 1) ^ (2 : ℕ)

/-- The objective function in Chapter 12 Exercise 12.7. -/
noncomputable def exercise127Objective (x : Point) : ℝ :=
  (1 / 2 : ℝ) * (x 1) ^ (2 : ℕ) - x 0 * x 1 +
    (1 / (6 * (1 - x 1) ^ (3 : ℕ))) *
      (-4 * (exercise127LinearGap x) ^ (3 : ℕ) -
        6 * (exercise127LinearGap x) ^ (2 : ℕ) * exercise127NonlinearGap x -
        12 * exercise127LinearGap x * (exercise127NonlinearGap x) ^ (2 : ℕ) -
        17 * (exercise127NonlinearGap x) ^ (3 : ℕ) +
        3 * (exercise127NonlinearGap x) ^ (4 : ℕ) / (1 - x 1))

/-- The equality constraint in Chapter 12 Exercise 12.7. -/
noncomputable def exercise127Constraint (x : Point) : ℝ :=
  x 0 +
    (1 / (1 - x 1) ^ (2 : ℕ)) *
      ((exercise127LinearGap x) ^ (2 : ℕ) +
        exercise127LinearGap x * exercise127NonlinearGap x +
        2 * (exercise127NonlinearGap x) ^ (2 : ℕ))

/-- Exercise 12.7 as the equality-constrained problem with objective `exercise127Objective`
and single equality constraint `exercise127Constraint`. -/
noncomputable def exercise127Problem : EqualityConstrainedProblem 2 1 where
  objective := exercise127Objective
  constraint := fun _ ↦ exercise127Constraint

/-- The source rational formulas of Exercise 12.7 are evaluated only on points with
`1 - x₂ ≠ 0`. -/
def exercise127DenominatorSafe (x : Point) : Prop :=
  x 1 ≠ 1

/-- A sequence in the Exercise 12.7 plane converges one-fast-one-slow to `xStar` when it
converges to `xStar` and the first-coordinate error is `O` of the square of the
second-coordinate error. -/
@[mk_iff hasOneFastOneSlowConvergenceTo_iff]
class HasOneFastOneSlowConvergenceTo (x : ℕ → Point) (xStar : Point) : Prop where
  tendsto : Tendsto x atTop (nhds xStar)
  first_isBigO_second_sq :
    (fun k ↦ |(x k - xStar) 0|) =O[atTop] fun k ↦ |(x k - xStar) 1| ^ (2 : ℕ)

/-- The unique constraint component of `exercise127Problem` is `exercise127Constraint`. -/
@[simp] theorem exercise127Problem_constraint_apply (x : Point) :
    exercise127Problem.constraint 0 x = exercise127Constraint x :=
  rfl

/-- The unique coordinate of `exercise127Problem.constraintVector x` is
`exercise127Constraint x`. -/
@[simp] theorem exercise127Problem_constraintVector_apply (x : Point) :
    exercise127Problem.constraintVector x 0 = exercise127Constraint x := by
  exact EqualityConstrainedProblem.constraintVector_apply exercise127Problem x 0

/-- The unique column of `exercise127Problem.constraintGradientMatrix x` is
`∇ exercise127Constraint x`. -/
@[simp] theorem exercise127Problem_constraintGradientMatrix_apply
    (x : Point) (row : Fin 2) :
    exercise127Problem.constraintGradientMatrix x row 0 =
      (gradient exercise127Constraint x) row := by
  exact EqualityConstrainedProblem.constraintGradientMatrix_apply
    exercise127Problem x row 0

/-- The single-column linearized constraint Jacobian `A(x)` for Exercise 12.7, viewed as a
continuous linear map `ℝ → ℝ²`. -/
noncomputable def exercise127ConstraintJacobian (x : Point) : Multiplier →L[ℝ] Point :=
  ((EuclideanSpace.proj 0 : Multiplier →L[ℝ] ℝ).smulRight
    (gradient exercise127Constraint x))

/-- For the single Exercise 12.7 equality constraint, `exercise127ConstraintJacobian x`
acts by multiplying `∇ exercise127Constraint x` with the unique multiplier coordinate. -/
@[simp] theorem exercise127ConstraintJacobian_apply
    (x : Point) (lam : Multiplier) :
    exercise127ConstraintJacobian x lam = lam 0 • gradient exercise127Constraint x :=
  rfl

/-- The Exercise 12.7 single-constraint Jacobian owner agrees with the chapter's canonical
gradient-matrix bridge for `exercise127Problem`. -/
theorem exercise127ConstraintJacobian_eq_constraintGradientMatrix (x : Point) :
    exercise127ConstraintJacobian x =
      (Matrix.toEuclideanLin
        (exercise127Problem.constraintGradientMatrix x)).toContinuousLinearMap :=
  by
    sorry

/-- The source initial point `(ε, ε)` for Exercise 12.7. -/
noncomputable def exercise127InitialPoint (ε : ℝ) : Point :=
  WithLp.toLp 2 ![ε, ε]

/-- The concrete iterate sequence obtained from the stage directions `d_k` by starting at
`exercise127InitialPoint ε` and updating via `x_(k+1) = x_k + d_k`. -/
noncomputable def exercise127Iterates (ε : ℝ) (d : ℕ → Point) : ℕ → Point
  | 0 => exercise127InitialPoint ε
  | k + 1 => exercise127Iterates ε d k + d k

/-- Unfolding `exercise127Iterates ε d` at stage `0` gives the source initial point `(ε, ε)`. -/
theorem exercise127Iterates_zero
    (ε : ℝ) (d : ℕ → Point) :
    exercise127Iterates ε d 0 = exercise127InitialPoint ε :=
  rfl

/-- Unfolding `exercise127Iterates ε d` at stage `k + 1` gives the update
`x_(k+1) = x_k + d_k`. -/
theorem exercise127Iterates_succ
    (ε : ℝ) (d : ℕ → Point) (k : ℕ) :
    exercise127Iterates ε d (k + 1) = exercise127Iterates ε d k + d k :=
  rfl

/-- The reported solution `(0, 0)` for Exercise 12.7. -/
noncomputable def exercise127Solution : Point :=
  WithLp.toLp 2 ![(0 : ℝ), 0]

#print axioms exercise127LinearGap
#print axioms exercise127NonlinearGap
#print axioms exercise127Objective
#print axioms exercise127Constraint
#print axioms exercise127Problem
#print axioms exercise127ConstraintJacobian
#print axioms exercise127InitialPoint
#print axioms exercise127Iterates
#print axioms exercise127Solution

/-- Chapter12 Exercise 12.7: there is a threshold `δ > 0` such that whenever
`0 < ε < δ`, there exist concrete stage directions `d_k`, reduced-Hessian operators `B_k`, and
reduced-space maps `Z_k` for the Exercise 12.7 process started from
`exercise127InitialPoint ε = (ε, ε)` such that each stage point `x_k` stays in the source
domain `x_k 1 ≠ 1` and each stage direction satisfies the chapter's canonical
`IsReducedHessianStep` owner specialized to the concrete equality-constrained owner
`exercise127Problem`, using the source-facing single-constraint Jacobian owner
`exercise127ConstraintJacobian` for the linearized constraint map, so the reduced-null-map
condition on each `Z_k` is carried by that canonical owner.
The induced iterate sequence `exercise127Iterates ε d` then converges to
`exercise127Solution = (0, 0)`, and the first coordinate error is `O` of the square of the
second coordinate error, expressed by `HasOneFastOneSlowConvergenceTo`. -/
theorem exercise127_twoSidedReducedHessianIterates_convergeOneFastOneSlow
    :
    ∃ δ > 0,
      ∀ ε : ℝ, 0 < ε → ε < δ →
        ∃ d : ℕ → Point,
          ∃ B : ℕ → Reduced →L[ℝ] Reduced,
            ∃ Z : ℕ → Reduced →L[ℝ] Point,
              (∀ k : ℕ,
                exercise127DenominatorSafe (exercise127Iterates ε d k) ∧
                  IsReducedHessianStep
                    (gradient exercise127Problem.objective (exercise127Iterates ε d k))
                    (exercise127ConstraintJacobian (exercise127Iterates ε d k))
                    (exercise127Problem.constraintVector (exercise127Iterates ε d k))
                    (B k)
                    (Z k)
                    (d k)) ∧
                HasOneFastOneSlowConvergenceTo
                  (exercise127Iterates ε d)
                  exercise127Solution := sorry

end
