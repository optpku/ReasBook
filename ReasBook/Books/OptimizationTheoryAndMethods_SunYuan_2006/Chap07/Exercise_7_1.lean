/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_1_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_3_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

open Matrix

section

-- Domain sampling:
-- * primary domain: finite-dimensional nonlinear least-squares Gauss-Newton and
--   Levenberg-Marquardt updates;
-- * sampled owners reused here: `nonlinearLeastSquaresObjective`, `residualJacobianMatrix`,
--   `solvesGaussNewtonNormalEquation`, `solvesLevenbergMarquardtNormalEquation`;
-- * core/canonical owner abstraction: the Chapter 7 normal-equation predicates, with the
--   source-facing Levenberg-Marquardt exercise data restricted to the positive damping domain;
-- * primitive data kept here: the concrete residual map, initial point, and the explicit
--   Gauss-Newton and Levenberg-Marquardt steps for Exercise 7.1.

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin 2)
local notation "JacobianMatrix" => Matrix (Fin 2) (Fin 2) ℝ

/-- The residual map `r(x) = (x 1 - (x 0)^2, 1 - x 0)` for the Exercise 7.1 least-squares
problem. -/
def exercise71Residual (x : Point) : ResidualVector :=
  WithLp.toLp 2 <| ![x 1 - (x 0) ^ (2 : ℕ), 1 - x 0]

/-- The source starting point `x^(0) = (0, 0)ᵀ` for Exercise 7.1. -/
def exercise71InitialPoint : Point :=
  WithLp.toLp 2 <| ![(0 : ℝ), 0]

/-- The explicit Gauss-Newton step chosen at `exercise71InitialPoint`. -/
def exercise71GaussNewtonStep : Point :=
  WithLp.toLp 2 <| ![(1 : ℝ), 0]

/-- The first Gauss-Newton iterate obtained from `exercise71InitialPoint`. -/
def exercise71GaussNewtonFirstIterate : Point :=
  exercise71InitialPoint + exercise71GaussNewtonStep

/-- The explicit second Gauss-Newton step taken from `exercise71GaussNewtonFirstIterate`. -/
def exercise71GaussNewtonSecondStep : Point :=
  WithLp.toLp 2 <| ![(0 : ℝ), 1]

/-- The second Gauss-Newton iterate obtained from `exercise71InitialPoint`. -/
def exercise71GaussNewtonSecondIterate : Point :=
  exercise71GaussNewtonFirstIterate + exercise71GaussNewtonSecondStep

/-- The explicit Levenberg-Marquardt step with positive damping parameter `μ` at
`exercise71InitialPoint`. -/
noncomputable def exercise71LevenbergMarquardtStep (μ : Set.Ioi (0 : ℝ)) : Point :=
  WithLp.toLp 2 <| ![(1 / (1 + μ) : ℝ), 0]

/-- The first Levenberg-Marquardt iterate obtained from `exercise71InitialPoint` with positive
damping parameter `μ`. -/
noncomputable def exercise71LevenbergMarquardtFirstIterate (μ : Set.Ioi (0 : ℝ)) : Point :=
  exercise71InitialPoint + exercise71LevenbergMarquardtStep μ

/-- Helper for Chapter07 Exercise 7.1: applying the canonical Jacobian matrix is the same as
applying the Fréchet derivative of the residual map. -/
private theorem residualJacobian_apply_eq_fderiv
    (r : Point → ResidualVector) (x v : Point) :
    Matrix.toEuclideanLin (residualJacobianMatrix r x) v = fderiv ℝ r x v := by
  have hToLin :
      Matrix.toLin
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (residualJacobianMatrix r x) v =
        (fderiv ℝ r x).toLinearMap v := by
    -- Reconstruct the derivative map from its matrix in the standard Euclidean bases.
    exact
      congrArg
        (fun L : Point →ₗ[ℝ] ResidualVector ↦ L v)
        (Matrix.toLin_toMatrix
          (v₁ := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
          (v₂ := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
          ((fderiv ℝ r x).toLinearMap))
  simpa [Matrix.toEuclideanLin_eq_toLin_orthonormal] using hToLin

/-- Helper for Chapter07 Exercise 7.1: the residual map has derivative
`v ↦ (-2 * x 0 * v 0 + v 1, -v 0)`. -/
private theorem exercise71Residual_hasFDerivAt (x : Point) :
    HasFDerivAt exercise71Residual
      (Matrix.toEuclideanLin !![-(2 * x 0), (1 : ℝ); -(1 : ℝ), (0 : ℝ)]).toContinuousLinearMap x := by
  let D : Point →L[ℝ] ResidualVector :=
    (Matrix.toEuclideanLin !![-(2 * x 0), (1 : ℝ); -(1 : ℝ), (0 : ℝ)]).toContinuousLinearMap
  let rho : Point → Fin 2 → ℝ := fun y ↦ ![y 1 - (y 0) ^ (2 : ℕ), 1 - y 0]
  let iso : ResidualVector ≃L[ℝ] (Fin 2 → ℝ) :=
    PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)
  let coord0 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 0
  let coord1 : Point →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 2 => ℝ) 1
  have firstCoordinateSquare_hasFDerivAt :
      HasFDerivAt
        (fun y : Point ↦ (y 0) ^ (2 : ℕ))
        (((2 : ℝ) * x 0) • coord0)
        x := by
    have hy0 : HasFDerivAt (fun y : Point ↦ y 0) coord0 x := by
      -- The first coordinate projection is a continuous linear functional.
      simpa [coord0] using (PiLp.hasFDerivAt_apply (p := 2) x 0)
    have hmul :
        HasFDerivAt
          (fun y : Point ↦ y 0 * y 0)
          (x 0 • coord0 + x 0 • coord0)
          x := by
      -- Differentiate the coordinate square as a product before normalizing its spelling.
      exact hy0.mul hy0
    -- Route correction: isolate the square derivative before re-entering the packaged `pi`
    -- derivative proof.
    convert hmul using 1
    · ext y
      rw [pow_two]
    · ext v
      simp [coord0, two_mul, add_smul]
  have firstResidualCoordinate_hasFDerivAt :
      HasFDerivAt
        ((fun y : Point ↦ y 1) - fun y : Point ↦ (y 0) ^ (2 : ℕ))
        (coord1 - (((2 : ℝ) * x 0) • coord0))
        x := by
    have hy1 : HasFDerivAt (fun y : Point ↦ y 1) coord1 x := by
      -- The second coordinate projection is the other canonical continuous linear functional.
      simpa [coord1] using (PiLp.hasFDerivAt_apply (p := 2) x 1)
    -- Reassemble the first residual coordinate directly as a difference to stay in the same
    -- instance-normal form as the square derivative helper.
    exact hy1.sub firstCoordinateSquare_hasFDerivAt
  have hproj0 :
      (ContinuousLinearMap.proj 0).comp ((iso : ResidualVector →L[ℝ] (Fin 2 → ℝ)).comp D) =
        coord1 - (((2 : ℝ) * x 0) • coord0) := by
    -- Compare the packaged derivative with the first coordinate formula.
    ext v
    have hv0 : vecHead v.ofLp = v 0 := rfl
    have hv1 : vecHead (vecTail v.ofLp) = v 1 := rfl
    simp [D, iso, coord0, coord1, hv0, hv1, Matrix.toEuclideanLin_apply]
    ring
  have hproj1 :
      (ContinuousLinearMap.proj 1).comp ((iso : ResidualVector →L[ℝ] (Fin 2 → ℝ)).comp D) =
        -coord0 := by
    -- The second coordinate is the linear form `v ↦ -v 0`.
    ext v
    have hv0 : vecHead v.ofLp = v 0 := rfl
    simp [D, iso, coord0, hv0, Matrix.toEuclideanLin_apply]
  have hrho : HasFDerivAt rho ((iso : ResidualVector →L[ℝ] (Fin 2 → ℝ)).comp D) x := by
    -- Differentiate the two residual coordinates separately.
    rw [hasFDerivAt_pi']
    intro i
    fin_cases i
    · -- Route correction: consume the named first-coordinate derivative instead of re-normalizing
      -- the square derivative inside this `fin_cases` branch.
      refine (firstResidualCoordinate_hasFDerivAt.congr_fderiv hproj0.symm).congr_of_eventuallyEq ?_
      filter_upwards with y
      simp [rho]
    · have hy0 : HasFDerivAt (fun y : Point ↦ y 0) coord0 x := by
        simpa [coord0] using (PiLp.hasFDerivAt_apply (p := 2) x 0)
      -- The second residual coordinate is `1 - y 0`.
      simpa [rho, hproj1, sub_eq_add_neg, add_comm] using hy0.neg.const_add (1 : ℝ)
  -- Transfer the coordinate derivative back across the Euclidean-space equivalence.
  exact (iso.comp_hasFDerivAt_iff (f := exercise71Residual) (x := x) (f' := D)).mp <|
    by simpa [exercise71Residual, rho, iso, D] using hrho

/-- Helper for Chapter07 Exercise 7.1: `leastSquaresGradient` is the coordinate vector
`(J(x)ᵀ).mulVec r(x)`. -/
private lemma leastSquaresGradient_eq_coordinate
    (r : Point → ResidualVector) (x : Point) :
    leastSquaresGradient r x =
      WithLp.toLp 2 (((residualJacobianMatrix r x)ᵀ).mulVec (r x).ofLp) := by
  -- Unpack the Euclidean matrix action into the concrete `mulVec` formula.
  simpa [leastSquaresGradient] using
    (Matrix.toEuclideanLin_apply ((residualJacobianMatrix r x)ᵀ) (r x))

/-- Helper for Chapter07 Exercise 7.1: the Gauss-Newton normal equation is equivalent to the
coordinate `mulVec` equation. -/
private lemma solvesGaussNewtonNormalEquation_iff_coordinate
    (r : Point → ResidualVector) (xk xNext : Point) :
    solvesGaussNewtonNormalEquation r xk xNext ↔
      (gaussNewtonNormalMatrix r xk).mulVec (xNext - xk).ofLp =
        -(leastSquaresGradient r xk).ofLp := by
  -- Transport the point-valued normal equation through `WithLp.ofLp`.
  rw [solvesGaussNewtonNormalEquation_iff, leastSquaresGradient_eq_coordinate]
  constructor
  · intro h
    simpa [Matrix.toEuclideanLin_apply] using congrArg (WithLp.ofLp) h
  · intro h
    apply WithLp.ofLp_injective 2
    simpa [Matrix.toEuclideanLin_apply] using h

/-- Helper for Chapter07 Exercise 7.1: a `2 × 2` matrix acts on `![u, v]` by the expected
coordinate formulas. -/
private theorem twoByTwoMulVec
    (a b c d u v : ℝ) :
    (!![a, b; c, d] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![u, v] =
      ![a * u + b * v, c * u + d * v] := by
  -- Expand the `Fin 2` matrix-vector product once so the theorem-local arithmetic stays small.
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- Expanding the canonical Chapter 7 nonlinear least-squares objective for `exercise71Residual`
gives the source formula `(1 / 2) * ((x 1 - (x 0)^2)^2 + (1 - x 0)^2)`. -/
theorem exercise71Objective_eq (x : Point) :
    nonlinearLeastSquaresObjective exercise71Residual x =
      (1 / 2 : ℝ) * ((x 1 - (x 0) ^ (2 : ℕ)) ^ (2 : ℕ) + (1 - x 0) ^ (2 : ℕ)) := by
  -- Rewrite the canonical least-squares objective into the two explicit residual coordinates.
  simpa [exercise71Residual, Fin.sum_univ_two] using
    nonlinearLeastSquaresObjective_eq_half_sum exercise71Residual x

/-- The canonical Jacobian owner for `exercise71Residual` has the source matrix formula
`J(x) = [[-2 * x 0, 1], [-1, 0]]`. -/
theorem exercise71Residual_jacobian_eq (x : Point) :
    residualJacobianMatrix exercise71Residual x =
      !![-(2 * x 0), (1 : ℝ); -(1 : ℝ), (0 : ℝ)] := by
  -- Compare both matrices through their Euclidean linear actions.
  let D : Point →L[ℝ] ResidualVector :=
    (Matrix.toEuclideanLin !![-(2 * x 0), (1 : ℝ); -(1 : ℝ), (0 : ℝ)]).toContinuousLinearMap
  apply Matrix.toEuclideanLin.injective
  ext v i
  have hcalc :
      Matrix.toEuclideanLin (residualJacobianMatrix exercise71Residual x) v =
        (Matrix.toEuclideanLin !![-(2 * x 0), (1 : ℝ); -(1 : ℝ), (0 : ℝ)]) v := by
    calc
      Matrix.toEuclideanLin (residualJacobianMatrix exercise71Residual x) v
          = fderiv ℝ exercise71Residual x v := by
              simpa using residualJacobian_apply_eq_fderiv exercise71Residual x v
      _ = D v := by
            rw [(exercise71Residual_hasFDerivAt x).fderiv]
      _ = (Matrix.toEuclideanLin !![-(2 * x 0), (1 : ℝ); -(1 : ℝ), (0 : ℝ)]) v := by
            rfl
  exact congrArg (fun z : ResidualVector ↦ z i) hcalc

/-- The first Gauss-Newton iterate satisfies the canonical Gauss-Newton normal equation at
`exercise71InitialPoint`. -/
theorem exercise71GaussNewtonFirstIterate_solvesNormalEquation :
    solvesGaussNewtonNormalEquation exercise71Residual exercise71InitialPoint
      exercise71GaussNewtonFirstIterate := by
  have hJ0 :
      residualJacobianMatrix exercise71Residual exercise71InitialPoint =
        !![(0 : ℝ), (1 : ℝ); -(1 : ℝ), (0 : ℝ)] := by
    -- Evaluate the explicit Jacobian formula at the zero initial point.
    simpa [exercise71InitialPoint] using exercise71Residual_jacobian_eq exercise71InitialPoint
  have hgrad0 :
      leastSquaresGradient exercise71Residual exercise71InitialPoint =
        WithLp.toLp 2 ![(-1 : ℝ), 0] := by
    -- Multiply the initial Jacobian transpose by the initial residual vector.
    rw [leastSquaresGradient_eq_coordinate, hJ0]
    ext i
    fin_cases i <;>
      simp [exercise71Residual, exercise71InitialPoint, Matrix.mulVec, Fin.sum_univ_two]
  have hstep :
      (exercise71GaussNewtonFirstIterate - exercise71InitialPoint).ofLp = ![(1 : ℝ), 0] := by
    -- The first iterate differs from the initial point by the explicit step `(1, 0)`.
    ext i
    fin_cases i <;>
      simp [exercise71GaussNewtonFirstIterate, exercise71InitialPoint, exercise71GaussNewtonStep]
  have hA0 :
      gaussNewtonNormalMatrix exercise71Residual exercise71InitialPoint =
        (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    -- The initial Gauss-Newton normal matrix is the identity.
    rw [gaussNewtonNormalMatrix_eq, hJ0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hA0step : ((1 : Matrix (Fin 2) (Fin 2) ℝ)).mulVec ![(1 : ℝ), 0] = ![(1 : ℝ), 0] := by
    -- The identity matrix fixes the explicit first Gauss-Newton step.
    ext i
    fin_cases i <;>
      norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.one_apply]
  have hneggrad0 : -(![(-1 : ℝ), 0] : Fin 2 → ℝ) = ![(1 : ℝ), 0] := by
    ext i
    fin_cases i <;> norm_num
  -- After the coordinate rewrite, the normal equation is a direct `2 × 2` computation.
  rw [solvesGaussNewtonNormalEquation_iff_coordinate, hstep, hgrad0, hA0]
  -- The rewritten coordinate equation is exactly the explicit identity-matrix computation above.
  simpa [hneggrad0] using hA0step

/-- The first Gauss-Newton iterate for the Exercise 7.1 least-squares objective from
`x^(0) = (0, 0)ᵀ` is `(1, 0)ᵀ`. -/
theorem exercise71GaussNewtonFirstIterate_eq :
    exercise71GaussNewtonFirstIterate = (WithLp.toLp 2 <| ![(1 : ℝ), 0]) := by
  -- The first iterate is just the starting point plus the explicit first step.
  ext i
  fin_cases i <;>
    simp [exercise71GaussNewtonFirstIterate, exercise71InitialPoint, exercise71GaussNewtonStep]

/-- The second Gauss-Newton iterate satisfies the canonical Gauss-Newton normal equation at
`exercise71GaussNewtonFirstIterate`. -/
theorem exercise71GaussNewtonSecondIterate_solvesNormalEquation :
    solvesGaussNewtonNormalEquation exercise71Residual exercise71GaussNewtonFirstIterate
      exercise71GaussNewtonSecondIterate := by
  have hJ1 :
      residualJacobianMatrix exercise71Residual exercise71GaussNewtonFirstIterate =
        !![(-2 : ℝ), (1 : ℝ); -(1 : ℝ), (0 : ℝ)] := by
    -- Rewrite the base point to `(1, 0)` before evaluating the Jacobian formula.
    rw [exercise71GaussNewtonFirstIterate_eq]
    simpa using exercise71Residual_jacobian_eq (WithLp.toLp 2 ![(1 : ℝ), 0])
  have hJ1' :
      residualJacobianMatrix exercise71Residual (WithLp.toLp 2 ![(1 : ℝ), 0]) =
        !![(-2 : ℝ), (1 : ℝ); -(1 : ℝ), (0 : ℝ)] := by
    simpa using exercise71Residual_jacobian_eq (WithLp.toLp 2 ![(1 : ℝ), 0])
  have hgrad1 :
      leastSquaresGradient exercise71Residual exercise71GaussNewtonFirstIterate =
        WithLp.toLp 2 ![(2 : ℝ), -1] := by
    -- Multiply `J(1,0)ᵀ` by the residual vector at `(1,0)`.
    rw [exercise71GaussNewtonFirstIterate_eq, leastSquaresGradient_eq_coordinate, hJ1']
    ext i
    fin_cases i <;>
      simp [exercise71Residual, Matrix.mulVec, Fin.sum_univ_two]
  have hstep :
      (exercise71GaussNewtonSecondIterate - exercise71GaussNewtonFirstIterate).ofLp =
        ![(0 : ℝ), 1] := by
    -- The second iterate adds the explicit second step `(0, 1)`.
    ext i
    fin_cases i <;>
      simp [exercise71GaussNewtonSecondIterate, exercise71GaussNewtonFirstIterate,
        exercise71GaussNewtonSecondStep]
  have hA1 :
      gaussNewtonNormalMatrix exercise71Residual exercise71GaussNewtonFirstIterate =
        !![(5 : ℝ), (-2 : ℝ); (-2 : ℝ), (1 : ℝ)] := by
    -- Multiply `J(1,0)ᵀ` and `J(1,0)` coordinatewise to get the explicit Gram matrix.
    rw [gaussNewtonNormalMatrix_eq, hJ1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  have hA1step :
      (!![(5 : ℝ), (-2 : ℝ); (-2 : ℝ), (1 : ℝ)] : Matrix (Fin 2) (Fin 2) ℝ).mulVec ![(0 : ℝ), 1] =
        ![(-2 : ℝ), 1] := by
    -- Apply the shared `2 × 2` normal form to the explicit second step.
    simpa using twoByTwoMulVec (5 : ℝ) (-2 : ℝ) (-2 : ℝ) (1 : ℝ) (0 : ℝ) (1 : ℝ)
  have hneggrad1 : -(![(2 : ℝ), -1] : Fin 2 → ℝ) = ![(-2 : ℝ), 1] := by
    ext i
    fin_cases i <;> norm_num
  -- The second normal equation is again a direct coordinate computation.
  rw [solvesGaussNewtonNormalEquation_iff_coordinate, hstep, hgrad1, hA1]
  -- The rewritten equation is exactly the explicit matrix-vector product computed above.
  simpa [hneggrad1] using hA1step

/-- Chapter07 Exercise 7.1 (1): starting from `x^(0) = (0, 0)ᵀ`, two Gauss-Newton steps reach
the minimizer `(1, 1)ᵀ`. -/
theorem exercise71GaussNewtonSecondIterate_eq :
    exercise71GaussNewtonSecondIterate = (WithLp.toLp 2 <| ![(1 : ℝ), 1]) := by
  -- The second iterate is the first explicit iterate plus the second explicit step.
  ext i
  fin_cases i <;>
    simp [exercise71GaussNewtonSecondIterate, exercise71GaussNewtonFirstIterate_eq,
      exercise71GaussNewtonSecondStep]

/-- The second Gauss-Newton iterate attains objective value `0`. -/
theorem exercise71GaussNewtonSecondIterate_objective_eq_zero :
    nonlinearLeastSquaresObjective exercise71Residual exercise71GaussNewtonSecondIterate = 0 :=
  by
  -- Rewrite the iterate and the objective into the textbook coordinates and simplify.
  rw [exercise71GaussNewtonSecondIterate_eq, exercise71Objective_eq]
  norm_num

/-- The explicit vector `exercise71LevenbergMarquardtStep μ` satisfies the canonical
Levenberg-Marquardt normal equation at `exercise71InitialPoint` for every damping parameter
`μ ∈ Set.Ioi 0`. -/
theorem exercise71LevenbergMarquardtStep_solvesNormalEquation
    (μ : Set.Ioi (0 : ℝ)) :
    solvesLevenbergMarquardtNormalEquation
      (residualJacobianMatrix exercise71Residual exercise71InitialPoint)
      (leastSquaresGradient exercise71Residual exercise71InitialPoint)
      μ
      (exercise71LevenbergMarquardtStep μ) := by
  have hJ0 :
      residualJacobianMatrix exercise71Residual exercise71InitialPoint =
        !![(0 : ℝ), (1 : ℝ); -(1 : ℝ), (0 : ℝ)] := by
    -- Reuse the explicit Jacobian formula at the initial point.
    simpa [exercise71InitialPoint] using exercise71Residual_jacobian_eq exercise71InitialPoint
  have hgrad0 :
      leastSquaresGradient exercise71Residual exercise71InitialPoint =
        WithLp.toLp 2 ![(-1 : ℝ), 0] := by
    -- Reuse the initial gradient computation from the first Gauss-Newton step.
    rw [leastSquaresGradient_eq_coordinate, hJ0]
    ext i
    fin_cases i <;>
      simp [exercise71Residual, exercise71InitialPoint, Matrix.mulVec, Fin.sum_univ_two]
  have hμne : (1 + (μ : ℝ)) ≠ 0 := by
    -- The damping parameter is positive, so the denominator is nonzero.
    have hμpos : 0 < (μ : ℝ) := μ.2
    nlinarith
  have hAμ :
      (residualJacobianMatrix exercise71Residual exercise71InitialPoint)ᵀ *
          residualJacobianMatrix exercise71Residual exercise71InitialPoint +
        (μ : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) =
          !![(1 + (μ : ℝ) : ℝ), (0 : ℝ); (0 : ℝ), 1 + (μ : ℝ)] := by
    -- The regularized initial normal matrix is diagonal with entries `1 + μ`.
    rw [hJ0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hAμstep :
      (!![(1 + (μ : ℝ) : ℝ), (0 : ℝ); (0 : ℝ), 1 + (μ : ℝ)] :
          Matrix (Fin 2) (Fin 2) ℝ).mulVec (exercise71LevenbergMarquardtStep μ).ofLp =
        ![(1 : ℝ), 0] := by
    -- Expand the damped step and reduce the diagonal matrix action to one scalar identity.
    rw [exercise71LevenbergMarquardtStep]
    rw [twoByTwoMulVec]
    ext i
    fin_cases i
    · field_simp [hμne]
      ring_nf
    · simp
  have hneggrad0coord : -(![(-1 : ℝ), 0] : Fin 2 → ℝ) = ![(1 : ℝ), 0] := by
    ext i
    fin_cases i <;> norm_num
  -- After expanding the regularized normal matrix, only the first coordinate needs a scalar solve.
  rw [solvesLevenbergMarquardtNormalEquation_iff, hgrad0, hAμ]
  -- The final damped normal equation is the explicit diagonal solve computed above.
  simpa [exercise71LevenbergMarquardtStep, hneggrad0coord] using hAμstep

/-- Chapter07 Exercise 7.1 (2): for positive damping parameter `μ`, the first
Levenberg-Marquardt iterate from `x^(0) = (0, 0)ᵀ` is `(1 / (1 + μ), 0)ᵀ`. -/
theorem exercise71LevenbergMarquardtFirstIterate_eq (μ : Set.Ioi (0 : ℝ)) :
    exercise71LevenbergMarquardtFirstIterate μ =
      (WithLp.toLp 2 <| ![(1 / (1 + μ) : ℝ), 0]) := by
  -- The first Levenberg-Marquardt iterate adds the explicit damped step to the zero start.
  ext i
  fin_cases i <;>
    simp [exercise71LevenbergMarquardtFirstIterate, exercise71InitialPoint,
      exercise71LevenbergMarquardtStep]

end
