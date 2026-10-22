/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_3_5

open Matrix

noncomputable section

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Semantic recall: `lean_leansearch` surfaced only generic nonlinear-operator results, so this
-- item keeps the source-facing Levenberg-Marquardt iteration directly on the local matrix and
-- Euclidean-space API already used elsewhere in Chapter 7.

/-- A candidate step `s_k` is accepted in Algorithm 7.4.1 exactly when it does not increase the
residual norm. -/
def levenbergMarquardtStepAccepted
    (r : Point → ResidualVector) (xk step : Point) : Prop :=
  ‖r (xk + step)‖ ≤ ‖r xk‖

/-- Unfolds the acceptance test from part (b) of Algorithm 7.4.1. -/
theorem levenbergMarquardtStepAccepted_iff
    (r : Point → ResidualVector) (xk step : Point) :
    levenbergMarquardtStepAccepted r xk step ↔ ‖r (xk + step)‖ ≤ ‖r xk‖ :=
  Iff.rfl

/-- Chapter07 Algorithm 7.4.1: a Levenberg-Marquardt iteration at `x_k` with trust-region radius
`Δ_k > 0` and positive definite diagonal scaling matrix `D_k` consists of a parameter `μ_k ≥ 0`,
a step `s_k`, the accepted or rejected next iterate `x_{k+1}`, a positive next trust-region
radius `Δ_{k+1} > 0`, and a next positive definite diagonal scaling matrix `D_{k+1}` such that
`((J x_k)ᵀ * J x_k + μ_k • D_k).mulVec s_k = -((J x_k)ᵀ.mulVec (r x_k))`, either `μ_k = 0` with
`‖D_k.mulVec s_k‖ ≤ Δ_k` or `0 < μ_k` with `‖D_k.mulVec s_k‖ = Δ_k`, and `x_{k+1}` is updated
according to the acceptance test `‖r (x_k + s_k)‖ ≤ ‖r x_k‖`. -/
structure LevenbergMarquardtIteration
    (r : Point → ResidualVector) (J : Point → JacobianMatrix)
    (xk : Point) (Δk : ℝ) (Dk : MatrixN) where
  mu : ℝ
  step : Point
  xNext : Point
  deltaNext : ℝ
  scalingMatrixNext : MatrixN
  delta_pos : 0 < Δk
  scalingMatrix_posDef : IsPositiveDefiniteDiagonalMatrix Dk
  mu_nonneg : 0 ≤ mu
  regularizedNormalEquation :
    (((J xk)ᵀ * J xk) + mu • Dk).mulVec step = -((J xk)ᵀ.mulVec (r xk))
  trustRegionCase :
    if mu = 0 then ‖Dk.mulVec step‖ ≤ Δk else ‖Dk.mulVec step‖ = Δk
  deltaNext_pos : 0 < deltaNext
  scalingMatrixNext_posDef : IsPositiveDefiniteDiagonalMatrix scalingMatrixNext
  acceptedUpdate :
    levenbergMarquardtStepAccepted r xk step → xNext = xk + step
  rejectedUpdate :
    ¬ levenbergMarquardtStepAccepted r xk step → xNext = xk

namespace LevenbergMarquardtIteration

variable {m n : ℕ}
variable {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {J : EuclideanSpace ℝ (Fin n) → Matrix (Fin m) (Fin n) ℝ}
variable {xk : EuclideanSpace ℝ (Fin n)} {Δk : ℝ} {Dk : Matrix (Fin n) (Fin n) ℝ}

/-- A Levenberg-Marquardt iteration coerces to its accepted or rejected next iterate `x_{k+1}`. -/
instance : CoeOut (LevenbergMarquardtIteration r J xk Δk Dk) (EuclideanSpace ℝ (Fin n)) where
  coe iter := iter.xNext

/-- `iter.Accepted` is the source acceptance test for the trial step `s_k`. -/
def Accepted (iter : LevenbergMarquardtIteration r J xk Δk Dk) : Prop :=
  levenbergMarquardtStepAccepted r xk iter.step

/-- `iter.Rejected` is the negation of the source acceptance test for the trial step `s_k`. -/
def Rejected (iter : LevenbergMarquardtIteration r J xk Δk Dk) : Prop :=
  ¬ iter.Accepted

/-- The Jacobian matrix used for the next iteration is obtained by evaluating `J` at `x_{k+1}`. -/
def nextJacobian
    (iter : LevenbergMarquardtIteration r J xk Δk Dk) : Matrix (Fin m) (Fin n) ℝ :=
  J iter.xNext

/-- The current scaling matrix `D_k` is positive definite diagonal in the Chapter 7 sense. -/
theorem currentScalingMatrix_posDef
    (iter : LevenbergMarquardtIteration r J xk Δk Dk) :
    IsPositiveDefiniteDiagonalMatrix Dk :=
  iter.scalingMatrix_posDef

/-- The next scaling matrix `D_(k + 1)` is positive definite diagonal in the Chapter 7 sense. -/
theorem nextScalingMatrix_posDef
    (iter : LevenbergMarquardtIteration r J xk Δk Dk) :
    IsPositiveDefiniteDiagonalMatrix iter.scalingMatrixNext :=
  iter.scalingMatrixNext_posDef

/-- Expanding `iter.Accepted` gives the source residual-norm comparison. -/
theorem accepted_iff (iter : LevenbergMarquardtIteration r J xk Δk Dk) :
    iter.Accepted ↔ ‖r (xk + iter.step)‖ ≤ ‖r xk‖ :=
  Iff.rfl

/-- Expanding `iter.Rejected` gives the negated source residual-norm comparison. -/
theorem rejected_iff (iter : LevenbergMarquardtIteration r J xk Δk Dk) :
    iter.Rejected ↔ ¬ ‖r (xk + iter.step)‖ ≤ ‖r xk‖ :=
  Iff.rfl

/-- If `μ_k = 0`, the source trust-region clause gives the interior-or-boundary inequality. -/
theorem scaledStepNorm_le_of_mu_eq_zero
    (iter : LevenbergMarquardtIteration r J xk Δk Dk) (hmu : iter.mu = 0) :
    ‖Dk.mulVec iter.step‖ ≤ Δk := by
  simpa [hmu] using iter.trustRegionCase

/-- If `μ_k ≠ 0`, the source trust-region clause forces the trial step onto the boundary. -/
theorem scaledStepNorm_eq_of_mu_ne_zero
    (iter : LevenbergMarquardtIteration r J xk Δk Dk) (hmu : iter.mu ≠ 0) :
    ‖Dk.mulVec iter.step‖ = Δk := by
  have hmu_ne_zero : iter.mu ≠ 0 := hmu
  simpa [if_neg hmu_ne_zero] using iter.trustRegionCase

/-- If the residual norm decreases, Algorithm 7.4.1 accepts the candidate step. -/
theorem xNext_eq_of_accepted
    (iter : LevenbergMarquardtIteration r J xk Δk Dk)
    (haccept : iter.Accepted) :
    iter.xNext = xk + iter.step :=
  iter.acceptedUpdate haccept

/-- If the residual norm does not decrease, Algorithm 7.4.1 rejects the candidate step. -/
theorem xNext_eq_of_rejected
    (iter : LevenbergMarquardtIteration r J xk Δk Dk)
    (hreject : iter.Rejected) :
    iter.xNext = xk :=
  iter.rejectedUpdate hreject

/-- If the residual norm decreases, the next Jacobian is `J (x_k + s_k)`. -/
theorem nextJacobian_eq_of_accepted
    (iter : LevenbergMarquardtIteration r J xk Δk Dk)
    (haccept : iter.Accepted) :
    iter.nextJacobian = J (xk + iter.step) :=
  congrArg J (xNext_eq_of_accepted iter haccept)

/-- If the residual norm does not decrease, the next Jacobian remains `J x_k`. -/
theorem nextJacobian_eq_of_rejected
    (iter : LevenbergMarquardtIteration r J xk Δk Dk)
    (hreject : iter.Rejected) :
    iter.nextJacobian = J xk :=
  congrArg J (xNext_eq_of_rejected iter hreject)

end LevenbergMarquardtIteration

end
