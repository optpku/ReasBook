/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open Matrix

-- Chapter 7 already uses `solvesGaussNewtonNormalEquation` as the owner for normal-equation
-- satisfaction. For the damped system, the primitive data is the Jacobian and the right-hand side
-- vector `g`, while the residual-form equation is the least-squares specialization
-- `g = Jᵀ.mulVec r`.

section

variable {m n : ℕ}

local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ
local notation "GradientVector" => Fin n → ℝ
local notation "ResidualVector" => Fin m → ℝ
local notation "StepVector" => Fin n → ℝ

/-- Chapter07 Definition 7.3-extra-1: for a Jacobian matrix `J`, right-hand side vector `g`,
damping parameter `μ`, and step `s`, the Levenberg-Marquardt direction is characterized by the
regularized normal equation `(Jᵀ * J + μ • 1).mulVec s = -g`. In nonlinear least squares this is
specialized by `g = Jᵀ.mulVec r`. -/
def solvesLevenbergMarquardtNormalEquation
    (J : JacobianMatrix) (g : GradientVector) (μ : ℝ) (s : StepVector) : Prop :=
  (Jᵀ * J + μ • (1 : MatrixN)).mulVec s = -g

/-- Companion characterization of `solvesLevenbergMarquardtNormalEquation`. -/
@[simp] theorem solvesLevenbergMarquardtNormalEquation_iff
    (J : JacobianMatrix) (g : GradientVector) (μ : ℝ) (s : StepVector) :
    solvesLevenbergMarquardtNormalEquation J g μ s ↔
      (Jᵀ * J + μ • (1 : MatrixN)).mulVec s = -g :=
  Iff.rfl

/-- Least-squares specialization of `solvesLevenbergMarquardtNormalEquation` with
`g = Jᵀ.mulVec r`. -/
@[simp] theorem solvesLevenbergMarquardtNormalEquation_residual_iff
    (J : JacobianMatrix) (r : ResidualVector) (μ : ℝ) (s : StepVector) :
    solvesLevenbergMarquardtNormalEquation J (Jᵀ.mulVec r) μ s ↔
      (Jᵀ * J + μ • (1 : MatrixN)).mulVec s = -(Jᵀ.mulVec r) :=
  Iff.rfl

end
