/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2.DifferentialData

noncomputable section

open Matrix
open scoped LeastSquares
open scoped Matrix.Norms.L2Operator

section

variable {m n : ℕ}

/-- The Gauss-Newton normal matrix `J(x)ᵀ * J(x)` attached to the residual map `r`. -/
def gaussNewtonNormalMatrix (r : Point n → Residual m) (x : Point n) : MatrixN n :=
  (J[r](x))ᵀ * J[r](x)

/-- Unfolding formula for `gaussNewtonNormalMatrix`. -/
theorem gaussNewtonNormalMatrix_eq (r : Point n → Residual m) (x : Point n) :
    gaussNewtonNormalMatrix r x = (J[r](x))ᵀ * J[r](x) :=
  rfl

/-- `solvesGaussNewtonNormalEquation r xk xNext` means that the increment `xNext - xk` satisfies
the Gauss-Newton normal equation `J(x_k)ᵀ J(x_k) (x_(k+1) - x_k) = -J(x_k)ᵀ r(x_k)`. -/
def solvesGaussNewtonNormalEquation
    (r : Point n → Residual m) (xk xNext : Point n) : Prop :=
  (gaussNewtonNormalMatrix r xk).toEuclideanLin (xNext - xk) =
    -g[r](xk)

/-- Unfolding formula for `solvesGaussNewtonNormalEquation`. -/
theorem solvesGaussNewtonNormalEquation_iff
    (r : Point n → Residual m) (xk xNext : Point n) :
    solvesGaussNewtonNormalEquation r xk xNext ↔
      (gaussNewtonNormalMatrix r xk).toEuclideanLin (xNext - xk) = -g[r](xk) :=
  Iff.rfl

/-- The source linear coefficient `‖(J(x*)ᵀ J(x*))⁻¹‖ * ‖S(x*)‖` in the one-step Gauss-Newton
error estimate, with both matrix norms taken in the Euclidean (`ℓ₂`) operator norm. -/
def gaussNewtonLinearErrorCoefficient (r : Point n → Residual m) (xStar : Point n) : ℝ :=
  ‖(gaussNewtonNormalMatrix r xStar)⁻¹‖ * ‖S[r](xStar)‖

/-- Unfolding formula for `gaussNewtonLinearErrorCoefficient`. -/
theorem gaussNewtonLinearErrorCoefficient_eq
    (r : Point n → Residual m) (xStar : Point n) :
    gaussNewtonLinearErrorCoefficient r xStar =
      ‖(gaussNewtonNormalMatrix r xStar)⁻¹‖ * ‖S[r](xStar)‖ :=
  rfl

/-- If the residual vanishes at `xStar`, then the source linear coefficient in the one-step
Gauss-Newton estimate is `0`. -/
theorem gaussNewtonLinearErrorCoefficient_eq_zero_of_residual_eq_zero
    (r : Point n → Residual m) (xStar : Point n) (hResidualZero : r xStar = 0) :
    gaussNewtonLinearErrorCoefficient r xStar = 0 := by
  rw [gaussNewtonLinearErrorCoefficient_eq]
  simp [leastSquaresCorrectionMatrix_eq_zero_of_residual_eq_zero, hResidualZero]

end
