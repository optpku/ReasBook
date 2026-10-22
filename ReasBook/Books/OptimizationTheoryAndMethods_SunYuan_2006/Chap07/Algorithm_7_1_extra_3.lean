/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_2_2

noncomputable section

open Matrix

section

variable {m n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "Residual" => EuclideanSpace ℝ (Fin m)

-- Semantic recall: the source-facing Newton update belongs on top of the Chapter 7 least-squares
-- owners from `Theorem_7_2_2`, rather than duplicating their calculus definitions locally.

/-- Chapter07 Algorithm 7.1-extra-3: for the nonlinear least-squares problem `(7.1.1)` with
residual map `r`, the Newton update at `x` is `x - G(x)⁻¹ g(x)`, where
`g(x) = leastSquaresGradient r x = J(x)ᵀ r(x)` and
`G(x) = leastSquaresHessianMatrix r x = J(x)ᵀ * J(x) + S(x)` with
`S(x) = leastSquaresCorrectionMatrix r x`. -/
def nonlinearLeastSquaresNewtonStep
    (r : Point → Residual) (x : Point)
    [Invertible (leastSquaresHessianMatrix r x)] : Point :=
  x - Matrix.toEuclideanLin (⅟ (leastSquaresHessianMatrix r x)) (leastSquaresGradient r x)

/-- Unfolds `nonlinearLeastSquaresNewtonStep` through the canonical least-squares Hessian and
gradient owners. -/
theorem nonlinearLeastSquaresNewtonStep_eq
    (r : Point → Residual) (x : Point)
    [Invertible (leastSquaresHessianMatrix r x)] :
    nonlinearLeastSquaresNewtonStep r x =
      x - Matrix.toEuclideanLin (⅟ (leastSquaresHessianMatrix r x)) (leastSquaresGradient r x) :=
  rfl

/-- Expands `nonlinearLeastSquaresNewtonStep` as the matrix Newton update
`x - G(x)⁻¹ J(x)ᵀ r(x)` with `G(x) = leastSquaresHessianMatrix r x = J(x)ᵀ * J(x) + S(x)` and
`S(x) = leastSquaresCorrectionMatrix r x`. -/
theorem nonlinearLeastSquaresNewtonStep_def
    (r : Point → Residual) (x : Point)
    [Invertible (leastSquaresHessianMatrix r x)] :
    nonlinearLeastSquaresNewtonStep r x =
      x -
        Matrix.toEuclideanLin
          (⅟ (leastSquaresHessianMatrix r x))
          (Matrix.toEuclideanLin
            ((residualJacobianMatrix r x)ᵀ)
            (r x)) := by
  rfl

end
