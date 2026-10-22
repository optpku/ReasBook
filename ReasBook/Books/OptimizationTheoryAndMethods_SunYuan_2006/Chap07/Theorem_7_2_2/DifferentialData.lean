/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.ToLin
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Definition_7_1_extra_1

noncomputable section

open Matrix
open scoped BigOperators

/-- The ambient Euclidean parameter space `ℝ^n` for the Chapter 7 least-squares residual map. -/
abbrev Point (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- The ambient Euclidean residual space `ℝ^m` for the Chapter 7 least-squares setup. -/
abbrev Residual (m : ℕ) := EuclideanSpace ℝ (Fin m)

/-- The real square `n × n` matrix type used by the Chapter 7 Gauss-Newton Hessian formulas. -/
abbrev MatrixN (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The standard coordinate equivalence on the residual space `Residual m`. -/
noncomputable abbrev residualCoords (m : ℕ) := EuclideanSpace.equiv (Fin m) ℝ

section

variable {m n : ℕ}

/-- The Jacobian matrix `J(x)` of the residual map `r` in the standard Euclidean bases. -/
abbrev residualJacobianMatrix
    (r : Point n → Residual m) (x : Point n) : Matrix (Fin m) (Fin n) ℝ :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin m) ℝ).toBasis
    (fderiv ℝ r x).toLinearMap

/-- The least-squares gradient `J(x)ᵀ r(x)` encoded on `EuclideanSpace ℝ (Fin n)`. -/
def leastSquaresGradient (r : Point n → Residual m) (x : Point n) : Point n :=
  ((residualJacobianMatrix r x)ᵀ).toEuclideanLin (r x)

/-- The Hessian matrix of the scalar residual coordinate `x ↦ r_i(x)` in the standard Euclidean
basis. -/
abbrev residualCoordinateHessianMatrix
    (r : Point n → Residual m) (i : Fin m) (x : Point n) : MatrixN n :=
  LinearMap.toMatrix
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
    (fderiv ℝ (gradient (fun y : Point n ↦ residualCoords m (r y) i)) x).toLinearMap

/-- The least-squares correction matrix `S(x) = ∑ i, r_i(x) • ∇² r_i(x)`. -/
def leastSquaresCorrectionMatrix (r : Point n → Residual m) (x : Point n) : MatrixN n :=
  ∑ i : Fin m, residualCoords m (r x) i • residualCoordinateHessianMatrix r i x

/-- The least-squares Hessian matrix `G(x) = J(x)ᵀ J(x) + S(x)`. -/
def leastSquaresHessianMatrix (r : Point n → Residual m) (x : Point n) : MatrixN n :=
  (residualJacobianMatrix r x)ᵀ * residualJacobianMatrix r x +
    leastSquaresCorrectionMatrix r x

scoped[LeastSquares] notation:max "J[" r "](" x ")" => residualJacobianMatrix r x
scoped[LeastSquares] notation:max "g[" r "](" x ")" => leastSquaresGradient r x
scoped[LeastSquares] notation:max "S[" r "](" x ")" => leastSquaresCorrectionMatrix r x
scoped[LeastSquares] notation:max "G[" r "](" x ")" => leastSquaresHessianMatrix r x

open scoped LeastSquares

/-- If the residual vanishes at `x`, then the canonical least-squares gradient vanishes. -/
theorem leastSquaresGradient_eq_zero_of_residual_eq_zero
    (r : Point n → Residual m) (x : Point n) (hResidualZero : r x = 0) :
    g[r](x) = 0 := by
  simp [leastSquaresGradient, hResidualZero]

/-- If the residual vanishes at `x`, then the residual-weighted correction matrix vanishes. -/
theorem leastSquaresCorrectionMatrix_eq_zero_of_residual_eq_zero
    (r : Point n → Residual m) (x : Point n) (hResidualZero : r x = 0) :
    S[r](x) = 0 := by
  simp [leastSquaresCorrectionMatrix, hResidualZero]

end
