/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Example_9_1.Objectives

public section

noncomputable section

namespace Exercise911

/-- The constant Hessian matrix `Kᵀ K + α I` for the regularized least-squares
objective `(9.2)` on the `§9.4.1` benchmark surface. -/
def leastSquaresHessianMatrix
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (regularization941 : ℝ) :
    EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
  fun _ ↦
    forwardOperator941.transpose * forwardOperator941 +
      regularization941 • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Evaluating `leastSquaresHessianMatrix` recovers the constant matrix
`Kᵀ K + α I`. -/
theorem leastSquaresHessianMatrix_apply
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (regularization941 : ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    leastSquaresHessianMatrix n forwardOperator941 regularization941 f =
      forwardOperator941.transpose * forwardOperator941 +
        regularization941 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Evaluating the constant Hessian family just unfolds its defining function.
  simp [leastSquaresHessianMatrix]

/-- The shifted Poisson-likelihood Hessian matrix family `Kᵀ D(f) K + α I`
using the diagonal matrix from `(9.8)`. -/
def likelihoodHessianMatrix
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (varianceShift941 regularization941 : ℝ) :
    EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ :=
  fun f ↦
    forwardOperator941.transpose *
        example91LikelihoodDiagonal n forwardOperator941 data941 varianceShift941 f *
        forwardOperator941 +
      regularization941 • (1 : Matrix (Fin n) (Fin n) ℝ)

/-- Evaluating `likelihoodHessianMatrix` recovers the matrix `Kᵀ D(f) K + α I`
from `(9.7)`-`(9.8)`. -/
theorem likelihoodHessianMatrix_apply
    (n : ℕ)
    (forwardOperator941 : Matrix (Fin n) (Fin n) ℝ)
    (data941 : EuclideanSpace ℝ (Fin n))
    (varianceShift941 regularization941 : ℝ)
    (f : EuclideanSpace ℝ (Fin n)) :
    likelihoodHessianMatrix n forwardOperator941 data941
        varianceShift941 regularization941 f =
      forwardOperator941.transpose *
          example91LikelihoodDiagonal n forwardOperator941 data941 varianceShift941 f *
          forwardOperator941 +
        regularization941 • (1 : Matrix (Fin n) (Fin n) ℝ) := by
  -- Evaluating the Hessian family exposes the displayed `Kᵀ D(f) K + α I` form.
  simp [likelihoodHessianMatrix]

end Exercise911
