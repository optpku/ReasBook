/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap06.Algorithm_6_2_2

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-
Domain sampling for this item:
- primary domain: quasi-Newton matrix updates on the Chapter 5/6 Euclidean matrix model;
- sampled owner declarations in this domain:
  `bfgsInverseUpdate`,
  `bfgsInverseUpdate_eq_expandedForm`,
  `bfgsInverseUpdate_eq_residualForm`,
  `collinearScalingBFGSMatrixUpdate`;
- best owner abstraction: the canonical Chapter 5 inverse-BFGS owner together with the Chapter 6
  collinear-scaling owner;
- primitive data here: a current matrix `C`, secant pair `s y`, and scaling parameter `γ`;
- derived API here: the three source-facing Exercise 6.14 formulas relating those owners.

This file therefore stays at the `source-facing` bridge layer and reuses the existing owners
directly instead of keeping parallel local matrix-update definitions.
-/

/-- Chapter06 Exercise 6.14 (1): the compact collinear scaling BFGS formula writes
`collinearScalingBFGSMatrixUpdate γ C s y` as `γ^2` times the Chapter 5 inverse-BFGS update. -/
theorem collinearScalingBFGSMatrixUpdate_eq_scaledBfgsInverseUpdate
    (γ : ℝ) (C : MatrixN) (s y : Point) :
    collinearScalingBFGSMatrixUpdate γ C s y = γ ^ 2 • bfgsInverseUpdate C s y := by
  simp [collinearScalingBFGSMatrixUpdate, bfgsInverseUpdate]

/-- Chapter06 Exercise 6.14 (2): the expanded collinear scaling BFGS formula is obtained by
scaling the expanded inverse-BFGS identity by `γ^2`. -/
theorem collinearScalingBFGSMatrixUpdate_eq_scaledExpandedForm
    (γ : ℝ) (C : MatrixN) (s y : Point) :
    collinearScalingBFGSMatrixUpdate γ C s y =
      γ ^ 2 •
        (C +
          ((1 + dotProduct y (C.mulVec y) / dotProduct s y) * (dotProduct s y)⁻¹) •
            Matrix.vecMulVec s s -
          (dotProduct s y)⁻¹ •
            (Matrix.vecMulVec s y * C + C * Matrix.vecMulVec y s)) := by
  rw [collinearScalingBFGSMatrixUpdate_eq_scaledBfgsInverseUpdate]
  simpa [Matrix.toEuclideanLin] using
    congrArg (fun M : MatrixN ↦ γ ^ 2 • M) (bfgsInverseUpdate_eq_expandedForm C s y)

/-- Chapter06 Exercise 6.14 (3): the residual collinear scaling BFGS formula is obtained by
scaling the residual inverse-BFGS identity by `γ^2`. -/
theorem collinearScalingBFGSMatrixUpdate_eq_scaledResidualForm
    (γ : ℝ) (C : MatrixN) (s y : Point) :
    collinearScalingBFGSMatrixUpdate γ C s y =
      let r := s - C.mulVec y
      γ ^ 2 •
        (C + (dotProduct s y)⁻¹ • (Matrix.vecMulVec r s + Matrix.vecMulVec s r) -
          (dotProduct r y * (dotProduct s y)⁻¹ * (dotProduct s y)⁻¹) •
            Matrix.vecMulVec s s) := by
  rw [collinearScalingBFGSMatrixUpdate_eq_scaledBfgsInverseUpdate]
  simpa [Matrix.toEuclideanLin] using
    congrArg (fun M : MatrixN ↦ γ ^ 2 • M) (bfgsInverseUpdate_eq_residualForm C s y)
