/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import OptimizationTheoryAndMethods_SunYuan_2006.Chap07.Theorem_7_4_3

noncomputable section

open Matrix

section

variable {m n : ℕ}

local notation "StepVector" => EuclideanSpace ℝ (Fin n)
local notation "ResidualVector" => EuclideanSpace ℝ (Fin m)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ
local notation "JacobianMatrix" => Matrix (Fin m) (Fin n) ℝ

-- Domain sampling:
-- * primary domain: damped least-squares / Levenberg-Marquardt stacked residual minimization
-- * sampled chapter owners:
--   `moreDampedLeastSquaresMatrix`
--   `moreDampedLeastSquaresOffset`
--   `moreDampedLeastSquaresObjective`
--   `IsMoreDampedLeastSquaresStep`
-- * core/canonical owner here: `IsMoreDampedLeastSquaresStep`
-- * bridge/view layer here: the Exercise 7.5 identity-scaling specialization `d = 1` together
--   with the explicit closed-form step on `EuclideanSpace ℝ (Fin n)` via `Matrix.toEuclideanLin`
-- * primitive data: the Jacobian `J`, residual vector `r`, and damping parameter `μ`
-- * derived API removed here: duplicate local identity-scaling matrix/offset/objective owners

/-- Chapter07 Exercise 7.5: for `r : ResidualVector`, `J : JacobianMatrix`, and `μ > 0`, the
explicit damped least-squares solution minimizes Moré's stacked damped least-squares objective in
the identity-scaling specialization `d = 1`. In the source notation this is the minimizer of
`s ↦ ‖W s + y‖²`, where `W = [J; √μ I]` and `y = [r; 0]`. -/
theorem dampedLeastSquaresStep_isMoreDampedLeastSquaresStep
    (J : JacobianMatrix) (r : ResidualVector) (μ : ℝ) (hμ : 0 < μ) :
    IsMoreDampedLeastSquaresStep J r (1 : Fin n → ℝ) μ
      (-((Jᵀ * J + μ • (1 : MatrixN))⁻¹).toEuclideanLin
        (trustRegionLevenbergMarquardtGradient J r)) := by
  sorry

end
