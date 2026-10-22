/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Exercise_5_3

noncomputable section

-- Domain sampling for this item:
-- * primary domain: positive-definite inverse-Hessian quasi-Newton updates on real matrices
-- * mathlib owner: `Matrix.PosDef`
-- * Chapter 5 core/canonical owner: `dfpInverseUpdate`
-- * bridge/view only: the secant and positivity lemmas recorded in `Exercise_5_3`
-- Primitive data here is just `H`, `s`, `y`, and the nonzero secant denominator needed to stay
-- on the DFP update domain; the positive curvature statement itself is owned upstream by
-- `satisfiesCurvatureCondition`.

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Theorem 5.1.5 (Positive Definiteness of DFP Update): if `H` is a positive
definite real matrix, then on the DFP update domain `dotProduct s y ≠ 0` the canonical DFP
inverse-Hessian update `dfpInverseUpdate H s y` is positive definite if and only if the secant
pair satisfies the Chapter 5 curvature condition. -/
theorem dfpInverseUpdate_posDef_iff
    (H : MatrixN) (hH : H.PosDef) (s y : Point) (hsy : dotProduct s y ≠ 0) :
    (dfpInverseUpdate H s y).PosDef ↔ satisfiesCurvatureCondition s y := by
  have hy : y ≠ 0 := right_ne_zero_of_dotProduct_ne_zero hsy
  constructor
  · intro hDfp
    have hy' : y.1 ≠ 0 := by
      simpa using hy
    have hPos : 0 < dotProduct y ((dfpInverseUpdate H s y).mulVec y) := by
      simpa using hDfp.dotProduct_mulVec_pos hy'
    have hQN := dfpInverseUpdate_satisfiesQuasiNewtonEquation H s y hsy
      (posDef_dotProduct_mulVec_ne_zero hH hy)
    have hQN' : (dfpInverseUpdate H s y).mulVec y.ofLp = s.ofLp := by
      simpa [satisfiesQuasiNewtonEquation] using congrArg WithLp.ofLp hQN
    rw [satisfiesCurvatureCondition_iff_dotProduct_pos]
    simpa [hQN', dotProduct_comm] using hPos
  · intro hcurv
    exact dfpInverseUpdate_posDef_of_posDef_of_curvature H hH s y <|
      satisfiesCurvatureCondition_iff_dotProduct_pos.mp hcurv

end
