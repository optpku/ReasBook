/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_4
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Symmetric

noncomputable section

-- Domain sampling for this file:
-- * core/canonical owner: `dfpInverseUpdate` from `Algorithm_5_1_4`
-- * same-domain companion forms: `bfgsInverseUpdate_eq_expandedForm` and
--   `dfpDualHessianUpdate_eq_expandedForm` in `Definition_5_1_extra_4`
-- * duplicate local DFP owners exist elsewhere in Chapter 5, so this file reuses the established
--   Chapter 5 owner instead of introducing another `dfpUpdate` wrapper

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/- Chapter05 Definition 5.1-extra-3: the DFP inverse-Hessian update is the existing Chapter 5
owner `dfpInverseUpdate`. -/
#check dfpInverseUpdate

/-- For symmetric `H`, the source matrix form
`H + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s
  - (dotProduct y (H.mulVec y))⁻¹ • (H * Matrix.vecMulVec y y * H)`
agrees with the canonical Chapter 5 DFP owner `dfpInverseUpdate H s y`. -/
theorem dfpInverseUpdate_eq_symmetricMatrixForm
    {H : MatrixN} (hH : H.IsSymm) (s y : Point) :
    dfpInverseUpdate H s y =
      H + (dotProduct s y)⁻¹ • Matrix.vecMulVec s s -
        (dotProduct y (H.mulVec y))⁻¹ • (H * Matrix.vecMulVec y y * H) := by
  -- Convert the right row-vector factor into the usual `mulVec` expression using symmetry.
  have hVecMul : Matrix.vecMul y H = H.mulVec y := by
    simpa [hH.eq] using Matrix.vecMul_transpose H y
  -- Normalize the symmetric sandwich into the outer product used by `dfpInverseUpdate`.
  have hOuter :
      H * Matrix.vecMulVec y y * H = Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
    calc
      H * Matrix.vecMulVec y y * H
          = Matrix.vecMulVec (H.mulVec y) y * H := by
              rw [Matrix.mul_vecMulVec]
      _ = Matrix.vecMulVec (H.mulVec y) (Matrix.vecMul y H) := by
            rw [Matrix.vecMulVec_mul]
      _ = Matrix.vecMulVec (H.mulVec y) (H.mulVec y) := by
            rw [hVecMul]
  -- Unfold the canonical owner and rewrite its final rank-one term into the textbook form.
  rw [dfpInverseUpdate, ← hOuter]

end
