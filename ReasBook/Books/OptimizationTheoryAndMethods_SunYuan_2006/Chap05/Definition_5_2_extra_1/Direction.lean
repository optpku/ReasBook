/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_4
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul

open Matrix

noncomputable section

section

variable {n : ℕ}

-- Local declaration justification (source-local notation): this item-owned helper file keeps the
-- fixed Euclidean-space notation from the surrounding source formulas local to the item API.
local notation "Point" => EuclideanSpace ℝ (Fin n)
-- Local declaration justification (source-local notation): this helper file works on one fixed
-- real square-matrix space, and the alias is local shorthand rather than reusable notation.
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- The inverse-form Broyden correction vector
`v = (yᵀ H y)^(1 / 2) • ((sᵀ y)⁻¹ • s - (yᵀ H y)⁻¹ • H.mulVec y)` from `(5.2.5)`,
used below on the source denominator domain `dotProduct s y ≠ 0` and
`0 < dotProduct y (H.mulVec y)`. -/
def broydenClassDirection (H : MatrixN) (s y : Point) : Point :=
  Real.sqrt (dotProduct y (H.mulVec y)) •
    ((dotProduct s y)⁻¹ • s - (dotProduct y (H.mulVec y))⁻¹ • H.toEuclideanLin y)

/-- Expanding `broydenClassDirection` recovers the source formula `(5.2.5)`. -/
theorem broydenClassDirection_eq (H : MatrixN) (s y : Point) :
    broydenClassDirection H s y =
      Real.sqrt (dotProduct y (H.mulVec y)) •
        ((dotProduct s y)⁻¹ • s - (dotProduct y (H.mulVec y))⁻¹ • H.toEuclideanLin y) := by
  rfl

/-- The canonical inverse-Hessian BFGS update is the canonical DFP inverse update plus the
rank-one correction `v vᵀ` built from `broydenClassDirection H s y`. -/
theorem bfgsInverseUpdate_eq_dfpInverseUpdate_add_broydenClassDirection
    (H : MatrixN) (hH : Matrix.IsSymm H) (s y : Point) (hsy : dotProduct s y ≠ 0)
    (hyHy : 0 < dotProduct y (H.mulVec y)) :
    bfgsInverseUpdate H s y =
      dfpInverseUpdate H s y
        + Matrix.vecMulVec
            (broydenClassDirection H s y)
            (broydenClassDirection H s y) := by
  have hVecMul : Matrix.vecMul y H = H.toEuclideanLin y := by
    simpa [hH.eq] using Matrix.vecMul_transpose H y
  -- Expand both updates and the Broyden direction in coordinates; the remaining step is a
  -- scalar identity on the common outer-product basis.
  rw [bfgsInverseUpdate_eq_expandedForm]
  ext i j
  simp [dfpInverseUpdate, broydenClassDirection, hVecMul, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.vecMulVec_apply, Matrix.toEuclideanLin,
    Matrix.toLpLin_apply, sub_eq_add_neg, div_eq_mul_inv]
  field_simp [hsy, hyHy.ne']
  simp [pow_two, Real.sq_sqrt (le_of_lt hyHy)]
  ring_nf

end
