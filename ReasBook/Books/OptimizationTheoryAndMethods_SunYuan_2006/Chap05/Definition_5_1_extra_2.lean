/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.ToLin

noncomputable section

open Matrix

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling for this file:
-- * primary domain: quasi-Newton SR1 inverse updates on Euclidean matrix models
-- * sampled same-domain owners: `sr1Update`, `sr1Residual`, `Matrix.toEuclideanLin`,
--   `Matrix.IsSymm`
-- * best owner abstraction: the Chapter 5 matrix owner `sr1Update`
-- * primitive data: a current matrix `H` and secant pair `s y`
-- * derived API: formula expansion, the concrete secant equation, and symmetry preservation
--
-- This file therefore keeps the SR1 owner local to the textbook item and develops only the
-- concrete matrix API that the later Chapter 5 results use.

/-- Helper for Chapter05 Definition 5.1-extra-2: the SR1 residual vector `s - H y`
that determines the rank-one correction. -/
def sr1Residual (H : MatrixN) (y s : Point) : Point :=
  s - Matrix.toEuclideanLin H y

/-- Chapter05 Definition 5.1-extra-2: the symmetric rank-one inverse-Hessian update is
`H + (dotProduct (sr1Residual H y s) y)⁻¹ •
  Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s)`. -/
def sr1Update (H : MatrixN) (s y : Point) : MatrixN :=
  H + (dotProduct (sr1Residual H y s) y)⁻¹ •
    Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s)

/-- Expanding the Chapter 5 owner `sr1Update` gives the residual rank-one correction formula
`H + (dotProduct (sr1Residual H y s) y)⁻¹ •
  Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s)`. -/
theorem sr1Update_eq_rankOneCorrection
    (H : MatrixN) (s y : Point) :
    sr1Update H s y =
      H + (dotProduct (sr1Residual H y s) y)⁻¹ •
        Matrix.vecMulVec (sr1Residual H y s) (sr1Residual H y s) := rfl

/-- Helper for Chapter05 Definition 5.1-extra-2: the SR1 rank-one correction sends the secant
vector `y` exactly to the residual vector `r`. -/
lemma sr1CorrectionAppliesResidual
    (r y : Point) (hdenom : dotProduct r y ≠ 0) :
    Matrix.toEuclideanLin ((dotProduct r y)⁻¹ • Matrix.vecMulVec r r) y = r := by
  -- Pull the scalar out of the matrix action and collapse the outer product on `y`.
  calc
    Matrix.toEuclideanLin ((dotProduct r y)⁻¹ • Matrix.vecMulVec r r) y
        = (dotProduct r y)⁻¹ • Matrix.toEuclideanLin (Matrix.vecMulVec r r) y := by
            simp
    _ = (dotProduct r y)⁻¹ • (dotProduct r y • r) := by
          rw [Matrix.toEuclideanLin, Matrix.toLpLin_apply]
          simp [Matrix.vecMulVec_mulVec]
    _ = r := by
          simp [hdenom]

/-- Helper for Chapter05 Definition 5.1-extra-2: the rank-one matrix `r rᵀ` is symmetric. -/
lemma rankOneSelf_isSymm (r : Point) : (Matrix.vecMulVec r r).IsSymm := by
  -- Compare the entries across the transpose; both sides are the same scalar product.
  rw [Matrix.IsSymm.ext_iff]
  intro i j
  simp [Matrix.vecMulVec_apply, mul_comm]

/-- The SR1 update satisfies the concrete inverse-form secant equation
`(sr1Update H s y).toEuclideanLin y = s`. -/
theorem sr1Update_toEuclideanLin_apply
    (H : MatrixN) (s y : Point) (hdenom : dotProduct (sr1Residual H y s) y ≠ 0) :
    (sr1Update H s y).toEuclideanLin y = s := by
  let r := sr1Residual H y s
  have hcorr : Matrix.toEuclideanLin ((dotProduct r y)⁻¹ • Matrix.vecMulVec r r) y = r := by
    -- The only nontrivial term is the SR1 correction, which evaluates to the residual.
    exact sr1CorrectionAppliesResidual r y (by simpa [r] using hdenom)
  -- Expand the update and rewrite the correction term as the residual `s - H y`.
  calc
    Matrix.toEuclideanLin (sr1Update H s y) y
        = Matrix.toEuclideanLin (H + (dotProduct r y)⁻¹ • Matrix.vecMulVec r r) y := by
            simp [sr1Update_eq_rankOneCorrection, r]
    _ = Matrix.toEuclideanLin H y +
          Matrix.toEuclideanLin ((dotProduct r y)⁻¹ • Matrix.vecMulVec r r) y := by
          simp
    _ = Matrix.toEuclideanLin H y + r := by
          rw [hcorr]
    _ = s := by
          dsimp [r, sr1Residual]
          abel

/-- If the current inverse-Hessian approximation `H` is symmetric, then its SR1 update is
symmetric as well. -/
theorem sr1Update_isSymm
    {H : MatrixN} (hH : H.IsSymm) (s y : Point) :
    (sr1Update H s y).IsSymm := by
  let r := sr1Residual H y s
  -- Expand the update and combine symmetry of the base matrix with symmetry of `r rᵀ`.
  rw [sr1Update_eq_rankOneCorrection]
  exact hH.add ((rankOneSelf_isSymm r).smul ((dotProduct r y)⁻¹))
