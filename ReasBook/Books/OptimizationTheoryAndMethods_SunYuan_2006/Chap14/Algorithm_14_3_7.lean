/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.EuclideanSubgradient
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul

noncomputable section

section

variable {n : ℕ}

open Chapter14 (IsSubgradientAt)
open scoped Subgradient

-- Domain sampling:
-- * source-facing owner in this file: `SpaceDilationMethod`
-- * chapter owner reused here: `Point` together with the bridge `IsSubgradientAt`
-- * mathlib owner reused here: `Matrix.toEuclideanLin`
-- Primitive data remain the source iterate, vector subgradient, and dilation matrix. The
-- coordinate-level matrix action wrapper has been deleted in favor of the canonical Euclidean
-- matrix action.

/-- The denominator `gᵀ H g` appearing in formulas `(14.3.38)` and `(14.3.39)`. -/
def spaceDilationDenominator
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (g : Chapter14.Point n) : ℝ :=
  dotProduct g (Matrix.toEuclideanLin H g)

/-- Unfolding `spaceDilationDenominator H g` gives the source quadratic form `gᵀ H g`. -/
theorem spaceDilationDenominator_eq
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (g : Chapter14.Point n) :
    spaceDilationDenominator H g = dotProduct g (Matrix.toEuclideanLin H g) :=
  rfl

/-- The normalized Step-2 direction from `(14.3.38)`, namely
`-(gᵀ H g)^(-1 / 2) • (H g)`. -/
def spaceDilationDirection
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (g : Chapter14.Point n) :
    Chapter14.Point n :=
  -((Real.sqrt (spaceDilationDenominator H g))⁻¹) • Matrix.toEuclideanLin H g

/-- Unfolding `spaceDilationDirection H g` gives the source direction
`-(gᵀ H g)^(-1 / 2) • (H g)`. -/
theorem spaceDilationDirection_eq
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (g : Chapter14.Point n) :
    spaceDilationDirection H g =
      -((Real.sqrt (spaceDilationDenominator H g))⁻¹) • Matrix.toEuclideanLin H g :=
  rfl

/-- The Step-3 matrix update from `(14.3.39)`,
`r • (H - (β / (gᵀ H g)) • (H g) (gᵀ H))`. -/
def spaceDilationMatrixUpdate
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (g : Chapter14.Point n)
    (r β : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  r •
    (H - (β / spaceDilationDenominator H g) •
      Matrix.vecMulVec (H.mulVec g.ofLp) (H.transpose.mulVec g.ofLp))

/-- Unfolding `spaceDilationMatrixUpdate H g r β` gives the source rank-one correction
`r • (H - (β / (gᵀ H g)) • (H g) (gᵀ H))`. -/
theorem spaceDilationMatrixUpdate_eq
    {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) (g : Chapter14.Point n) (r β : ℝ) :
    spaceDilationMatrixUpdate H g r β =
      r •
        (H - (β / spaceDilationDenominator H g) •
          Matrix.vecMulVec (H.mulVec g.ofLp) (H.transpose.mulVec g.ofLp)) :=
  rfl

/-- The fixed stepsize `αₖ = 1 / (n + 1)` from `(14.3.40)` for Algorithm 14.3.7. -/
def spaceDilationStepSize (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

/-- The fixed stepsize `αₖ = 1 / (n + 1)` from `(14.3.40)` is positive. -/
theorem spaceDilationStepSize_pos (n : ℕ) :
    0 < spaceDilationStepSize n := by
  have hden : 0 < (n + 1 : ℝ) := by
    exact_mod_cast Nat.succ_pos n
  simpa [spaceDilationStepSize] using one_div_pos.mpr hden

/-- The fixed contraction coefficient `βₖ = 2 / (n + 2)` from `(14.3.40)` for
Algorithm 14.3.7. -/
def spaceDilationBeta (n : ℕ) : ℝ :=
  2 / (n + 2 : ℝ)

/-- The fixed coefficient `βₖ = 2 / (n + 2)` from `(14.3.40)` is positive. -/
theorem spaceDilationBeta_pos (n : ℕ) :
    0 < spaceDilationBeta n := by
  have hden : 0 < (n + 2 : ℝ) := by
    exact_mod_cast Nat.succ_pos (n + 1)
  simpa [spaceDilationBeta] using div_pos (show (0 : ℝ) < 2 by norm_num) hden

/-- If `n ≥ 1`, the fixed coefficient `βₖ = 2 / (n + 2)` from `(14.3.40)` satisfies `βₖ < 1`. -/
theorem spaceDilationBeta_lt_one {n : ℕ} (hn : 1 ≤ n) :
    spaceDilationBeta n < 1 := by
  have hden : (0 : ℝ) < n + 2 := by
    exact_mod_cast Nat.succ_pos (n + 1)
  have hlt : (2 : ℝ) < n + 2 := by
    have hlt_nat : 2 < n + 2 := by
      omega
    exact_mod_cast hlt_nat
  simpa [spaceDilationBeta] using (div_lt_one hden).2 hlt

/-- The fixed rescaling factor `rₖ = n^2 / (n^2 - 1)` from `(14.3.40)` for
Algorithm 14.3.7. -/
def spaceDilationScaleFactor (n : ℕ) : ℝ :=
  (n : ℝ) ^ (2 : ℕ) / ((n : ℝ) ^ (2 : ℕ) - 1)

/-- If `n ≥ 2`, the fixed rescaling factor `rₖ = n^2 / (n^2 - 1)` from `(14.3.40)` is positive. -/
theorem spaceDilationScaleFactor_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < spaceDilationScaleFactor n := by
  have hn' : (2 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hsq : (4 : ℝ) ≤ (n : ℝ) ^ (2 : ℕ) := by
    nlinarith [sq_nonneg ((n : ℝ) - 2)]
  have hnum : 0 < (n : ℝ) ^ (2 : ℕ) := by
    nlinarith
  have hden : 0 < (n : ℝ) ^ (2 : ℕ) - 1 := by
    nlinarith
  exact div_pos hnum hden

/-- The rate factor `q` from `(14.3.42)` in Theorem 14.3.8. -/
def spaceDilationRateFactor (n : ℕ) : ℝ :=
  ((1 : ℝ) - 2 / (n + 1 : ℝ)) ^ (1 / (2 * n : ℝ)) *
    (n : ℝ) / Real.sqrt ((n : ℝ) ^ (2 : ℕ) - 1)

/-- Chapter14 Algorithm 14.3.7: the space dilation method for `f : ℝ^n → ℝ` is only valid in
dimension `n ≥ 2`. It starts from an initial point `x₁`, an initial scalar `α > 0` with
`H₁ = α I`, and for each stage `k ≥ 1` records a chosen vector `g_k` whose Riesz functional lies
in `∂ f(x_k)`. In Algorithm 14.3.7 the stepsize, rescaling factor, and coefficient are fixed by
`(14.3.40)` as `αₖ = 1 / (n + 1)`, `rₖ = n^2 / (n^2 - 1)`, and `βₖ = 2 / (n + 2)` for every
stage `k ≥ 1`, so their positivity properties are exposed as companion lemmas rather than as
extra structure fields. The iterate update is
`x_(k + 1) = x_k - α_k • (g_kᵀ H_k g_k)^(-1 / 2) • (H_k g_k)`, and the matrix update is
`H_(k + 1) = r_k • (H_k - (β_k / (g_kᵀ H_k g_k)) • (H_k g_k) (g_kᵀ H_k))`. -/
structure SpaceDilationMethod (n : ℕ) where
  objective : Chapter14.Point n → ℝ
  initialPoint : Chapter14.Point n
  initialScale : ℝ
  iterate : ℕ → Chapter14.Point n
  subgradient : ℕ → Chapter14.Point n
  dilation : ℕ → Matrix (Fin n) (Fin n) ℝ
  dimension_two_le : 2 ≤ n
  initialScale_pos : 0 < initialScale
  iterate_one : iterate 1 = initialPoint
  dilation_one : dilation 1 = initialScale • (1 : Matrix (Fin n) (Fin n) ℝ)
  subgradient_mem {k : ℕ} (hk : 1 ≤ k) :
    IsSubgradientAt objective (iterate k) (subgradient k)
  denominator_pos {k : ℕ} (hk : 1 ≤ k) :
    0 < spaceDilationDenominator (dilation k) (subgradient k)
  iterate_succ {k : ℕ} (hk : 1 ≤ k) :
    iterate (k + 1) =
      iterate k + spaceDilationStepSize n • spaceDilationDirection (dilation k) (subgradient k)
  dilation_succ {k : ℕ} (hk : 1 ≤ k) :
    dilation (k + 1) =
      spaceDilationMatrixUpdate
        (dilation k)
        (subgradient k)
        (spaceDilationScaleFactor n)
        (spaceDilationBeta n)

namespace SpaceDilationMethod

/-- The objective value `f(x_k)` attached to the stage-`k` iterate. -/
def objectiveValueAt
    (method : SpaceDilationMethod n) (k : ℕ) : ℝ :=
  method.objective (method.iterate k)

/-- Unfolding `method.objectiveValueAt k` gives the source objective value `f(x_k)`. -/
@[simp] theorem objectiveValueAt_eq
    (method : SpaceDilationMethod n) (k : ℕ) :
    method.objectiveValueAt k = method.objective (method.iterate k) :=
  rfl

/-- The Step-2 denominator `g_kᵀ H_k g_k` attached to stage `k`. -/
def denominatorAt
    (method : SpaceDilationMethod n) (k : ℕ) : ℝ :=
  spaceDilationDenominator (method.dilation k) (method.subgradient k)

/-- The Step-2 direction attached to stage `k`. -/
def directionAt
    (method : SpaceDilationMethod n) (k : ℕ) :
    Chapter14.Point n :=
  spaceDilationDirection (method.dilation k) (method.subgradient k)

/-- The Step-3 matrix update determined by the stage-`k` data. -/
def matrixUpdateAt
    (method : SpaceDilationMethod n) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℝ :=
  spaceDilationMatrixUpdate
    (method.dilation k)
    (method.subgradient k)
    (spaceDilationScaleFactor n)
    (spaceDilationBeta n)

/-- Unfolding `method.denominatorAt k` gives the source quadratic form `g_kᵀ H_k g_k`. -/
theorem denominatorAt_eq
    (method : SpaceDilationMethod n) (k : ℕ) :
    method.denominatorAt k =
      spaceDilationDenominator (method.dilation k) (method.subgradient k) :=
  rfl

/-- Unfolding `method.directionAt k` gives the normalized Step-2 direction from `(14.3.38)`. -/
theorem directionAt_eq
    (method : SpaceDilationMethod n) (k : ℕ) :
    method.directionAt k =
      spaceDilationDirection (method.dilation k) (method.subgradient k) :=
  rfl

/-- Unfolding `method.matrixUpdateAt k` gives the Step-3 matrix update from `(14.3.39)`. -/
theorem matrixUpdateAt_eq
    (method : SpaceDilationMethod n) (k : ℕ) :
    method.matrixUpdateAt k =
      spaceDilationMatrixUpdate
        (method.dilation k)
        (method.subgradient k)
        (spaceDilationScaleFactor n)
        (spaceDilationBeta n) :=
  rfl

/-- At every stage `k ≥ 1`, the Riesz functional of the chosen vector `g_k` lies in
`∂ method.objective(x_k)`. -/
theorem subgradient_mem_at
    (method : SpaceDilationMethod n) {k : ℕ} (hk : 1 ≤ k) :
    IsSubgradientAt method.objective (method.iterate k) (method.subgradient k) :=
  method.subgradient_mem hk

/-- A space-dilation method lives in dimension `n > 1`, equivalently `n ≥ 2`. -/
theorem one_lt_dimension
    (method : SpaceDilationMethod n) :
    1 < n := by
  exact lt_of_lt_of_le (by decide : 1 < 2) method.dimension_two_le

/-- If `k ≥ 1`, the denominator `g_kᵀ H_k g_k` used in `(14.3.38)` and `(14.3.39)` is positive. -/
theorem denominator_pos_at
    (method : SpaceDilationMethod n) {k : ℕ} (hk : 1 ≤ k) :
    0 < method.denominatorAt k := by
  simpa [denominatorAt] using method.denominator_pos hk

/-- If `k ≥ 1`, the next iterate is obtained by moving along the normalized Step-2
direction with the fixed source stepsize `αₖ = 1 / (n + 1)`. -/
theorem iterate_succ_eq_add_direction
    (method : SpaceDilationMethod n) {k : ℕ} (hk : 1 ≤ k) :
    method.iterate (k + 1) = method.iterate k + spaceDilationStepSize n • method.directionAt k := by
  simpa [directionAt] using method.iterate_succ hk

/-- If `k ≥ 1`, the next dilation matrix is the recorded Step-3 update built from the current
matrix `H_k`, subgradient `g_k`, and the fixed constants `rₖ` and `βₖ` from `(14.3.40)`. -/
theorem dilation_succ_eq_matrixUpdateAt
    (method : SpaceDilationMethod n) {k : ℕ} (hk : 1 ≤ k) :
    method.dilation (k + 1) = method.matrixUpdateAt k := by
  simpa [matrixUpdateAt] using method.dilation_succ hk

end SpaceDilationMethod

#print axioms spaceDilationDenominator
#print axioms spaceDilationDirection
#print axioms spaceDilationMatrixUpdate
#print axioms spaceDilationStepSize
#print axioms spaceDilationBeta
#print axioms spaceDilationScaleFactor
#print axioms spaceDilationRateFactor
#print axioms subdifferential

end
