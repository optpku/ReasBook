/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Domain sampling in the Chapter 5 quasi-Newton update family shows that
-- `symmetrizedBroydenLimit` from `Definition_5_1_extra_4` is already the owner of the
-- general PSB matrix. Its SR1/DFP/BFGS specializations are likewise recorded there by the
-- canonical declarations `sr1Residual`, `sr1DualBFormUpdate`, `dfpDualHessianUpdate`,
-- `bfgsHessianUpdate`, and `powellSymmetricBroydenUpdate`. This file therefore keeps only
-- the additional source-facing specialization statements from the current entry.

#check symmetrizedBroydenLimit

/-- Chapter05 Definition 5.1-extra-5 (1): the general PSB update is the previously introduced
owner `symmetrizedBroydenLimit`, and it satisfies the source formula
`B + (dotProduct c s)⁻¹ •
    (Matrix.vecMulVec (sr1Residual B s y) c + Matrix.vecMulVec c (sr1Residual B s y)) -
  (dotProduct (sr1Residual B s y) s / (dotProduct c s) ^ (2 : ℕ)) • Matrix.vecMulVec c c`. -/
theorem symmetrizedBroydenLimit_eq_formula
    (B : MatrixN) (s y c : Point) :
    symmetrizedBroydenLimit B s y c =
      B + (dotProduct c s)⁻¹ •
          (Matrix.vecMulVec (sr1Residual B s y) c + Matrix.vecMulVec c (sr1Residual B s y)) -
        (dotProduct (sr1Residual B s y) s / (dotProduct c s) ^ (2 : ℕ)) •
          Matrix.vecMulVec c c := by
  -- Unfold the owner formula once and reassociate the duplicated inverse factor.
  simp [symmetrizedBroydenLimit, sr1Residual, pow_two, div_eq_mul_inv, mul_assoc]

/-- Companion to Chapter05 Definition 5.1-extra-5 (2): setting
`c = sr1Residual B s y` in the general PSB class recovers the SR1 specialization
formula `(5.1.54)`, namely the existing owners `sr1Residual` and
`sr1DualBFormUpdate`. -/
theorem symmetrizedBroydenLimit_eq_sr1DualBFormUpdate
    (B : MatrixN) (s y : Point) :
    symmetrizedBroydenLimit B s y (sr1Residual B s y) = sr1DualBFormUpdate B s y := by
  -- Specialize the PSB formula at the SR1 residual and collapse the coefficient algebra.
  rw [symmetrizedBroydenLimit_eq_formula, sr1DualBFormUpdate]
  let r : Point := sr1Residual B s y
  by_cases hrs : dotProduct r s = 0
  · -- In the totalized zero-denominator branch, both correction terms vanish.
    simp [hrs, r]
  · -- Otherwise the two rank-one coefficients combine to the SR1 scalar.
    ext i j
    simp [Matrix.vecMulVec_apply, div_eq_mul_inv]
    field_simp [hrs]
    ring

/-- Companion to Chapter05 Definition 5.1-extra-5 (3): in the symmetric quasi-Newton
setting, setting `c = y` in the general PSB class recovers the DFP specialization,
namely the existing canonical owner `dfpDualHessianUpdate`. -/
theorem symmetrizedBroydenLimit_eq_dfpDualHessianUpdate
    (B : MatrixN) (s y : Point) (hB : Matrix.IsSymm B) :
    symmetrizedBroydenLimit B s y y = dfpDualHessianUpdate B s y := by
  -- Reuse the residual-form DFP owner and only normalize the denominator spelling.
  simpa [symmetrizedBroydenLimit, sr1Residual, pow_two, div_eq_mul_inv] using
    (dfpDualHessianUpdate_eq_residualForm B s y hB).symm

/-- Helper for Chapter05 Definition 5.1-extra-5: on the nonnegative square-root branch,
the BFGS affine PSB choice has denominator `√((dotProduct y s) / (dotProduct s (B.mulVec s))) *
dotProduct s (B.mulVec s)`. -/
theorem bfgsPsbChoice_dotProduct_eq_sqrtMulCurvature
    (B : MatrixN) (s y : Point)
    (hRatio : 0 ≤ dotProduct y s / dotProduct s (B.mulVec s))
    (hBs : dotProduct s (B.mulVec s) ≠ 0) :
    let w : ℝ := Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s))
    let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
    dotProduct c s = w * dotProduct s (B.mulVec s) := by
  -- Route correction: normalize the affine denominator once so later BFGS proofs can rewrite
  -- through a stable scalar identity instead of repeatedly unfolding `c`.
  let a : ℝ := dotProduct y s
  let b : ℝ := dotProduct s (B.mulVec s)
  let w : ℝ := Real.sqrt (a / b)
  let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
  change dotProduct c s = w * b
  have hw_sq : w ^ (2 : ℕ) = a / b := by
    simpa [w] using (Real.sq_sqrt hRatio)
  have ha : a = w ^ (2 : ℕ) * b := by
    symm
    exact (eq_div_iff hBs).1 hw_sq
  have hw1 : w + 1 ≠ 0 := by
    have hw_nonneg : 0 ≤ w := by
      simp [w]
    linarith
  -- Expand the dot product of the affine combination and rewrite `a` through `w² b`.
  calc
    dotProduct c s = (1 / (w + 1)) * a + (w / (w + 1)) * b := by
      simp [c, a, b, dotProduct_add, dotProduct_smul, dotProduct_comm]
    _ = w * b := by
      rw [ha]
      field_simp [hw1]

/-- Helper for Chapter05 Definition 5.1-extra-5: for the totalized square-root expression
`w = √((dotProduct y s) / (dotProduct s (B.mulVec s)))` and the associated affine combination
`c`, the PSB denominator `dotProduct c s` is nonzero whenever `dotProduct y s` is nonzero. This
is an algebraic Lean helper, not the source-faithful positive-curvature BFGS domain statement. -/
theorem bfgsPsbChoice_dotProduct_ne_zero
    (B : MatrixN) (s y : Point)
    (hys : dotProduct y s ≠ 0) :
    let w : ℝ := Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s))
    let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
    dotProduct c s ≠ 0 := by
  -- Split first on the curvature denominator and then on the sign of the square-root ratio.
  dsimp
  by_cases hBs : dotProduct s (B.mulVec s) = 0
  · -- If the curvature denominator vanishes, then `w = 0` and the PSB denominator is `yᵀ s`.
    simpa [hBs, dotProduct_comm] using hys
  · by_cases hRatio : 0 ≤ dotProduct y s / dotProduct s (B.mulVec s)
    · -- On the nonnegative branch, use the normalized denominator and show both factors are
      -- nonzero.
      have hdot := bfgsPsbChoice_dotProduct_eq_sqrtMulCurvature B s y hRatio hBs
      dsimp at hdot ⊢
      rw [hdot]
      apply mul_ne_zero
      · have hratio_ne : dotProduct y s / dotProduct s (B.mulVec s) ≠ 0 := by
          exact div_ne_zero hys hBs
        exact (Real.sqrt_ne_zero hRatio).2 hratio_ne
      · simpa [dotProduct_comm] using hBs
    · -- On the negative branch, `Real.sqrt` again totalizes to `0`.
      have hw :
          Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s)) = 0 :=
        Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hRatio)
      have hw' :
          Real.sqrt (dotProduct s y / dotProduct s (B.mulVec s)) = 0 := by
        simpa [dotProduct_comm] using hw
      simpa [hw, hw', dotProduct_comm] using hys

/-- If the Chapter 5 BFGS square-root parameter is formed from positive curvature pairings,
then the algebraic BFGS-specialization denominator is nonzero. -/
theorem bfgsPsbChoice_dotProduct_ne_zero_of_pos
    (B : MatrixN) (s y : Point)
    (hys : 0 < dotProduct y s) (_hBs : 0 < dotProduct s (B.mulVec s)) :
    let w : ℝ := Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s))
    let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
    dotProduct c s ≠ 0 := by
  -- The positive-curvature corollary is the unconditional algebraic denominator lemma.
  simpa using bfgsPsbChoice_dotProduct_ne_zero B s y (ne_of_gt hys)

/-- Companion to Chapter05 Definition 5.1-extra-5 (4): in the symmetric quasi-Newton
setting and on the algebraic square-root domain
`0 ≤ (dotProduct y s) / (dotProduct s (B.mulVec s))`, choosing
`w = √((dotProduct y s) / (dotProduct s (B.mulVec s)))` and
`c = (1 / (w + 1)) • y + (w / (w + 1)) • B.mulVec s` in the general PSB class
recovers the existing BFGS Hessian-update owner `(5.1.46)`. -/
theorem symmetrizedBroydenLimit_eq_bfgsHessianUpdate
    (B : MatrixN) (s y : Point)
    (hB : Matrix.IsSymm B)
    (hRatio : 0 ≤ dotProduct y s / dotProduct s (B.mulVec s))
    (hys : dotProduct y s ≠ 0) (hBs : dotProduct s (B.mulVec s) ≠ 0) :
    let w : ℝ := Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s))
    let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
    symmetrizedBroydenLimit B s y c = bfgsHessianUpdate B s y := by
  -- Normalize both owners to sums of `vecMulVec` terms and compare the scalar coefficients
  -- entrywise through the square-root parameter `w`.
  let w : ℝ := Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s))
  let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
  change symmetrizedBroydenLimit B s y c = bfgsHessianUpdate B s y
  have hdot :
      dotProduct c s = w * dotProduct s (B.mulVec s) := by
    simpa [w, c] using
      bfgsPsbChoice_dotProduct_eq_sqrtMulCurvature B s y hRatio hBs
  have hw_sq : w ^ (2 : ℕ) = dotProduct y s / dotProduct s (B.mulVec s) := by
    simpa [w] using (Real.sq_sqrt hRatio)
  have hysw : dotProduct y s = w ^ (2 : ℕ) * dotProduct s (B.mulVec s) := by
    symm
    exact (eq_div_iff hBs).1 hw_sq
  have hw : w ≠ 0 := by
    have hratio_ne :
        dotProduct y s / dotProduct s (B.mulVec s) ≠ 0 := by
      exact div_ne_zero hys hBs
    exact (Real.sqrt_ne_zero hRatio).2 hratio_ne
  have hw_nonneg : 0 ≤ w := by
    simp [w]
  have hw1 : w + 1 ≠ 0 := by
    linarith
  rw [symmetrizedBroydenLimit_eq_formula, bfgsHessianUpdate,
    symmetricSandwich_eq_rankOneOfMulVec hB s]
  ext i j
  rw [hdot]
  simp [sr1Residual, Matrix.vecMulVec_apply, sub_eq_add_neg, w, c, div_eq_mul_inv]
  rw [hysw]
  field_simp [hys, hBs, hw, hw1]
  simp [Real.sqrt_sq hw_nonneg]
  simp [dotProduct_comm]
  ring_nf

/-- In the symmetric quasi-Newton setting, if the Chapter 5 BFGS square-root parameter is
formed from positive curvature pairings `0 < dotProduct y s` and
`0 < dotProduct s (B.mulVec s)`, then the corresponding PSB specialization recovers the
existing BFGS Hessian-update owner `(5.1.46)`. -/
theorem symmetrizedBroydenLimit_eq_bfgsHessianUpdate_of_pos
    (B : MatrixN) (s y : Point)
    (hB : Matrix.IsSymm B)
    (hys : 0 < dotProduct y s) (hBs : 0 < dotProduct s (B.mulVec s)) :
    let w : ℝ := Real.sqrt (dotProduct y s / dotProduct s (B.mulVec s))
    let c : Point := (1 / (w + 1)) • y + (w / (w + 1)) • B.toEuclideanLin s
    symmetrizedBroydenLimit B s y c = bfgsHessianUpdate B s y := by
  -- Positivity places the BFGS ratio on the nonnegative square-root branch used above.
  apply symmetrizedBroydenLimit_eq_bfgsHessianUpdate
  · exact hB
  · exact div_nonneg (le_of_lt hys) (le_of_lt hBs)
  · exact ne_of_gt hys
  · exact ne_of_gt hBs

/-- Companion to Chapter05 Definition 5.1-extra-5 (5): setting `c = s` in the general PSB
class gives the PSB specialization formula `(5.1.63)`, namely the existing owner
`powellSymmetricBroydenUpdate`. -/
theorem powellSymmetricBroydenUpdate_eq_formula
    (B : MatrixN) (s y : Point) :
    powellSymmetricBroydenUpdate B s y =
      B + (dotProduct s s)⁻¹ •
          (Matrix.vecMulVec (sr1Residual B s y) s + Matrix.vecMulVec s (sr1Residual B s y)) -
        (dotProduct (sr1Residual B s y) s / (dotProduct s s) ^ (2 : ℕ)) •
          Matrix.vecMulVec s s := by
  simpa [powellSymmetricBroydenUpdate] using symmetrizedBroydenLimit_eq_formula B s y s

/-- Companion to Chapter05 Definition 5.1-extra-5 (6): the dual `H`-form obtained by
setting `c = y` in the general PSB class with exchanged secant data `(y, s)` is called
the Greenstadt update. Its owner-level expression is
`symmetrizedBroydenLimit H y s y`. -/
theorem symmetrizedBroydenLimit_eq_greenstadtFormula
    (H : MatrixN) (s y : Point) :
    symmetrizedBroydenLimit H y s y =
      H + (dotProduct y y)⁻¹ •
          (Matrix.vecMulVec (sr1Residual H y s) y + Matrix.vecMulVec y (sr1Residual H y s)) -
        (dotProduct (sr1Residual H y s) y / (dotProduct y y) ^ (2 : ℕ)) •
          Matrix.vecMulVec y y := by
  simpa using symmetrizedBroydenLimit_eq_formula H y s y
