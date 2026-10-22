/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_1
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Basic

noncomputable section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

-- Semantic recall: Chapter 5 already uses the inverse-form generalized quasi-Newton surface
-- `Hnext.mulVec y = ρ • s`. This item derives the same relation from the Chapter 6 collinear
-- scaling formula on the local concrete `EuclideanSpace`/matrix layer.

/-- Rearranging the collinear scaling identity `s = w / (1 + hᵀ w)` gives
`w = (1 + hᵀ w) • s` whenever the denominator is nonzero. -/
theorem collinearScaling_eq_generalizedSecant
    (h s w : Point) (hdenom : 1 + dotProduct h w ≠ 0)
    (hs : s = (1 + dotProduct h w)⁻¹ • w) :
    w = (1 + dotProduct h w) • s := by
  rw [hs, smul_smul]
  simp [hdenom]

/-- Chapter06 Exercise 6.13: if the collinear scaling formula
`s = w / (1 + hᵀ w)` is applied to a quasi-Newton image `w = Hnext.mulVec y`, then `Hnext`
satisfies the canonical generalized quasi-Newton equation with right-hand side
`(1 + hᵀ w) • s`. -/
theorem collinearScaling_satisfiesGeneralizedQuasiNewtonEquation
    (Hnext : MatrixN) (h y s w : Point) (hw : w = Hnext.mulVec y)
    (hdenom : 1 + dotProduct h w ≠ 0)
    (hs : s = (1 + dotProduct h w)⁻¹ • w) :
    satisfiesQuasiNewtonEquation Hnext.toEuclideanLin y ((1 + dotProduct h w) • s) := by
  refine satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mpr ?_
  simpa [hw] using
    congrArg (fun v : Point ↦ v.ofLp) (collinearScaling_eq_generalizedSecant h s w hdenom hs)

/- The same collinear-scaling argument expressed through the canonical operator view
`Hnext.toEuclideanLin y = (1 + hᵀ w) • s`. -/
theorem collinearScaling_satisfiesGeneralizedQuasiNewtonEquation_apply
    (Hnext : MatrixN) (h y s w : Point) (hw : w = Hnext.mulVec y)
    (hdenom : 1 + dotProduct h w ≠ 0)
    (hs : s = (1 + dotProduct h w)⁻¹ • w) :
    Hnext.toEuclideanLin y = (1 + dotProduct h w) • s := by
  exact collinearScaling_satisfiesGeneralizedQuasiNewtonEquation Hnext h y s w hw hdenom hs

/- The canonical Chapter 5 bridge turns the operator-valued secant equation above into the
concrete matrix identity `Hnext.mulVec y = (1 + hᵀ w) • s`. -/
theorem collinearScaling_satisfiesGeneralizedQuasiNewtonEquation_mulVec
    (Hnext : MatrixN) (h y s w : Point) (hw : w = Hnext.mulVec y)
    (hdenom : 1 + dotProduct h w ≠ 0)
    (hs : s = (1 + dotProduct h w)⁻¹ • w) :
    Hnext.mulVec y = (1 + dotProduct h w) • s := by
  simpa using
    (satisfiesQuasiNewtonEquation_toEuclideanLin_iff.mp
      (collinearScaling_satisfiesGeneralizedQuasiNewtonEquation Hnext h y s w hw hdenom hs))
