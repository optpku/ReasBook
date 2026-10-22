/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Algorithm_5_1_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_4
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Matrix.Mul

noncomputable section

section Chapter05BFGSMethod

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Domain sampling:
-- * `GeneralQuasiNewtonMethod` is the Chapter 5 owner for quasi-Newton trajectory data.
-- * `bfgsInverseUpdate` is the Chapter 5 owner for the inverse-BFGS matrix recursion.
-- * this file exports the reusable BFGS bridge/view layer on top of the canonical run owner.

/-- A general quasi-Newton run is a BFGS method when the stopping tolerance is `0` and every
nonterminal stage updates the inverse-Hessian approximation by the BFGS formula with positive
curvature `⟪x (k + 1) - x k, g (k + 1) - g k⟫ > 0`. -/
structure IsBFGSMethod
    {f : Point → ℝ} (A : GeneralQuasiNewtonMethod f) : Prop where
  epsilon_eq_zero : A.ε = 0
  curvature_pos (k : ℕ) (_ : A.ε < ‖A.g k‖) :
    0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k)
  bfgs_update (k : ℕ) (_ : A.ε < ‖A.g k‖) :
    A.matrix (k + 1) =
      bfgsInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k)

namespace IsBFGSMethod

/-- Every nonterminal BFGS stage has positive curvature and the explicit BFGS inverse update. -/
theorem stepSpec
    {f : Point → ℝ} {A : GeneralQuasiNewtonMethod f}
    (hBFGS : IsBFGSMethod A) {k : ℕ} (hNotStopped : A.ε < ‖A.g k‖) :
    0 < dotProduct (A (k + 1) - A k) (A.g (k + 1) - A.g k) ∧
      A.matrix (k + 1) =
        bfgsInverseUpdate (A.matrix k) (A (k + 1) - A k) (A.g (k + 1) - A.g k) := by
  exact ⟨hBFGS.curvature_pos k hNotStopped, hBFGS.bfgs_update k hNotStopped⟩

end IsBFGSMethod

end Chapter05BFGSMethod
