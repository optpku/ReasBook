/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Definition_5_1_extra_5
import OptimizationTheoryAndMethods_SunYuan_2006.Chap05.Theorem_5_1_10

noncomputable section

open Matrix
open scoped Matrix.Norms.Frobenius

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "MatrixN" => Matrix (Fin n) (Fin n) ℝ

/-- Chapter05 Exercise 5.5: the inverse-Hessian BFGS update in formula `(5.1.49)` is the unique
solution of the dual least-change problem `(5.1.79)`. Concretely, if `H` and `M` are symmetric,
`M` is nonsingular, `0 < dotProduct s y`, and `M.mulVec s = (M⁻¹).mulVec y`, then
`bfgsInverseUpdate H s y` is symmetric, satisfies the canonical inverse-form secant equation,
minimizes the weighted Frobenius change `weightedFrobeniusNorm M (Hhat - H)` among symmetric
matrices `Hhat` satisfying that secant equation, and is the unique feasible symmetric
minimizer. -/
theorem bfgsInverseUpdate_isUniqueWeightedFrobeniusMinimizer
    (H M : MatrixN) (s y : Point)
    (hH : H.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hsy : 0 < dotProduct s y) (hMs : M.mulVec s = (M⁻¹).mulVec y) :
    let Hbar := bfgsInverseUpdate H s y
    let objective : MatrixN → ℝ := fun Hhat ↦ weightedFrobeniusNorm M (Hhat - H)
    let feasibleSet : Set MatrixN :=
      {Hhat | Hhat.IsSymm ∧ satisfiesQuasiNewtonEquation Hhat.toEuclideanLin y s}
    (Hbar.IsSymm ∧ satisfiesQuasiNewtonEquation Hbar.toEuclideanLin y s) ∧
      IsMinOn objective feasibleSet Hbar ∧
      ∀ Hhat : MatrixN, Hhat ∈ feasibleSet →
        IsMinOn objective feasibleSet Hhat → Hhat = Hbar := by
  have hBfgs :
      symmetrizedBroydenLimit H y s s = bfgsInverseUpdate H s y := by
    rw [symmetrizedBroydenLimit_eq_dfpDualHessianUpdate H y s hH,
      dfpDualHessianUpdate_eq_bfgsInverseUpdate]
  simpa [hBfgs, satisfiesQuasiNewtonEquation, satisfiesQuasiNewtonEquationHessianForm] using
    (symmetrizedBroydenLimit_isUniqueWeightedFrobeniusMinimizer
      H M s y s hH hM hMdet hsy hMs)

/-- Under the exercise hypotheses, `bfgsInverseUpdate H s y` is a minimizer of
`weightedFrobeniusNorm M (Hhat - H)` on the symmetric inverse-form secant feasible set. -/
theorem bfgsInverseUpdate_isMinOn_weightedFrobeniusSymmetricSecantSet
    (H M : MatrixN) (s y : Point)
    (hH : H.IsSymm) (hM : M.IsSymm) (hMdet : IsUnit M.det)
    (hsy : 0 < dotProduct s y) (hMs : M.mulVec s = (M⁻¹).mulVec y) :
    let Hbar := bfgsInverseUpdate H s y
    let objective : MatrixN → ℝ := fun Hhat ↦ weightedFrobeniusNorm M (Hhat - H)
    let feasibleSet : Set MatrixN :=
      {Hhat | Hhat.IsSymm ∧ satisfiesQuasiNewtonEquation Hhat.toEuclideanLin y s}
    IsMinOn objective feasibleSet Hbar := by
  simpa using
    (bfgsInverseUpdate_isUniqueWeightedFrobeniusMinimizer H M s y hH hM hMdet hsy hMs).2.1

end
