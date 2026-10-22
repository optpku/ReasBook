/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Real.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Exercise_1_5

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator

section

variable {m n : ℕ}

/-- The Section 13.3 branch hypothesis `(13.3.25)` for the stage data
`(c_k, A_k, ξ_k, Δ_k, b₂)`, written directly on the canonical Moore-Penrose pseudoinverse
`A_k⁺ = (A_k)⁺`. -/
def powellYuanSection13325
    (ck : EuclideanSpace ℝ (Fin m))
    (Ak : Matrix (Fin n) (Fin m) ℝ)
    (trustRegionRadius ξk b2 : ℝ) : Prop :=
  (b2 * trustRegionRadius ≥ ‖(Ak⁺).transpose.toEuclideanLin ck‖ → ξk = 0) ∧
    (b2 * trustRegionRadius < ‖(Ak⁺).transpose.toEuclideanLin ck‖ →
      ξk ≤ ‖ck - Ak.transpose.toEuclideanLin
          (((b2 * trustRegionRadius) / ‖(Ak⁺).transpose.toEuclideanLin ck‖) •
            (Ak⁺).transpose.toEuclideanLin ck)‖)

/-- Unfolding `powellYuanSection13325 ck Ak trustRegionRadius ξk b2` recovers the two source
branches from `(13.3.25)`. -/
theorem powellYuanSection13325_iff
    (ck : EuclideanSpace ℝ (Fin m))
    (Ak : Matrix (Fin n) (Fin m) ℝ)
    (trustRegionRadius ξk b2 : ℝ) :
    powellYuanSection13325 ck Ak trustRegionRadius ξk b2 ↔
      (b2 * trustRegionRadius ≥ ‖(Ak⁺).transpose.toEuclideanLin ck‖ → ξk = 0) ∧
        (b2 * trustRegionRadius < ‖(Ak⁺).transpose.toEuclideanLin ck‖ →
          ξk ≤ ‖ck - Ak.transpose.toEuclideanLin
              (((b2 * trustRegionRadius) / ‖(Ak⁺).transpose.toEuclideanLin ck‖) •
                (Ak⁺).transpose.toEuclideanLin ck)‖) :=
  Iff.rfl

#print axioms powellYuanSection13325
#print axioms powellYuanSection13325_iff

end
