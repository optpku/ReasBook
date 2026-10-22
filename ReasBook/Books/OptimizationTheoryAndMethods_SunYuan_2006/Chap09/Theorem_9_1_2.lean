/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_3
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_1_1

noncomputable section

section Chapter09Theorem912

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace QuadraticProgram

/-- Chapter09 Theorem 9.1.2: if `xStar` is a Chapter 8 KKT point of
`P.toConstrainedOptimizationProblem` with multiplier vector `λ*`, then positivity of `dᵀ G d`
on the Chapter 8 null-constraint directions implies that `xStar` is a strict local minimizer of
`P.objective` on `P.feasibleSet`. -/
theorem isStrictLocalMinOn_of_isKKTPoint_of_positive_on_linearizedNullConstraintDirections
    (P : QuadraticProgram n me mi) (xStar : Point) (lamStar : Fin (me + mi) → ℝ)
    (hKKT :
      P.toConstrainedOptimizationProblem.IsKKTPoint
        ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar)
    (hPositive :
      ∀ d : Point,
        (EuclideanSpace.equiv (Fin n) ℝ d) ∈
          P.toConstrainedOptimizationProblem.linearizedNullConstraintDirections
            ((EuclideanSpace.equiv (Fin n) ℝ) xStar) lamStar →
          0 < inner ℝ d (Matrix.toEuclideanLin P.G d)) :
    IsStrictLocalMinOn P.objective P.feasibleSet xStar := by
  sorry

end QuadraticProgram

end Chapter09Theorem912
