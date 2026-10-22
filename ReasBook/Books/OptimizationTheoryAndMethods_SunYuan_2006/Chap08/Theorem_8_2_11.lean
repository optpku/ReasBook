/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_2_10
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7

noncomputable section

section Chapter08Theorem8211

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/-- Chapter08 Theorem 8.2.11: let `xStar` be a feasible point. If each active constraint
`problem.constraint i` is differentiable at `xStar` and LICQ holds at `xStar`. Then the Chapter 8
constraint qualification `(8.2.19)` holds; equivalently, the linearized feasible direction set
agrees with `posTangentConeAt problem.feasibleSet xStar`. -/
theorem constraintQualificationAt_of_licqAt
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_licq : problem.LicqAt xStar) :
    problem.ConstraintQualificationAt xStar := by
  sorry

end ConstrainedOptimizationProblem

end Chapter08Theorem8211
