/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Theorem_8_2_7
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Corollary_8_2_9

noncomputable section

section Chapter08Exercise83

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/-- Chapter08 Exercise 8.3: if every active constraint `cᵢ` of `problem` at the feasible point
`xStar` is linear, then the Chapter 8 constraint qualification `(8.2.19)` holds at `xStar`. This
is the source-facing bridge to the canonical owner `problem.LfcqAt xStar`. -/
theorem constraintQualificationAt_of_activeConstraints_linear
    (problem : ConstrainedOptimizationProblem n m E I) (xStar : Point)
    (hxStar : xStar ∈ problem)
    (h_linear :
      ∀ i ∈ problem.activeConstraintIndexSet xStar,
        ∃ ci : Point →ₗ[ℝ] ℝ, problem.constraint i = ci) :
    problem.ConstraintQualificationAt xStar := by
  have h_lfcq : problem.LfcqAt xStar := (problem.lfcqAt_iff xStar).2 h_linear
  exact problem.constraintQualificationAt_of_lfcqAt xStar hxStar h_lfcq

end ConstrainedOptimizationProblem

end Chapter08Exercise83
