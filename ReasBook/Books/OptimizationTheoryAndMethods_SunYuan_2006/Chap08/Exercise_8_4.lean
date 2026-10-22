/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_2

noncomputable section

section Chapter08Exercise84

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => Fin n → ℝ

namespace ConstrainedOptimizationProblem

/- Domain sampling:
* primary domain: Chapter 8 null-constraint directions for constrained optimization
* inspected project owners:
  `ConstrainedOptimizationProblem.sequentialNullConstraintDirections_subset_posTangentConeAt`
  and
  `ConstrainedOptimizationProblem.linearizedNullConstraintDirections_subset_linearizedFeasible`
  from `Definition_8_3_2`
* source/core/bridge triage:
  - source-facing exercise content:
    formulas `(8.3.16)` and `(8.3.17)`
  - core/canonical owners:
    `posTangentConeAt problem.feasibleSet xStar` for
    `SFD(xStar, problem.feasibleSet)` and
    `problem.linearizedFeasibleDirectionSet xStar`
  - bridge/view choice here:
    both formulas are now recall-layer items because the owner file
    `Definition_8_3_2` already carries the source-facing bridge for `(8.3.16)`
    and the canonical theorem for `(8.3.17)`
-/

/- Chapter08 Exercise 8.4 (1): formula `(8.3.16)` is already the Chapter 8 theorem
`ConstrainedOptimizationProblem.sequentialNullConstraintDirections_subset_posTangentConeAt`
from `Definition_8_3_2`. -/
#check ConstrainedOptimizationProblem.sequentialNullConstraintDirections_subset_posTangentConeAt

end ConstrainedOptimizationProblem

/- Chapter08 Exercise 8.4 (2): formula `(8.3.17)` is already the Chapter 8 theorem
`ConstrainedOptimizationProblem.linearizedNullConstraintDirections_subset_linearizedFeasible`. -/
#check ConstrainedOptimizationProblem.linearizedNullConstraintDirections_subset_linearizedFeasible

end Chapter08Exercise84
