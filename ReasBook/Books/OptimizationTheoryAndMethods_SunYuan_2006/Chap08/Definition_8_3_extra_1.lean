/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_3_1

section Chapter08Definition83Extra1

variable {n m : ℕ} {E I : Set (Fin m)}

local notation "Point" => EuclideanSpace ℝ (Fin n)

/- Chapter08 Definition 8.3-extra-1: the source's strong active constraint index set
`I₊(xStar)` is already owned by
`ConstrainedOptimizationProblem.positiveActiveIneqIndexSet` in
`Definition_8_3_1.lean`. This file therefore stays at the recall layer and reuses that
canonical Chapter 8 owner directly instead of keeping a duplicate local alias. -/

#check ConstrainedOptimizationProblem.positiveActiveIneqIndexSet
#check ConstrainedOptimizationProblem.mem_positiveActiveIneqIndexSet_iff

namespace ConstrainedOptimizationProblem

/-- Every index in `positiveActiveIneqIndexSet xStar lamStar` is an active inequality
constraint at `xStar`. -/
theorem positiveActiveIneqIndexSet_subset_activeIneqIndexSet
    (problem : ConstrainedOptimizationProblem n m E I)
    (xStar : Point) (lamStar : Fin m → ℝ) :
    problem.positiveActiveIneqIndexSet xStar lamStar ⊆ problem.activeIneqIndexSet xStar := by
  intro i hi
  exact (problem.mem_positiveActiveIneqIndexSet_iff xStar lamStar i).1 hi |>.1

end ConstrainedOptimizationProblem

end Chapter08Definition83Extra1
