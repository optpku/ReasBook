/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap08.Definition_8_1_1

/-
Chapter08 Definition 8.1.5: the active-set owner surface is already provided upstream by
`ConstrainedOptimizationProblem.activeIneqIndexSet` and
`ConstrainedOptimizationProblem.activeConstraintIndexSet` in `Definition_8_1_1`.
-/
#check ConstrainedOptimizationProblem.activeIneqIndexSet
#check ConstrainedOptimizationProblem.activeConstraintIndexSet
