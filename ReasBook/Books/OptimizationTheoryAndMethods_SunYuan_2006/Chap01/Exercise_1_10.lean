/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_2_23

-- Domain sampling pass: the owner abstraction in this neighborhood is the theorem
-- `cubicRemainderBound_of_hessian_lipschitzOn`, with the source-facing centered/basepoint bridge
-- `cubicRemainderBound_of_hessian_basepointLipschitzOn` in `Theorem_1_2_23.lean`.

/-
Chapter01 Exercise 1.10

Recall-only entry: this exercise asks for Theorem 1.2.23, whose owner declaration is
`cubicRemainderBound_of_hessian_lipschitzOn`.
-/
#check cubicRemainderBound_of_hessian_lipschitzOn
