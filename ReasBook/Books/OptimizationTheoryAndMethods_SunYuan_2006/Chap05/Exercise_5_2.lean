/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.PiL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Exercise_4_3

-- The extended Rosenbrock benchmark already has a source-facing owner in Chapter 4, so this
-- BFGS exercise reuses that declaration and keeps only the genuinely new Powell test function as
-- a direct objective owner.

/-- The standard Powell singular objective
`x ↦ (x 0 + 10 * x 1)^2 + 5 * (x 2 - x 3)^2 + (x 1 - 2 * x 2)^4 + 10 * (x 0 - x 3)^4`
on `ℝ⁴`. -/
def powellSingularFunction (x : EuclideanSpace ℝ (Fin 4)) : ℝ :=
  (x 0 + (10 : ℝ) * x 1) ^ (2 : ℕ) +
    (5 : ℝ) * (x 2 - x 3) ^ (2 : ℕ) +
    (x 1 - (2 : ℝ) * x 2) ^ (4 : ℕ) +
    (10 : ℝ) * (x 0 - x 3) ^ (4 : ℕ)

/-
Chapter05 Exercise 5.2: use the BFGS method to minimize
`extendedRosenbrockFunction` from Appendix 1.2 and `powellSingularFunction`
from Appendix 1.4.
-/
#check extendedRosenbrockFunction
#check powellSingularFunction
