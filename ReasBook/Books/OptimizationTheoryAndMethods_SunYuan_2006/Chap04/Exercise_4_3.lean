/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap03.Exercise_3_4

open scoped BigOperators

-- Domain sampling:
-- * source-facing owner upstream: `Chapter03.Exercise_3_4.rosenbrockFunction`
-- * heavier project packaging: `OptimizationProblem`
-- * nearby concrete-objective style: `Chapter04.Exercise_4_2`
-- The present exercise only names benchmark objectives, so the right public surface is the
-- objective functions themselves, not a packaged optimization problem or public point aliases.

section

variable (n : ℕ)

local notation "Point" => EuclideanSpace ℝ (Fin n × Fin 2)

/-- The standard extended Rosenbrock objective on `n` coordinate pairs:
`∑ i, 100 * (x (i, 1) - (x (i, 0))^2)^2 + (1 - x (i, 0))^2`. -/
def extendedRosenbrockFunction (x : Point) : ℝ :=
  ∑ i : Fin n,
    ((100 : ℝ) * (x (i, 1) - (x (i, 0)) ^ (2 : ℕ)) ^ (2 : ℕ) +
      (1 - x (i, 0)) ^ (2 : ℕ))

end

-- Semantic recall: this computational exercise does not have a canonical
-- convergence theorem in mathlib, so the main entry is a labeled exercise block
-- that records the two objective functions to be minimized in later stages.
/-
Chapter04 Exercise 4.3: using the Fletcher-Reeves conjugate-gradient method,
minimize `rosenbrockFunction` from Appendix 1.1; using the
Polak-Ribiere-Polyak conjugate-gradient method, minimize
`extendedRosenbrockFunction` from Appendix 1.2.
-/
#check rosenbrockFunction
#check extendedRosenbrockFunction
