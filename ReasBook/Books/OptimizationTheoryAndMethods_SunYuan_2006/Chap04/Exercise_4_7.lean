/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap04.Theorem_4_2_1

section

variable (n : ℕ)

/-- The `n × n` Hilbert matrix with entries `1 / (i + j + 1)` in zero-based `Fin`
coordinates, corresponding to the textbook formula `1 / (i + j - 1)` with indices
starting at `1`. -/
noncomputable def hilbertMatrix : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦ (1 : ℝ) / (((i : ℕ) + (j : ℕ) + 1 : ℕ) : ℝ)

/-- The vector `b = (1, 1, ..., 1)ᵀ` from Exercise 4.7. -/
def hilbertOnes : Fin n → ℝ :=
  1

/-- The initial point `x^(0) = 0` from Exercise 4.7. -/
def hilbertInitialPoint : Fin n → ℝ :=
  0

/-- The offset vector `c = -b` that rewrites the source objective as the linear-system
quadratic associated to `hilbertMatrix n` and `hilbertMatrix n`.mulVec x + c = 0`. -/
def hilbertConjugateGradientOffset : Fin n → ℝ :=
  -(hilbertOnes n)

/-- The three concrete dimensions requested in Exercise 4.7. -/
def hilbertExerciseDimensions : List ℕ :=
  [5, 10, 20]

-- Domain-style sampling summary:
-- * primary domain: finite-dimensional linear algebra for linear conjugate gradient on
--   quadratic objectives;
-- * inspected owners: `quadraticObjective` in Chapter 4.1,
--   `LinearConjugateGradientMethod` in Chapter 4.2, and the local Hilbert-specific data below;
-- * owner choice: `quadraticObjective (hilbertMatrix n) (hilbertConjugateGradientOffset n) 0`
--   is the canonical objective surface in the current import closure here, while
--   `hilbertMatrix`, `hilbertOnes`, `hilbertInitialPoint`, and
--   `hilbertConjugateGradientOffset` are the source-facing primitive exercise data.

/- Chapter04 Exercise 4.7: using the linear conjugate gradient method, minimize
`quadraticObjective (hilbertMatrix n) (hilbertConjugateGradientOffset n) 0` with
initial point `hilbertInitialPoint n`; equivalently, solve `hilbertMatrix n`.mulVec x +
hilbertConjugateGradientOffset n = 0` in the concrete cases
`n ∈ hilbertExerciseDimensions`. -/
#check hilbertMatrix 5
#check quadraticObjective (hilbertMatrix 5) (hilbertConjugateGradientOffset 5) 0
#check quadraticObjective (hilbertMatrix 10) (hilbertConjugateGradientOffset 10) 0
#check quadraticObjective (hilbertMatrix 20) (hilbertConjugateGradientOffset 20) 0
#check hilbertInitialPoint 5
#check hilbertConjugateGradientOffset 5
#check hilbertExerciseDimensions

end
