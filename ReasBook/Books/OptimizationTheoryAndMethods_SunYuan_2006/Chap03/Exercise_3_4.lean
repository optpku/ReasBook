/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Fin.VecNotation

noncomputable section

-- Domain sampling:
-- * `IsMinOn` is the canonical mathlib owner for minimizers.
-- * `extendedRosenbrockFunction` in Chapter 4 and the constrained Rosenbrock data in Chapter 12
--   are downstream views of the same benchmark family.
-- Source/core/bridge triage:
-- * source-facing: the standard Rosenbrock benchmark on `ℝ²` and its named points.
-- * core/canonical: the shared carrier `rosenbrockPoint` and objective `rosenbrockFunction`.
-- * bridge/view: later extended or constrained Rosenbrock variants.

/-- The ambient carrier `ℝ²` for the standard Rosenbrock benchmark. -/
abbrev rosenbrockPoint := EuclideanSpace ℝ (Fin 2)

/-- The Rosenbrock objective for Chapter03 Exercise 3.4:
`f(x) = 100 * (x 1 - (x 0)^2)^2 + (1 - x 0)^2` on `ℝ²`. -/
def rosenbrockFunction (x : rosenbrockPoint) : ℝ :=
  (100 : ℝ) * (x 1 - (x 0) ^ (2 : ℕ)) ^ (2 : ℕ) + (1 - x 0) ^ (2 : ℕ)

/-- The initial point `x^(0) = (-6 / 5, 1)` for the Rosenbrock test problem. -/
def rosenbrockInitialPoint : rosenbrockPoint :=
  !₂[-((6 : ℝ) / 5), 1]

/-- The reference minimizer `x* = (1, 1)` for the Rosenbrock test problem. -/
def rosenbrockMinimizer : rosenbrockPoint :=
  !₂[(1 : ℝ), 1]

/-- Helper for Chapter03 Exercise 3.4: the Rosenbrock objective is nonnegative everywhere. -/
lemma rosenbrockFunction_nonneg (x : rosenbrockPoint) :
    0 ≤ rosenbrockFunction x := by
  -- Each summand in the Rosenbrock objective is nonnegative.
  have hsq₁ : 0 ≤ (x 1 - (x 0) ^ (2 : ℕ)) ^ (2 : ℕ) := sq_nonneg _
  have hsq₂ : 0 ≤ (1 - x 0) ^ (2 : ℕ) := sq_nonneg _
  have hHundred : 0 ≤ (100 : ℝ) := by
    norm_num
  -- Combine the two nonnegative summands after unfolding the objective once.
  simpa [rosenbrockFunction] using add_nonneg (mul_nonneg hHundred hsq₁) hsq₂

/-- Helper for Chapter03 Exercise 3.4: the first coordinate of `rosenbrockMinimizer` is `1`. -/
lemma rosenbrockMinimizer_apply_zero :
    rosenbrockMinimizer 0 = 1 := by
  -- The benchmark minimizer is defined explicitly as `(1, 1)`.
  rfl

/-- Helper for Chapter03 Exercise 3.4: the second coordinate of `rosenbrockMinimizer` is `1`. -/
lemma rosenbrockMinimizer_apply_one :
    rosenbrockMinimizer 1 = 1 := by
  -- The benchmark minimizer is defined explicitly as `(1, 1)`.
  rfl

/-- Helper for Chapter03 Exercise 3.4: evaluating the Rosenbrock objective at `(1, 1)` gives `0`. -/
lemma rosenbrockFunction_eq_zero_atMinimizer :
    rosenbrockFunction rosenbrockMinimizer = 0 := by
  -- Rewrite the coordinates of the reference minimizer before normalizing the arithmetic.
  rw [rosenbrockFunction, rosenbrockMinimizer_apply_zero, rosenbrockMinimizer_apply_one]
  norm_num

/-- Chapter03 Exercise 3.4: the reference point `(1, 1)` is a global minimizer of the
Rosenbrock function. -/
theorem rosenbrockFunction_isMinOn :
    IsMinOn rosenbrockFunction Set.univ rosenbrockMinimizer := by
  -- Reduce minimization on the whole space to a pointwise lower bound.
  rw [isMinOn_univ_iff]
  intro x
  -- The minimizing value is zero, so pointwise nonnegativity closes the comparison.
  rw [rosenbrockFunction_eq_zero_atMinimizer]
  exact rosenbrockFunction_nonneg x

/-- The Rosenbrock function attains the value `0` at the reference minimizer `(1, 1)`. -/
theorem rosenbrockFunction_minimizer_eq_zero :
    rosenbrockFunction rosenbrockMinimizer = 0 := by
  -- Reuse the earlier direct evaluation of the objective at the benchmark minimizer.
  exact rosenbrockFunction_eq_zero_atMinimizer
