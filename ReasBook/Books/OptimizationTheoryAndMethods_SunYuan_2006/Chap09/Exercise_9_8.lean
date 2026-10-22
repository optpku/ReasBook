/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Theorem_9_1_3

open Matrix

noncomputable section

local notation "Point" => EuclideanSpace ℝ (Fin 2)

private def point (x₀ x₁ : ℝ) : Point :=
  EuclideanSpace.single 0 x₀ + EuclideanSpace.single 1 x₁

-- Domain-style sampling for this item:
-- * primary domain: quadratic programming with affine equality constraints in Chapter 9.
-- * inspected project declarations:
--   - `QuadraticProgram`, `.objective`, and `.feasibleSet` from
--     `Definition_9_1_extra_1`;
--   - the earlier equality-constrained bridge `EqualityConstrainedQuadraticProgram` from
--     `Problem_9_3_extra_1`, whose extra rank packaging is not primitive data for this exercise.
-- * source/core/bridge triage:
--   - source-facing owner here: the concrete one-constraint quadratic program
--     `chapter09Exercise98Problem`;
--   - core/canonical owner upstream: `QuadraticProgram 2 1 0`;
--   - bridge/view reused here: `QuadraticProgram.objective` and `QuadraticProgram.feasibleSet`.
-- * primitive data: the linear term, Hessian, single equality-constraint vector, and
--   right-hand side, packaged once as the quadratic-program owner.
-- * derived API here: the displayed objective formula, feasible-set characterization, affine
--   parametrization, optimizer, and optimality statements.

/-- The linear term `(1, -1)ᵀ` in the Exercise 9.8 quadratic objective. -/
def chapter09Exercise98LinearTerm : Point :=
  point 1 (-1)

/-- The Hessian matrix `[[1, 2], [2, 4]]` in the Exercise 9.8 quadratic objective. -/
def chapter09Exercise98Hessian : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(1 : ℝ), 2; 2, 4]

/-- The affine equality-constraint vector `(1, 1)ᵀ` for the source condition `x 0 + x 1 = 1`. -/
def chapter09Exercise98ConstraintVector : Point :=
  point 1 1

/-- The equality right-hand side `1` of the source constraint `x 0 + x 1 = 1`. -/
def chapter09Exercise98ConstraintRhs : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 1

/-- The quadratic program from Exercise 9.8, viewed through the Chapter 9 owner
`QuadraticProgram 2 1 0` with one equality constraint and no inequality constraints. -/
def chapter09Exercise98Problem : QuadraticProgram 2 1 0 where
  G := chapter09Exercise98Hessian
  hG_symm := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [chapter09Exercise98Hessian]
  g := chapter09Exercise98LinearTerm
  Aeq := !![(1 : ℝ), 1]
  beq := chapter09Exercise98ConstraintRhs
  Aineq := 0
  bineq := 0

/-- Expanding `chapter09Exercise98Problem.objective` recovers the source objective
`(1, -1)ᵀ x + (1 / 2) * xᵀ [[1, 2], [2, 4]] x`. -/
theorem chapter09Exercise98_objective_apply (x : Point) :
    chapter09Exercise98Problem.objective x =
      dotProduct chapter09Exercise98LinearTerm x +
        (1 / 2 : ℝ) * dotProduct x (chapter09Exercise98Hessian.mulVec x) := sorry

/-- Membership in `chapter09Exercise98Problem.feasibleSet` is exactly the source equality
constraint `x 0 + x 1 = 1`. -/
theorem chapter09Exercise98_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter09Exercise98Problem.feasibleSet ↔ x 0 + x 1 = 1 := sorry

/-- The parametrization `x = (t, 1 - t)ᵀ` of the Exercise 9.8 feasible set. -/
def chapter09Exercise98Parametrization (t : ℝ) : Point :=
  point t (1 - t)

/-- The solution point `(0, 1)ᵀ` of the Exercise 9.8 equality-constrained quadratic program. -/
def chapter09Exercise98Optimizer : Point :=
  point 0 1

/-- Every feasible point of `chapter09Exercise98Problem.feasibleSet` is obtained from the affine
parametrization `x = (t, 1 - t)ᵀ` with `t = x 0`. -/
theorem chapter09Exercise98_eq_parametrization_of_mem_feasibleSet
    (x : Point) (hx : x ∈ chapter09Exercise98Problem.feasibleSet) :
    x = chapter09Exercise98Parametrization (x 0) := sorry

/-- Substituting the feasible-set parametrization into `chapter09Exercise98Problem.objective`
yields the reduced one-variable objective `t ↦ (1 / 2) * t^2 + 1`. -/
theorem chapter09Exercise98_objective_eq_reducedObjective (t : ℝ) :
    chapter09Exercise98Problem.objective (chapter09Exercise98Parametrization t) =
      (1 / 2 : ℝ) * t ^ (2 : ℕ) + 1 := sorry

/-- Chapter09 Exercise 9.8 (1): the equality-constrained quadratic program with objective
`(1, -1)ᵀ x + (1 / 2) * xᵀ [[1, 2], [2, 4]] x` and constraint `x 0 + x 1 = 1` is minimized at
`(0, 1)ᵀ`. -/
theorem chapter09Exercise98_isMinOn :
    IsMinOn
      chapter09Exercise98Problem.objective
      chapter09Exercise98Problem.feasibleSet
      chapter09Exercise98Optimizer := sorry

/-- Chapter09 Exercise 9.8 (2): the optimal value of the equality-constrained quadratic program
is `1`. -/
theorem chapter09Exercise98_optimalValue :
    chapter09Exercise98Problem.objective chapter09Exercise98Optimizer = 1 := sorry
