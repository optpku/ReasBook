/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

open Matrix

-- Domain sampling:
-- * primary domain: concrete quadratic programming on `ℝ²`
-- * inspected owner declarations:
--   `QuadraticProgram.objective`, `QuadraticProgram.feasibleSet`,
--   `QuadraticProgram.mem_feasibleSet_iff` from `Definition_9_1_extra_1`,
--   `IsMinOn` from mathlib
-- * best owner abstraction: the chapter's `QuadraticProgram`
-- * layer triage in this file:
--   source-facing: the concrete Exercise 9.15 quadratic program and its optimizer
--   core/canonical: `QuadraticProgram` with its objective/coercion and feasible-set API
--   bridge/view: the explicit polynomial and inequality characterizations below
-- * primitive data: Hessian, linear term, inequality matrix, inequality bound, optimizer
-- * derived API: the displayed objective formula, feasible-set membership, minimizer, and
--   optimal-value statements

noncomputable section

section

local notation "Point" => EuclideanSpace ℝ (Fin 2)
local notation "ConstraintMatrix" => Matrix (Fin 4) (Fin 2) ℝ

private abbrev point (x : Fin 2 → ℝ) : Point :=
  (EuclideanSpace.equiv (Fin 2) ℝ).symm x

private abbrev constraintPoint (x : Fin 4 → ℝ) : EuclideanSpace ℝ (Fin 4) :=
  (EuclideanSpace.equiv (Fin 4) ℝ).symm x

/-- The linear term `(-2, -6)ᵀ` in the Exercise 9.15 quadratic objective. -/
def chapter09Exercise915LinearTerm : Point :=
  point ![(-2 : ℝ), -6]

/-- The Hessian matrix `[[2, -2], [-2, 4]]` in the Exercise 9.15 quadratic objective. -/
def chapter09Exercise915Hessian : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(2 : ℝ), -2; -2, 4]

/-- The inequality matrix encoding
`(1 / 2) * x 0 + (1 / 2) * x 1 ≤ 1`, `-x 0 + x 1 ≤ 2`, `0 ≤ x 0`, and `0 ≤ x 1`. -/
def chapter09Exercise915ConstraintMatrix : ConstraintMatrix :=
  !![(-1 : ℝ), -1; 1, -1; 1, 0; 0, 1]

/-- The right-hand side vector `(-2, -2, 0, 0)ᵀ` for the Exercise 9.15 inequality system. -/
def chapter09Exercise915ConstraintBound : EuclideanSpace ℝ (Fin 4) :=
  constraintPoint ![(-2 : ℝ), -2, 0, 0]

/-- The solution point of Exercise 9.15 is `(4 / 5, 6 / 5)ᵀ`. -/
def chapter09Exercise915Optimizer : Point :=
  point ![(4 / 5 : ℝ), (6 / 5 : ℝ)]

/-- The concrete quadratic-program owner for Exercise 9.15. -/
def chapter09Exercise915Problem : QuadraticProgram 2 0 4 where
  G := chapter09Exercise915Hessian
  hG_symm := by
    change chapter09Exercise915Hessian.transpose = chapter09Exercise915Hessian
    ext i j
    fin_cases i <;> fin_cases j <;> simp [chapter09Exercise915Hessian]
  g := chapter09Exercise915LinearTerm
  Aeq := 0
  beq := 0
  Aineq := chapter09Exercise915ConstraintMatrix
  bineq := chapter09Exercise915ConstraintBound

/-- Evaluating `chapter09Exercise915Problem` as a function recovers the source objective
formula. -/
@[simp] theorem chapter09Exercise915Problem_apply (x : Point) :
    chapter09Exercise915Problem x =
      x 0 ^ (2 : ℕ) + 2 * x 1 ^ (2 : ℕ) - 2 * x 0 - 6 * x 1 - 2 * x 0 * x 1 := by
  simp [QuadraticProgram.objective, chapter09Exercise915Problem,
    chapter09Exercise915Hessian, chapter09Exercise915LinearTerm, point, dotProduct,
    Fin.sum_univ_two]
  ring

/-- Membership in `chapter09Exercise915Problem.feasibleSet` is exactly the displayed source
inequalities. -/
@[simp] theorem mem_chapter09Exercise915Problem_feasibleSet_iff (x : Point) :
    x ∈ chapter09Exercise915Problem.feasibleSet ↔
      (1 / 2 : ℝ) * x 0 + (1 / 2 : ℝ) * x 1 ≤ 1 ∧
        -x 0 + x 1 ≤ 2 ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  constructor
  · rintro ⟨_, hIneq⟩
    have h0 : (-2 : ℝ) ≤ -(x 1 + x 0) := by
      simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 0
    have h1 : (-2 : ℝ) ≤ x 0 - x 1 := by
      simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail, add_comm, add_left_comm, add_assoc] using hIneq 1
    have h2 : (0 : ℝ) ≤ x 0 := by
      simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 2
    have h3 : (0 : ℝ) ≤ x 1 := by
      simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 3
    refine ⟨?_, ?_, h2, h3⟩
    · linarith
    · linarith
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨by ext i; exact Fin.elim0 i, ?_⟩
    intro i
    fin_cases i
    · have h : (-2 : ℝ) ≤ -(x 1 + x 0) := by
        linarith
      simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h
    · have h : (-2 : ℝ) ≤ x 0 - x 1 := by
        linarith
      simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail, add_comm, add_left_comm, add_assoc] using h
    · simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h2
    · simpa [chapter09Exercise915Problem, chapter09Exercise915ConstraintMatrix,
        chapter09Exercise915ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h3

/-- Completing the square rewrites the Exercise 9.15 objective as
`(x 0 - x 1 - 1)^2 + (x 1 - 4)^2 - 17`. -/
theorem chapter09Exercise915_objective_eq_completedSquare (x : Point) :
    chapter09Exercise915Problem x =
      (x 0 - x 1 - 1) ^ (2 : ℕ) + (x 1 - 4) ^ (2 : ℕ) - 17 := by
  rw [chapter09Exercise915Problem_apply]
  ring

/-- The explicit optimizer `(4 / 5, 6 / 5)ᵀ` satisfies the four source inequalities defining
`chapter09Exercise915Problem.feasibleSet`. -/
theorem chapter09Exercise915Optimizer_mem_feasibleSet :
    chapter09Exercise915Optimizer ∈ chapter09Exercise915Problem.feasibleSet := by
  rw [mem_chapter09Exercise915Problem_feasibleSet_iff]
  norm_num [chapter09Exercise915Optimizer, point]

/-- Chapter09 Exercise 9.15: the canonical `QuadraticProgram` formulation of the exercise,
equivalently the problem with constraints
`(1 / 2) * x 0 + (1 / 2) * x 1 ≤ 1`, `-x 0 + x 1 ≤ 2`, `0 ≤ x 0`, and `0 ≤ x 1`,
is minimized at `(4 / 5, 6 / 5)ᵀ`. -/
theorem chapter09Exercise915_isMinOn :
    IsMinOn
      chapter09Exercise915Problem
      chapter09Exercise915Problem.feasibleSet
      chapter09Exercise915Optimizer := by
  rw [isMinOn_iff]
  intro x hx
  have hx0 : (1 / 2 : ℝ) * x 0 + (1 / 2 : ℝ) * x 1 ≤ 1 := by
    exact (mem_chapter09Exercise915Problem_feasibleSet_iff x).mp hx |>.1
  have hOptimizer :
      chapter09Exercise915Problem chapter09Exercise915Optimizer = -(36 / 5 : ℝ) := by
    rw [chapter09Exercise915Problem_apply]
    norm_num [chapter09Exercise915Optimizer, point]
  rw [hOptimizer]
  have hxslack : (0 : ℝ) ≤ 2 - x 0 - x 1 := by
    linarith
  have hsq0 : (0 : ℝ) ≤ (x 1 - 6 / 5) ^ (2 : ℕ) := by
    nlinarith
  have hsq1 : (0 : ℝ) ≤ (x 0 - x 1 + 2 / 5) ^ (2 : ℕ) := by
    nlinarith
  have hNonneg :
      (0 : ℝ) ≤
        (x 1 - 6 / 5) ^ (2 : ℕ) +
          (x 0 - x 1 + 2 / 5) ^ (2 : ℕ) +
            (14 / 5 : ℝ) * (2 - x 0 - x 1) := by
    nlinarith
  have hDecomp :
      chapter09Exercise915Problem x + (36 / 5 : ℝ) =
        (x 1 - 6 / 5) ^ (2 : ℕ) +
          (x 0 - x 1 + 2 / 5) ^ (2 : ℕ) +
            (14 / 5 : ℝ) * (2 - x 0 - x 1) := by
    rw [chapter09Exercise915Problem_apply]
    ring
  nlinarith

/-- The optimal value of the solved Exercise 9.15 quadratic program is `-36 / 5`. -/
theorem chapter09Exercise915_optimalValue :
    chapter09Exercise915Problem chapter09Exercise915Optimizer = -(36 / 5 : ℝ) := by
  rw [chapter09Exercise915Problem_apply]
  norm_num [chapter09Exercise915Optimizer, point]

end
