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
--   source-facing: the concrete Exercise 9.14 quadratic program and its optimizer
--   core/canonical: `QuadraticProgram` with its objective/coercion and feasible-set API
--   bridge/view: the displayed polynomial and inequality characterizations below
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

/-- The linear term `(-1000, -1000)ᵀ` in the Exercise 9.14 quadratic objective. -/
def chapter09Exercise914LinearTerm : Point :=
  point ![(-1000 : ℝ), -1000]

/-- The Hessian matrix `[[2, 0], [0, 2]]` in the Exercise 9.14 quadratic objective. -/
def chapter09Exercise914Hessian : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.diagonal fun _ ↦ (2 : ℝ)

/-- The inequality matrix encoding
`3 ≤ 3 * x 0 + x 1`, `4 ≤ x 0 + 4 * x 1`, `0 ≤ x 0`, and `0 ≤ x 1`. -/
def chapter09Exercise914ConstraintMatrix : ConstraintMatrix :=
  !![(3 : ℝ), 1; 1, 4; 1, 0; 0, 1]

/-- The right-hand side vector `(3, 4, 0, 0)ᵀ` for the Exercise 9.14 inequality system. -/
def chapter09Exercise914ConstraintBound : EuclideanSpace ℝ (Fin 4) :=
  constraintPoint ![(3 : ℝ), 4, 0, 0]

/-- The solution point of Exercise 9.14 is `(500, 500)ᵀ`. -/
def chapter09Exercise914Optimizer : Point :=
  point ![(500 : ℝ), (500 : ℝ)]

/-- The concrete quadratic-program owner for Exercise 9.14. -/
def chapter09Exercise914Problem : QuadraticProgram 2 0 4 where
  G := chapter09Exercise914Hessian
  hG_symm := Matrix.isSymm_diagonal (fun _ : Fin 2 ↦ (2 : ℝ))
  g := chapter09Exercise914LinearTerm
  Aeq := 0
  beq := 0
  Aineq := chapter09Exercise914ConstraintMatrix
  bineq := chapter09Exercise914ConstraintBound

/-- Evaluating `chapter09Exercise914Problem` as a function recovers the source objective
formula. -/
@[simp] theorem chapter09Exercise914Problem_apply (x : Point) :
    chapter09Exercise914Problem x =
      x 0 ^ (2 : ℕ) + x 1 ^ (2 : ℕ) - 1000 * x 0 - 1000 * x 1 := by
  simp [QuadraticProgram.objective, chapter09Exercise914Problem,
    chapter09Exercise914Hessian, chapter09Exercise914LinearTerm, point, dotProduct,
    Fin.sum_univ_two]
  ring

/-- Membership in `chapter09Exercise914Problem.feasibleSet` is exactly the displayed source
inequalities. -/
@[simp] theorem mem_chapter09Exercise914Problem_feasibleSet_iff (x : Point) :
    x ∈ chapter09Exercise914Problem.feasibleSet ↔
      3 ≤ 3 * x 0 + x 1 ∧
        4 ≤ x 0 + 4 * x 1 ∧ 0 ≤ x 0 ∧ 0 ≤ x 1 := by
  constructor
  · rintro ⟨_, hIneq⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 0
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 1
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 2
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using hIneq 3
  · rintro ⟨h0, h1, h2, h3⟩
    refine ⟨by ext i; exact Fin.elim0 i, ?_⟩
    intro i
    fin_cases i
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h0
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h1
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h2
    · simpa [chapter09Exercise914Problem, chapter09Exercise914ConstraintMatrix,
        chapter09Exercise914ConstraintBound, constraintPoint, Fin.sum_univ_two,
        vecHead, vecTail] using h3

/-- Completing the square rewrites the Exercise 9.14 objective as the sum of two shifted
squares minus `500000`. -/
theorem chapter09Exercise914_objective_eq_completedSquare (x : Point) :
    chapter09Exercise914Problem x =
      (x 0 - 500) ^ (2 : ℕ) + (x 1 - 500) ^ (2 : ℕ) - 500000 := by
  rw [chapter09Exercise914Problem_apply]
  ring

/-- The explicit optimizer `(500, 500)ᵀ` satisfies the four source inequalities defining
`chapter09Exercise914Problem.feasibleSet`. -/
theorem chapter09Exercise914Optimizer_mem_feasibleSet :
    chapter09Exercise914Optimizer ∈ chapter09Exercise914Problem.feasibleSet := by
  rw [mem_chapter09Exercise914Problem_feasibleSet_iff]
  norm_num [chapter09Exercise914Optimizer, point]

/-- Chapter09 Exercise 9.14: the canonical `QuadraticProgram` formulation of the exercise,
equivalently the problem with constraints
`3 ≤ 3 * x 0 + x 1`, `4 ≤ x 0 + 4 * x 1`, `0 ≤ x 0`, and `0 ≤ x 1`,
is minimized at `(500, 500)ᵀ`. -/
theorem chapter09Exercise914_isMinOn :
    IsMinOn
      chapter09Exercise914Problem
      chapter09Exercise914Problem.feasibleSet
      chapter09Exercise914Optimizer := by
  rw [isMinOn_iff]
  intro x hx
  have hOptimizer :
      chapter09Exercise914Problem chapter09Exercise914Optimizer = -500000 := by
    rw [chapter09Exercise914_objective_eq_completedSquare]
    norm_num [chapter09Exercise914Optimizer, point]
  rw [hOptimizer, chapter09Exercise914_objective_eq_completedSquare]
  nlinarith [sq_nonneg (x 0 - 500), sq_nonneg (x 1 - 500)]

/-- The optimal value of the solved Exercise 9.14 quadratic program is `-500000`. -/
theorem chapter09Exercise914_optimalValue :
    chapter09Exercise914Problem chapter09Exercise914Optimizer = -500000 := by
  rw [chapter09Exercise914_objective_eq_completedSquare]
  norm_num [chapter09Exercise914Optimizer, point]

end
