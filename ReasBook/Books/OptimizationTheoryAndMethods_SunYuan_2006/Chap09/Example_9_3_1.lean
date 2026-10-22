/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Rank
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Definition_9_1_extra_1

open Matrix

-- Semantic recall: Chapter 9 already provides the canonical owner
-- `EqualityConstrainedQuadraticProgram` for equality-constrained quadratic programs. This example
-- is therefore recorded as a concrete source-facing problem together with the solved point,
-- multiplier, and textbook bridge lemmas back to the displayed formulas.

noncomputable section

local notation "Point" => EuclideanSpace ℝ (Fin 3)
local notation "MultiplierPoint" => EuclideanSpace ℝ (Fin 2)
local notation "ConstraintMatrix" => Matrix (Fin 3) (Fin 2) ℝ

/-- Helper for Chapter09 Example 9.3.1: a quadratic program is evaluated by its quadratic
objective, matching the source-facing `P x` notation used in this example. -/
-- Local instance justification (notation bridge): this file records the source-facing objective
-- as `P x`, but the canonical owner `QuadraticProgram` only exposes `objective` explicitly.
local instance quadraticProgramCoeFun {n me mi : ℕ} :
    CoeFun (QuadraticProgram n me mi)
      (fun _ ↦ EuclideanSpace ℝ (Fin n) → ℝ) where
  coe P := P.objective

namespace QuadraticProgram

/-- Helper for Chapter09 Example 9.3.1: for an equality-only quadratic program, the source
constraint matrix `A` is the transpose of the canonical equality block `Aeq`. -/
abbrev A {n m : ℕ} (P : QuadraticProgram n m 0) : Matrix (Fin n) (Fin m) ℝ :=
  P.Aeqᵀ

/-- Helper for Chapter09 Example 9.3.1: full column rank for an equality-only quadratic program
means `Matrix.rank P.A = m`. -/
def HasFullColumnRank {n m : ℕ} (P : QuadraticProgram n m 0) : Prop :=
  Matrix.rank P.A = m

end QuadraticProgram

/-- The Hessian matrix `diag(2, -2, -2)` encoding the quadratic form
`x 0^2 - x 1^2 - x 2^2` from Example 9.3.1. -/
def chapter09Example931Hessian : Matrix (Fin 3) (Fin 3) ℝ :=
  !![(2 : ℝ), 0, 0; 0, -2, 0; 0, 0, -2]

/-- The constraint matrix `A = [[1, 0], [1, 1], [1, -1]]` used in the stationarity equation
`g* = A λ*`. -/
def chapter09Example931ConstraintMatrix : ConstraintMatrix :=
  !![(1 : ℝ), 0; 1, 1; 1, -1]

/-- Helper for Chapter09 Example 9.3.1: `G x` is computed coordinatewise as
`(2 * x 0, -2 * x 1, -2 * x 2)`. -/
private theorem chapter09Example931_hessian_mulVec (x : Point) :
    chapter09Example931Hessian.mulVec x = ![2 * x 0, -2 * x 1, -2 * x 2] := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, chapter09Example931Hessian]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, chapter09Example931Hessian]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, chapter09Example931Hessian]

/-- Helper for Chapter09 Example 9.3.1: `Aᵀ x` records the two constraint left-hand sides
`x 0 + x 1 + x 2` and `x 1 - x 2`. -/
private theorem chapter09Example931_constraintTranspose_mulVec (x : Point) :
    chapter09Example931ConstraintMatrixᵀ.mulVec x =
      !₂[x 0 + x 1 + x 2, x 1 - x 2] := by
  ext i
  fin_cases i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, chapter09Example931ConstraintMatrix]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, chapter09Example931ConstraintMatrix]
    ring

/-- Helper for Chapter09 Example 9.3.1: the concrete Hessian `diag(2, -2, -2)` is symmetric. -/
private theorem chapter09Example931Hessian_isSymm :
    chapter09Example931Hessian.IsSymm := by
  -- The matrix is diagonal, so symmetry reduces to checking finitely many coordinates.
  ext i j
  fin_cases i <;> fin_cases j <;> simp [chapter09Example931Hessian]

/-- Helper for Chapter09 Example 9.3.1: the concrete constraint matrix has full column rank. -/
private theorem chapter09Example931ConstraintMatrix_rank :
    Matrix.rank chapter09Example931ConstraintMatrix = 2 := by
  -- The last two rows already form an invertible `2 × 2` minor, so the full matrix has rank `2`.
  have hminorRank :
      Matrix.rank
        (chapter09Example931ConstraintMatrix.submatrix Fin.succ (fun j : Fin 2 => j)) = 2 := by
    have hminor :
        chapter09Example931ConstraintMatrix.submatrix Fin.succ (fun j : Fin 2 => j) =
          (!![(1 : ℝ), 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [chapter09Example931ConstraintMatrix]
    calc
      Matrix.rank (chapter09Example931ConstraintMatrix.submatrix Fin.succ (fun j : Fin 2 => j)) =
          Matrix.rank (!![(1 : ℝ), 1; 1, -1] : Matrix (Fin 2) (Fin 2) ℝ) := by
        rw [hminor]
      _ = 2 := by
        apply Matrix.rank_of_isUnit
        rw [Matrix.isUnit_iff_isUnit_det]
        norm_num [Matrix.det_fin_two]
  have hge : 2 ≤ Matrix.rank chapter09Example931ConstraintMatrix := by
    calc
      2 =
          Matrix.rank
            (chapter09Example931ConstraintMatrix.submatrix Fin.succ (fun j : Fin 2 => j)) :=
        hminorRank.symm
      _ ≤ Matrix.rank chapter09Example931ConstraintMatrix :=
        Matrix.rank_submatrix_le chapter09Example931ConstraintMatrix Fin.succ (fun j : Fin 2 => j)
  have hle : Matrix.rank chapter09Example931ConstraintMatrix ≤ 2 := by
    simpa using Matrix.rank_le_width chapter09Example931ConstraintMatrix
  exact le_antisymm hle hge

/-- The concrete equality-constrained quadratic program from Example 9.3.1, with objective
`x 0^2 - x 1^2 - x 2^2` and equality constraints
`x 0 + x 1 + x 2 = 1`, `x 1 - x 2 = 1`. -/
def chapter09Example931Problem : QuadraticProgram 3 2 0 where
  g := 0
  G := chapter09Example931Hessian
  Aeq := chapter09Example931ConstraintMatrixᵀ
  beq := !₂[(1 : ℝ), 1]
  Aineq := 0
  bineq := 0
  hG_symm := chapter09Example931Hessian_isSymm

/-- The example constraint matrix has full column rank, matching the textbook standing
assumption for the equality-constrained problem. -/
theorem chapter09Example931Problem_hasFullColumnRank :
    chapter09Example931Problem.HasFullColumnRank :=
  chapter09Example931ConstraintMatrix_rank

/-- Evaluating `chapter09Example931Problem` recovers the source objective
`Q(x) = x 0^2 - x 1^2 - x 2^2`. -/
theorem chapter09Example931_objective_apply (x : Point) :
    chapter09Example931Problem x =
      x 0 ^ (2 : ℕ) - x 1 ^ (2 : ℕ) - x 2 ^ (2 : ℕ) := by
  -- Expand the canonical quadratic-program objective and simplify the concrete diagonal Hessian.
  simp [QuadraticProgram.objective, chapter09Example931Problem,
    chapter09Example931_hessian_mulVec, dotProduct, Fin.sum_univ_three]
  ring

/-- Membership in `chapter09Example931Problem.feasibleSet` is exactly the pair of source
equalities `x 0 + x 1 + x 2 = 1` and `x 1 - x 2 = 1`. -/
theorem chapter09Example931_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter09Example931Problem.feasibleSet ↔
      x 0 + x 1 + x 2 = 1 ∧ x 1 - x 2 = 1 := by
  -- Rewrite feasibility as `Aᵀ x = b`, then read off the two coordinates of that equality.
  rw [QuadraticProgram.mem_feasibleSet_iff]
  simp [chapter09Example931Problem, chapter09Example931_constraintTranspose_mulVec]

/-- The parametrization `x = (-2 * t, t + 1, t)` obtained by eliminating `x 0` and `x 1`
from the constraints in Example 9.3.1. -/
def chapter09Example931Parametrization (t : ℝ) : Point :=
  !₂[-2 * t, t + 1, t]

/-- The solution point `(-1, 3 / 2, 1 / 2)ᵀ` obtained in Example 9.3.1. -/
def chapter09Example931Solution : Point :=
  !₂[(-1 : ℝ), 3 / 2, 1 / 2]

/-- The multiplier vector `(-2, -1)ᵀ` computed in Example 9.3.1. -/
def chapter09Example931Multipliers : MultiplierPoint :=
  !₂[(-2 : ℝ), -1]

/-- Evaluating `chapter09Example931Problem.G.mulVec chapter09Example931Solution` recovers the
source gradient vector `(-2, -3, -1)ᵀ`. -/
theorem chapter09Example931_gradientAtSolution_eq :
    chapter09Example931Problem.G.mulVec chapter09Example931Solution =
      ![(-2 : ℝ), -3, -1] := by
  -- Compute the Hessian action on the displayed solution coordinatewise.
  ext i
  fin_cases i <;> norm_num [chapter09Example931Problem, chapter09Example931Hessian,
    chapter09Example931Solution]

/-- Every feasible point of `chapter09Example931Problem.feasibleSet` is obtained by substituting
`x 1 = x 2 + 1` and `x 0 = -2 * x 2`. -/
theorem chapter09Example931_eq_parametrization_of_mem_feasibleSet
    (x : Point) (hx : x ∈ chapter09Example931Problem.feasibleSet) :
    x = chapter09Example931Parametrization (x 2) := by
  -- The two scalar constraints solve uniquely for `x 0` and `x 1`
  -- in terms of the free variable `x 2`.
  rcases (chapter09Example931_mem_feasibleSet_iff x).1 hx with ⟨hsum, hdiff⟩
  have hx1 : x 1 = x 2 + 1 := by
    linarith
  have hx0 : x 0 = -2 * x 2 := by
    linarith
  ext i
  fin_cases i
  · simpa [chapter09Example931Parametrization] using hx0
  · simpa [chapter09Example931Parametrization] using hx1
  · simp [chapter09Example931Parametrization]

/-- Substituting `x = (-2 * t, t + 1, t)` into `chapter09Example931Problem` yields the
reduced one-variable objective `4 * t^2 - (t + 1)^2 - t^2`. -/
theorem chapter09Example931_objective_eq_reducedObjective (t : ℝ) :
    chapter09Example931Problem (chapter09Example931Parametrization t) =
      4 * t ^ (2 : ℕ) - (t + 1) ^ (2 : ℕ) - t ^ (2 : ℕ) := by
  -- After the feasible-set parametrization,
  -- the objective becomes the scalar quadratic from the text.
  rw [chapter09Example931_objective_apply]
  simp [chapter09Example931Parametrization]
  ring

/-- Chapter09 Example 9.3.1 (1): the point `(-1, 3 / 2, 1 / 2)ᵀ` is a global solution of the
problem `min Q(x) = x 0^2 - x 1^2 - x 2^2` subject to
`x 0 + x 1 + x 2 = 1` and `x 1 - x 2 = 1`. -/
theorem chapter09Example931_isMinOn :
    IsMinOn
      chapter09Example931Problem
      chapter09Example931Problem.feasibleSet
      chapter09Example931Solution := by
  rw [isMinOn_iff]
  intro x hx
  have hparam : x = chapter09Example931Parametrization (x 2) :=
    chapter09Example931_eq_parametrization_of_mem_feasibleSet x hx
  have hsolution :
      chapter09Example931Solution = chapter09Example931Parametrization (1 / 2) := by
    -- Match the displayed optimizer with the feasible-set parametrization at `t = 1 / 2`.
    ext i
    fin_cases i <;> norm_num [chapter09Example931Solution, chapter09Example931Parametrization]
  -- Reduce the comparison to the one-variable quadratic and finish by square nonnegativity.
  rw [hsolution, hparam, chapter09Example931_objective_eq_reducedObjective,
    chapter09Example931_objective_eq_reducedObjective]
  nlinarith [sq_nonneg (x 2 - 1 / 2)]

/-- Chapter09 Example 9.3.1 (2): the multiplier vector `(-2, -1)ᵀ` satisfies the stationarity
equation `A λ* = g*`, where `A = chapter09Example931ConstraintMatrix` and
`g* = (-2, -3, -1)ᵀ`. -/
theorem chapter09Example931_lagrangeMultipliers :
    chapter09Example931Problem.A.mulVec chapter09Example931Multipliers =
      chapter09Example931Problem.G.mulVec chapter09Example931Solution :=
  by
  -- Compute the left-hand side and compare it with the already computed gradient vector.
  calc
    chapter09Example931Problem.A.mulVec chapter09Example931Multipliers =
        ![(-2 : ℝ), -3, -1] := by
      change chapter09Example931ConstraintMatrix.mulVec chapter09Example931Multipliers =
        ![(-2 : ℝ), -3, -1]
      ext i
      fin_cases i <;> norm_num [chapter09Example931ConstraintMatrix, chapter09Example931Multipliers]
    _ = chapter09Example931Problem.G.mulVec chapter09Example931Solution := by
      symm
      exact chapter09Example931_gradientAtSolution_eq

end
