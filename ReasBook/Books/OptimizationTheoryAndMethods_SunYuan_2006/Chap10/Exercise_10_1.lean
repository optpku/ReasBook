/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Definition_10_1_extra_1

open Filter

noncomputable section

section

-- Semantic recall: Chapter 10 already owns the constrained-problem surface
-- `StandardPenaltyProblem` together with the canonical quadratic-penalty owner
-- `PenaltyFunction.quadratic`. This exercise therefore keeps only the source-facing objective,
-- constraint, and explicit minimizers, then specializes the chapter owners to the one-equality
-- problem `x 1 - (x 0)^2 = 0`.

local notation "Point" => EuclideanSpace ℝ (Fin 2)

/-- The linear objective `x ↦ -2 * x 0 + x 1` from Exercise 10.1. -/
def chapter10Exercise101Objective (x : Point) : ℝ :=
  -(2 : ℝ) * x 0 + x 1

/-- The single equality constraint `x 1 - (x 0)^2 = 0` from Exercise 10.1. -/
def chapter10Exercise101Constraint (x : Point) : ℝ :=
  x 1 - (x 0) ^ (2 : ℕ)

/-- The Exercise 10.1 problem viewed on Chapter 10's canonical
`StandardPenaltyProblem` surface: one equality constraint and no inequality constraints. -/
def chapter10Exercise101Problem : StandardPenaltyProblem 2 1 where
  eqCount := 1
  eqCount_le := le_rfl
  objective := chapter10Exercise101Objective
  constraint := fun _ ↦ chapter10Exercise101Constraint

/-- The feasible point `(1, 1)` solving the constrained problem in Exercise 10.1. -/
def chapter10Exercise101Optimizer : Point :=
  EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 : ℝ)

/-- For penalty parameter `σ`, the unconstrained Courant-penalty minimizer is
`(1, 1 - 1 / (2 * σ))`. -/
def chapter10Exercise101PenaltyMinimizer (σ : ℝ) : Point :=
  EuclideanSpace.single 0 (1 : ℝ) + EuclideanSpace.single 1 (1 - 1 / (2 * σ))

/-- Feasibility for `chapter10Exercise101Problem` is exactly the equation
`x 1 = (x 0)^2`. -/
theorem chapter10Exercise101_mem_feasibleSet_iff (x : Point) :
    x ∈ chapter10Exercise101Problem.feasibleSet ↔ x 1 = (x 0) ^ (2 : ℕ) := by
  -- The single equality coordinate is the only feasibility condition for this problem.
  rw [StandardPenaltyProblem.mem_feasibleSet_iff]
  simp [chapter10Exercise101Problem, chapter10Exercise101Constraint, sub_eq_zero]

/-- For positive `σ`, the chapter's canonical quadratic penalty function on
`chapter10Exercise101Problem` expands to the Exercise 10.1 source formula
`x ↦ -2 * x 0 + x 1 + σ * (x 1 - (x 0)^2)^2`. -/
theorem chapter10Exercise101_quadratic_apply
    (σ : ℝ) (hσ : 0 < σ) (x : Point) :
    PenaltyFunction.quadratic chapter10Exercise101Problem σ hσ x =
      chapter10Exercise101Objective x +
        σ * (chapter10Exercise101Constraint x) ^ (2 : ℕ) :=
  by
  -- The violation vector has a single equality coordinate, namely the source constraint value.
  rw [PenaltyFunction.quadratic_apply]
  have hViolation :
      c⁽-⁾[chapter10Exercise101Problem] x =
        EuclideanSpace.single 0 (chapter10Exercise101Constraint x) := by
    ext i
    fin_cases i
    simp [StandardPenaltyProblem.constraintViolation, chapter10Exercise101Problem,
      chapter10Exercise101Constraint]
  -- Once the violation vector is normalized to a single coordinate, the norm square is scalar.
  rw [hViolation, PiLp.norm_single]
  simp [chapter10Exercise101Problem, chapter10Exercise101Objective, Real.norm_eq_abs]

/-- Helper for Chapter10 Exercise 10.1: the quadratic penalty objective is a constant plus the
two nonnegative squares controlling the horizontal and constraint directions. -/
lemma chapter10Exercise101_quadraticPenalty_eq_completedSquare
    (σ : ℝ) (hσ : 0 < σ) (x : Point) :
    PenaltyFunction.quadratic chapter10Exercise101Problem σ hσ x =
      (x 0 - 1) ^ (2 : ℕ) +
        σ * (chapter10Exercise101Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) -
        1 - 1 / (4 * σ) := by
  -- Rewrite to the source scalar formula, then complete the square in `x 0` and the
  -- constraint residual.
  rw [chapter10Exercise101_quadratic_apply]
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  unfold chapter10Exercise101Objective chapter10Exercise101Constraint
  field_simp [hσ0]
  ring

/-- Helper for Chapter10 Exercise 10.1: on the feasible parabola `x 1 = (x 0)^2`, the objective
reduces to the one-variable square `(x 0 - 1)^2 - 1`. -/
lemma chapter10Exercise101_objective_eq_completedSquare_of_feasible
    {x : Point} (hx : x ∈ chapter10Exercise101Problem.feasibleSet) :
    chapter10Exercise101Problem.objective x = (x 0 - 1) ^ (2 : ℕ) - 1 := by
  -- Feasibility replaces `x 1` by `(x 0)^2`, leaving a single completed square.
  rw [chapter10Exercise101_mem_feasibleSet_iff] at hx
  simp [chapter10Exercise101Problem, chapter10Exercise101Objective, hx]
  ring

/-- Chapter10 Exercise 10.1: for every positive penalty parameter `σ`, the Courant quadratic
penalty function for the problem with objective `x ↦ -2 * x 0 + x 1` and equality constraint
`x 1 - (x 0)^2 = 0` is minimized on `Set.univ` at
`chapter10Exercise101PenaltyMinimizer σ = (1, 1 - 1 / (2 * σ))`. -/
theorem chapter10Exercise101_quadraticPenalty_isMinOn
    (σ : ℝ) (hσ : 0 < σ) :
    IsMinOn
      (PenaltyFunction.quadratic chapter10Exercise101Problem σ hσ)
      Set.univ
      (chapter10Exercise101PenaltyMinimizer σ) := by
  -- On `Set.univ`, minimization is the pointwise lower-bound inequality.
  rw [isMinOn_univ_iff]
  intro x
  calc
    PenaltyFunction.quadratic chapter10Exercise101Problem σ hσ
        (chapter10Exercise101PenaltyMinimizer σ)
        = -1 - 1 / (4 * σ) := by
          -- The explicit candidate kills both squares in the completed-square formula.
          rw [chapter10Exercise101_quadraticPenalty_eq_completedSquare]
          simp [chapter10Exercise101PenaltyMinimizer, chapter10Exercise101Constraint]
    _ ≤ (x 0 - 1) ^ (2 : ℕ) +
          σ * (chapter10Exercise101Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) -
            1 - 1 / (4 * σ) := by
          -- The remaining terms are nonnegative squares with a nonnegative coefficient `σ`.
          have hFirst : 0 ≤ (x 0 - 1) ^ (2 : ℕ) := sq_nonneg (x 0 - 1)
          have hSecond :
              0 ≤ σ * (chapter10Exercise101Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) :=
            mul_nonneg hσ.le (sq_nonneg _)
          nlinarith
    _ = PenaltyFunction.quadratic chapter10Exercise101Problem σ hσ x := by
          rw [chapter10Exercise101_quadraticPenalty_eq_completedSquare]

/-- The original constrained problem in Exercise 10.1 is minimized at `(1, 1)`. -/
theorem chapter10Exercise101_isMinOn :
    IsMinOn
      chapter10Exercise101Problem.objective
      chapter10Exercise101Problem.feasibleSet
      chapter10Exercise101Optimizer := by
  -- On the feasible parabola, the objective is the one-variable square `(x 0 - 1)^2 - 1`.
  rw [isMinOn_iff]
  intro x hx
  calc
    chapter10Exercise101Problem.objective chapter10Exercise101Optimizer = -1 := by
      norm_num [chapter10Exercise101Problem, chapter10Exercise101Objective,
        chapter10Exercise101Optimizer]
    _ ≤ (x 0 - 1) ^ (2 : ℕ) - 1 := by
      have hsquare : 0 ≤ (x 0 - 1) ^ (2 : ℕ) := sq_nonneg (x 0 - 1)
      nlinarith
    _ = chapter10Exercise101Problem.objective x := by
      symm
      exact chapter10Exercise101_objective_eq_completedSquare_of_feasible hx

/-- The optimal value of the constrained problem in Exercise 10.1 is `-1`. -/
theorem chapter10Exercise101_optimalValue :
    chapter10Exercise101Problem.objective chapter10Exercise101Optimizer = -1 := by
  -- Evaluate the explicit optimizer in the concrete linear objective.
  norm_num [chapter10Exercise101Problem, chapter10Exercise101Objective,
    chapter10Exercise101Optimizer]

/-- Helper for Chapter10 Exercise 10.1: the penalty minimizer is the constrained optimizer minus
the vertical shift `(1 / (2 * σ)) e₁`. -/
lemma chapter10Exercise101_penaltyMinimizer_eq_optimizer_sub_verticalShift (σ : ℝ) :
    chapter10Exercise101PenaltyMinimizer σ =
      chapter10Exercise101Optimizer - (1 / (2 * σ)) • EuclideanSpace.single 1 (1 : ℝ) := by
  -- Compare the two explicit points coordinatewise; only the second coordinate moves.
  ext i
  fin_cases i <;>
    simp [chapter10Exercise101PenaltyMinimizer, chapter10Exercise101Optimizer, sub_eq_add_neg]

/-- The Courant-penalty minimizers converge to the constrained optimizer `(1, 1)` as
`σ → +∞`. -/
theorem chapter10Exercise101_penaltyMinimizer_tendsto :
    Tendsto chapter10Exercise101PenaltyMinimizer atTop
      (nhds chapter10Exercise101Optimizer) := by
  -- Route correction: rewrite the explicit minimizer as a fixed point minus a scalar vertical
  -- shift, then send that scalar to `0`.
  let e1 : Point := EuclideanSpace.single 1 (1 : ℝ)
  have hInv :
      Tendsto (fun σ : ℝ ↦ 1 / (2 * σ)) atTop (nhds 0) := by
    -- Factor `1 / (2 * σ)` as a constant multiple of `σ⁻¹`.
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      (tendsto_inv_atTop_zero.const_mul ((1 : ℝ) / 2))
  have hShift :
      Tendsto
        (fun σ : ℝ ↦ (1 / (2 * σ)) • e1)
        atTop
        (nhds ((0 : ℝ) • e1)) :=
    hInv.smul_const e1
  have hAffine :
      Tendsto
        (fun σ : ℝ ↦
          chapter10Exercise101Optimizer -
            (1 / (2 * σ)) • e1)
        atTop
        (nhds
          (chapter10Exercise101Optimizer -
            (0 : ℝ) • e1)) :=
    tendsto_const_nhds.sub hShift
  have hPenaltyEq :
      chapter10Exercise101PenaltyMinimizer =
        fun σ : ℝ ↦ chapter10Exercise101Optimizer - (1 / (2 * σ)) • e1 := by
    funext σ
    simp [chapter10Exercise101_penaltyMinimizer_eq_optimizer_sub_verticalShift, e1]
  rw [hPenaltyEq]
  simpa [e1] using hAffine

#print axioms chapter10Exercise101Problem
#print axioms chapter10Exercise101Optimizer
#print axioms chapter10Exercise101PenaltyMinimizer

end
