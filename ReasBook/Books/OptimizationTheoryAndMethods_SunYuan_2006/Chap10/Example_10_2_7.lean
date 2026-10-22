/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap10.Algorithm_10_2_3

noncomputable section

section Chapter10Example1027

local notation "Point" => EuclideanSpace ℝ (Fin 2)

-- Primary domain: Chapter 10 penalty methods for constrained minimization in `ℝ²`.
-- Source-facing layer: the concrete objective, equality constraint, and closed-form solution data
-- of Example 10.2.7 together with the Section 10.2 stage objective `P_σ`.
-- Core/canonical layer inspected in the chapter: `StandardPenaltyProblem` for the constrained
-- problem, `StandardPenaltyProblem.simplePenaltyObjective` for the Section 10.2 owner,
-- `PenaltyFunction.simple` for the canonical penalty owner beneath that source view, and
-- `SimplePenaltyFunctionMethod` for Algorithm 10.2.3. The older
-- `PenaltyFunction.quadratic` specialization is therefore kept only as a bridge view in this
-- quadratic example.
-- Primitive data kept local: the concrete objective, constraint, constrained solution, penalty
-- shift, and closed-form stage minimizer. Derived API: the feasible-set theorems, the source
-- stage objective `P_σ`, and the method-level iterate statement.

/-- The objective in Example 10.2.7 is `x ↦ x 0 + x 1`. -/
def example1027Objective (x : Point) : ℝ :=
  x 0 + x 1

/-- The equality constraint in Example 10.2.7 is `x 1 - (x 0)^2 = 0`. -/
def example1027Constraint (x : Point) : ℝ :=
  x 1 - (x 0) ^ (2 : ℕ)

/-- Example 10.2.7 as a `StandardPenaltyProblem` with one equality constraint and no
inequalities. -/
def example1027Problem : StandardPenaltyProblem 2 1 where
  eqCount := 1
  eqCount_le := le_rfl
  objective := example1027Objective
  constraint := fun _ ↦ example1027Constraint

/-- The constrained solution `x*` in Example 10.2.7 is `![-1 / 2, 1 / 4]`. -/
def example1027Solution : Point :=
  EuclideanSpace.single 0 (-((1 : ℝ) / 2)) +
    EuclideanSpace.single 1 ((1 : ℝ) / 4)

/-- The penalty-shift direction in Example 10.2.7 is `![0, 1 / 2]`. -/
def example1027PenaltyShift : Point :=
  EuclideanSpace.single 1 ((1 : ℝ) / 2)

/-- The explicit penalty-subproblem solution in Example 10.2.7 is
`x(σ) = ![-1 / 2, 1 / 4 - 1 / (2 * σ)]`, written as `(1 / 2) / σ` in the second coordinate. -/
def example1027PenaltyPoint (σ : ℝ) : Point :=
  EuclideanSpace.single 0 (-((1 : ℝ) / 2)) +
    EuclideanSpace.single 1 ((1 : ℝ) / 4 - ((1 : ℝ) / 2) / σ)

local notation "P_" σ => example1027Problem.simplePenaltyObjective σ (2 : ℝ)

/-- Feasibility in `example1027Problem.feasibleSet` is exactly the parabola equation
`x 1 = (x 0)^2`. -/
theorem example1027_mem_feasibleSet_iff (x : Point) :
    x ∈ example1027Problem.feasibleSet ↔ x 1 = (x 0) ^ (2 : ℕ) := by
  rw [StandardPenaltyProblem.mem_feasibleSet_iff]
  simpa [example1027Problem, example1027Constraint] using
    (sub_eq_zero : x 1 - (x 0) ^ (2 : ℕ) = 0 ↔ x 1 = (x 0) ^ (2 : ℕ))

/-- In Example 10.2.7, the Section 10.2 stage objective `P_σ` is exactly the Chapter 10.1
quadratic specialization. -/
theorem example1027PenaltyObjective_eq_quadratic
    (σ : ℝ) (hσ : 0 < σ) :
    (P_ σ : Point → ℝ) = PenaltyFunction.quadratic example1027Problem σ hσ := by
  -- Both owners evaluate to the same objective plus the same squared violation norm.
  ext x
  rw [StandardPenaltyProblem.simplePenaltyObjective_apply, PenaltyFunction.quadratic_apply]
  simp

/-- Helper for Chapter10 Example 10.2.7: the quadratic penalty objective is a constant plus the
two nonnegative squares controlling the horizontal coordinate and the constraint violation. -/
lemma example1027_quadraticPenalty_eq_completedSquare
    (σ : ℝ) (hσ : 0 < σ) (x : Point) :
    PenaltyFunction.quadratic example1027Problem σ hσ x =
      (x 0 + 1 / 2) ^ (2 : ℕ) +
        σ * (example1027Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) -
        1 / 4 - 1 / (4 * σ) := by
  -- Normalize the one-coordinate violation vector to the single source constraint value.
  rw [PenaltyFunction.quadratic_apply]
  have hViolation :
      c⁽-⁾[example1027Problem] x =
        EuclideanSpace.single 0 (example1027Constraint x) := by
    ext i
    fin_cases i
    simp [StandardPenaltyProblem.constraintViolation, example1027Problem, example1027Constraint]
  -- Once the norm square is scalar, the remaining identity is a completed-square calculation.
  rw [hViolation, PiLp.norm_single]
  simp [example1027Problem, example1027Objective, example1027Constraint, Real.norm_eq_abs]
  field_simp [hσ.ne']
  ring

/-- Chapter10 Example 10.2.7 (1): for every positive penalty factor `σ`, the Section 10.2 stage
objective `P_σ` with exponent `2` is minimized on `ℝ²` at `example1027PenaltyPoint σ`. -/
theorem example1027PenaltyPoint_isMinOn
    (σ : ℝ) (hσ : 0 < σ) :
    IsMinOn
      (P_ σ)
      Set.univ
      (example1027PenaltyPoint σ) := by
  -- Read minimization on `Set.univ` as a pointwise lower bound.
  rw [isMinOn_univ_iff]
  intro x
  rw [example1027PenaltyObjective_eq_quadratic σ hσ]
  calc
    PenaltyFunction.quadratic example1027Problem σ hσ (example1027PenaltyPoint σ) =
        -1 / 4 - 1 / (4 * σ) := by
      rw [example1027_quadraticPenalty_eq_completedSquare σ hσ]
      -- The explicit penalty point zeros both square terms in the completed-square form.
      have hFirst : example1027PenaltyPoint σ 0 + 1 / 2 = 0 := by
        simp [example1027PenaltyPoint]
      have hConstraint :
          example1027Constraint (example1027PenaltyPoint σ) = -1 / (2 * σ) := by
        -- Evaluating the explicit point in the constraint leaves only the vertical shift term.
        simp [example1027Constraint, example1027PenaltyPoint, div_eq_mul_inv]
        ring_nf
      have hSecond :
          example1027Constraint (example1027PenaltyPoint σ) + 1 / (2 * σ) = 0 := by
        rw [hConstraint]
        ring
      rw [hFirst, hSecond]
      ring
    _ ≤ (x 0 + 1 / 2) ^ (2 : ℕ) +
          σ * (example1027Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) -
          1 / 4 - 1 / (4 * σ) := by
      -- Both square terms are nonnegative, and the penalty coefficient is positive.
      have hSquare₁ : 0 ≤ (x 0 + 1 / 2) ^ (2 : ℕ) := sq_nonneg (x 0 + 1 / 2)
      have hSquare₂ : 0 ≤ σ * (example1027Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) := by
        have hTerm : 0 ≤ (example1027Constraint x + 1 / (2 * σ)) ^ (2 : ℕ) := by
          exact sq_nonneg (example1027Constraint x + 1 / (2 * σ))
        nlinarith
      nlinarith
    _ = PenaltyFunction.quadratic example1027Problem σ hσ x := by
      rw [example1027_quadraticPenalty_eq_completedSquare σ hσ]

/-- Chapter10 Example 10.2.7 (2): for every positive penalty factor `σ`,
`example1027PenaltyPoint σ = example1027Solution - (1 / σ) • example1027PenaltyShift`. -/
theorem example1027PenaltyPoint_eq_solution_sub_shift
    (σ : ℝ) :
    example1027PenaltyPoint σ =
      example1027Solution - (1 / σ) • example1027PenaltyShift := by
  -- Compare the two explicit points coordinatewise; only the second coordinate shifts.
  ext i
  fin_cases i
  · simp [example1027PenaltyPoint, example1027Solution, example1027PenaltyShift, sub_eq_add_neg]
  · simp [example1027PenaltyPoint, example1027Solution, example1027PenaltyShift, sub_eq_add_neg,
      div_eq_mul_inv, mul_comm]

/-- Helper for Chapter10 Example 10.2.7: on the feasible parabola, the objective reduces to the
one-variable square `(x 0 + 1 / 2)^2 - 1 / 4`. -/
lemma example1027_objective_eq_completedSquare_of_feasible
    {x : Point} (hx : x ∈ example1027Problem.feasibleSet) :
    example1027Problem.objective x = (x 0 + 1 / 2) ^ (2 : ℕ) - 1 / 4 := by
  -- Feasibility replaces `x 1` by `(x 0)^2`, leaving a single completed square.
  rw [example1027_mem_feasibleSet_iff] at hx
  change x 0 + x 1 = (x 0 + 1 / 2) ^ (2 : ℕ) - 1 / 4
  rw [hx]
  ring

/-- Chapter10 Example 10.2.7 (3): `example1027Solution` is a minimizer of
`example1027Problem.objective` on the feasible set `example1027Problem.feasibleSet`. -/
theorem example1027Solution_isMinOnFeasibleSet :
    IsMinOn example1027Problem.objective example1027Problem.feasibleSet example1027Solution := by
  -- Read feasible minimization as a pointwise lower bound along the parabola.
  rw [isMinOn_iff]
  intro x hx
  calc
    example1027Problem.objective example1027Solution = -1 / 4 := by
      -- Evaluate the explicit constrained solution in the concrete linear objective.
      norm_num [example1027Problem, example1027Objective, example1027Solution]
    _ ≤ (x 0 + 1 / 2) ^ (2 : ℕ) - 1 / 4 := by
      have hSquare : 0 ≤ (x 0 + 1 / 2) ^ (2 : ℕ) := sq_nonneg (x 0 + 1 / 2)
      nlinarith
    _ = example1027Problem.objective x := by
      symm
      exact example1027_objective_eq_completedSquare_of_feasible hx

/-- The constrained solution `example1027Solution = (-1 / 2, 1 / 4)` is feasible for Example
10.2.7. -/
theorem example1027Solution_mem_feasibleSet :
    example1027Solution ∈ example1027Problem.feasibleSet := by
  rw [example1027_mem_feasibleSet_iff]
  norm_num [example1027Solution]

/-- Helper for Chapter10 Example 10.2.7: every feasible point with the same objective value as
`example1027Solution` must equal that explicit solution. -/
lemma example1027_eq_solution_of_mem_feasibleSet_of_objective_eq
    {x : Point} (hx : x ∈ example1027Problem.feasibleSet)
    (hObj :
      example1027Problem.objective x =
        example1027Problem.objective example1027Solution) :
    x = example1027Solution := by
  -- Compare both feasible objectives through the completed-square normal form.
  have hxSquare :
      example1027Problem.objective x = (x 0 + 1 / 2) ^ (2 : ℕ) - 1 / 4 :=
    example1027_objective_eq_completedSquare_of_feasible hx
  have hSolutionValue :
      example1027Problem.objective example1027Solution = -1 / 4 := by
    -- Evaluate the explicit solution once so the equality case reduces to a vanishing square.
    norm_num [example1027Problem, example1027Objective, example1027Solution]
  have hSquareZero : (x 0 + 1 / 2) ^ (2 : ℕ) = 0 := by
    rw [hxSquare, hSolutionValue] at hObj
    nlinarith
  have hx0 : x 0 = -1 / 2 := by
    have hZero : x 0 + 1 / 2 = 0 := sq_eq_zero_iff.mp hSquareZero
    linarith
  have hx1 : x 1 = 1 / 4 := by
    -- Feasibility pins the second coordinate to the square of the first coordinate.
    have hFeasible := (example1027_mem_feasibleSet_iff x).1 hx
    nlinarith [hx0, hFeasible]
  -- Matching the two coordinates identifies the feasible point with the closed-form solution.
  ext i
  fin_cases i
  · calc
      x 0 = -1 / 2 := hx0
      _ = example1027Solution 0 := by
        norm_num [example1027Solution]
  · calc
      x 1 = (1 : ℝ) / 4 := hx1
      _ = example1027Solution 1 := by
        norm_num [example1027Solution]

/-- Chapter10 Example 10.2.7 (4): every feasible minimizer of the constrained problem agrees with
`example1027Solution`, so the constrained solution is unique. -/
theorem example1027_eq_solution_of_isMinOnFeasibleSet
    {x : Point} (hx : x ∈ example1027Problem.feasibleSet)
    (hmin : IsMinOn example1027Problem.objective example1027Problem.feasibleSet x) :
    x = example1027Solution := by
  -- Compare the unknown feasible minimizer with the explicit solution in both directions.
  have hMinX := isMinOn_iff.mp hmin
  have hMinSolution := isMinOn_iff.mp example1027Solution_isMinOnFeasibleSet
  have hxLe :
      example1027Problem.objective x ≤
        example1027Problem.objective example1027Solution :=
    hMinX example1027Solution example1027Solution_mem_feasibleSet
  have hSolutionLe :
      example1027Problem.objective example1027Solution ≤
        example1027Problem.objective x :=
    hMinSolution x hx
  exact
    example1027_eq_solution_of_mem_feasibleSet_of_objective_eq hx
      (le_antisymm hxLe hSolutionLe)

/-- Chapter10 Example 10.2.7 (5): if a simple penalty method for this example records
`x_(k+1) = example1027PenaltyPoint (σ_k)`, then
`x_(k+1) - example1027Solution = -(1 / σ_k) • example1027PenaltyShift`. -/
theorem example1027_iterate_sub_solution
    (method : SimplePenaltyFunctionMethod 2 1) {k : ℕ}
    (hStep :
      method.iterate (k + 1) =
        example1027PenaltyPoint (method.penaltyParameter k)) :
    method.iterate (k + 1) - example1027Solution =
      (- (1 / method.penaltyParameter k)) • example1027PenaltyShift := by
  -- Substitute the recorded penalty-stage point and simplify the explicit shift coordinatewise.
  rw [hStep, example1027PenaltyPoint_eq_solution_sub_shift]
  ext i
  fin_cases i <;>
    simp [example1027Solution, example1027PenaltyShift, sub_eq_add_neg]

end Chapter10Example1027
