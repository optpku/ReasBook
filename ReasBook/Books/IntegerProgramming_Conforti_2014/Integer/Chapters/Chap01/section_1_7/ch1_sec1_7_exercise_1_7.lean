import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-- Feasible nonnegative integer points for the integer program from Exercise 1.7. -/
def exercise_1_7_feasible (x1 x2 : Nat) : Prop :=
  x2 ≤ x1 ∧ 6 * x1 + 2 * x2 ≤ 21

/-- Objective function for the integer program from Exercise 1.7. -/
def exercise_1_7_objective (x1 x2 : Nat) : Nat :=
  2 * x1 + x2

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_7.lean. Exercise 1.7 (1): every feasible nonnegative integer point has objective value at most `7`. -/
theorem exercise_1_7_objective_le_seven {x1 x2 : Nat}
    (hfeas : exercise_1_7_feasible x1 x2) :
    exercise_1_7_objective x1 x2 ≤ 7 := by
  -- Expose the two linear constraints packaged by feasibility.
  rcases hfeas with ⟨h₁, h₂⟩
  -- Normalize the objective and discharge the resulting Presburger goal.
  simp only [exercise_1_7_objective] at h₁ h₂ ⊢
  omega

/-- Exercise 1.7 (2): the point `(3, 1)` is feasible and attains objective value `7`. -/
theorem exercise_1_7_optimal_point :
    exercise_1_7_feasible 3 1 ∧ exercise_1_7_objective 3 1 = 7 := by
  -- Evaluate the constraints and objective at the proposed optimal point.
  norm_num [exercise_1_7_feasible, exercise_1_7_objective]
