/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic search tool `lean_leansearch` was not available in this environment; the statement
-- shape below follows the local Chapter 1 integer-programming precedent.

/-- Feasible nonnegative integer points for the pure integer program from Exercise 1.4. -/
def exercise_1_4_feasible (x1 x2 : Nat) : Prop :=
  x2 ≤ x1 ∧ 6 * x1 + 2 * x2 ≤ 21

/-- Objective function for the pure integer program from Exercise 1.4. -/
def exercise_1_4_objective (x1 x2 : Nat) : Nat :=
  2 * x1 + x2

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap01/section_1_7/ch1_sec1_7_exercise_1_4.lean.
Exercise 1.4 (1): every feasible nonnegative integer point has objective value at most `7`. -/
theorem exercise_1_4_objective_le_seven {x1 x2 : Nat}
    (hfeas : exercise_1_4_feasible x1 x2) :
    exercise_1_4_objective x1 x2 ≤ 7 := by
  -- Expose the order and capacity constraints before solving the integer arithmetic bound.
  simp only [exercise_1_4_feasible] at hfeas
  rcases hfeas with ⟨horder, hcapacity⟩
  simp only [exercise_1_4_objective]
  omega

/-- Exercise 1.4 (2): the point `(3, 1)` is feasible for the given pure integer program. -/
theorem exercise_1_4_optimal_point_feasible :
    exercise_1_4_feasible 3 1 := by
  -- Evaluate both feasibility constraints at the proposed integer point.
  norm_num [exercise_1_4_feasible]

/-- Exercise 1.4 (3): the feasible point `(3, 1)` attains objective value `7`. -/
theorem exercise_1_4_optimal_point_objective :
    exercise_1_4_objective 3 1 = 7 := by
  -- Evaluate the objective at the feasible point to certify attainment of the bound.
  norm_num [exercise_1_4_objective]

#print axioms exercise_1_4_objective_le_seven
#print axioms exercise_1_4_optimal_point_feasible
#print axioms exercise_1_4_optimal_point_objective
