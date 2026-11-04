/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_3.ch1_sec1_3_1_definition_1_10.FeasibleRegion
import Mathlib.Order.Bounds.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct

open scoped Matrix

section Definition110

variable {m n : ℕ}

/-- Definition 1.10. The set of objective values attained by feasible points of the standard-form
linear programming problem with data `(A, b, c)`, using the canonical objective `x ↦ c ⬝ᵥ x`. -/
def linear_programming_objective_values
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ) : Set ℝ :=
  (c ⬝ᵥ ·) '' linear_programming_feasible_set A b

/-- `linear_programming_objective_values A b c` is definitionally the image of the feasible region
under the canonical dot-product objective `x ↦ c ⬝ᵥ x`. -/
theorem linear_programming_objective_values_def
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ) :
    linear_programming_objective_values A b c = (c ⬝ᵥ ·) '' linear_programming_feasible_set A b :=
  rfl

/-- Membership in `linear_programming_objective_values A b c` means that the value is attained by
some feasible vector. -/
theorem mem_linear_programming_objective_values_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (r : ℝ) :
    r ∈ linear_programming_objective_values A b c ↔
      ∃ x : Fin n → ℝ,
        x ∈ linear_programming_feasible_set A b ∧ c ⬝ᵥ x = r := by
  rfl

/-- Every feasible point contributes its attained dot-product value to
`linear_programming_objective_values A b c`. -/
theorem objective_value_mem_linear_programming_objective_values
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {x : Fin n → ℝ}
    (hx : x ∈ linear_programming_feasible_set A b) :
    c ⬝ᵥ x ∈ linear_programming_objective_values A b c := by
  exact (mem_linear_programming_objective_values_iff A b c (c ⬝ᵥ x)).2 ⟨x, hx, rfl⟩

/-- Optimality predicate for Definition 1.10: a vector `x` solves the standard-form linear
programming problem with data `(A, b, c)` when it is feasible and its objective value is the
greatest attained value. -/
def is_linear_programming_optimal_solution
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (x : Fin n → ℝ) : Prop :=
  x ∈ linear_programming_feasible_set A b ∧
    IsGreatest (linear_programming_objective_values A b c) (c ⬝ᵥ x)

/-- The optimal-solution predicate unfolds to feasibility together with the `IsGreatest` condition
for the attained objective value `c ⬝ᵥ x`. -/
theorem is_linear_programming_optimal_solution_iff
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (x : Fin n → ℝ) :
    is_linear_programming_optimal_solution A b c x ↔
      x ∈ linear_programming_feasible_set A b ∧
        IsGreatest (linear_programming_objective_values A b c) (c ⬝ᵥ x) :=
  Iff.rfl

/-- An optimal solution is, in particular, feasible. -/
theorem is_linear_programming_optimal_solution.feasible
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {c : Fin n → ℝ}
    {x : Fin n → ℝ}
    (hx : is_linear_programming_optimal_solution A b c x) :
    x ∈ linear_programming_feasible_set A b :=
  hx.1

/-- An optimal solution attains a greatest element of the objective-value set. -/
theorem is_linear_programming_optimal_solution.isGreatest
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {c : Fin n → ℝ}
    {x : Fin n → ℝ}
    (hx : is_linear_programming_optimal_solution A b c x) :
    IsGreatest (linear_programming_objective_values A b c) (c ⬝ᵥ x) :=
  hx.2

/-- The objective value of an optimal solution lies in the attained objective-value set. -/
theorem is_linear_programming_optimal_solution.objective_mem
    {A : Matrix (Fin m) (Fin n) ℝ}
    {b : Fin m → ℝ}
    {c : Fin n → ℝ}
    {x : Fin n → ℝ}
    (hx : is_linear_programming_optimal_solution A b c x) :
    c ⬝ᵥ x ∈ linear_programming_objective_values A b c :=
  hx.2.1

end Definition110
