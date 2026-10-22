/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

open WithLp (toLp)

section

variable {E : Type u} {m : ℕ}

/- Definition 8.23 is `source-facing`: the textbook introduces an approximate constrained-solution
notion with two components, objective-value suboptimality and Euclidean norm of the positive-part
constraint residual. Domain sampling against the surrounding optimization API shows that the
canonical owners are:
1. the point predicate `x ∈ X ∧ f x - fOpt ≤ ε` for the objective-value part;
2. the Euclidean bridge `toLp 2 ((g x)⁺)` for the inequality-residual vector.
The public API therefore keeps the source-facing point predicate directly, with a small reusable
helper for the objective-gap portion and the canonical Euclidean norm on the positive-part
residual. -/

/-- A point of `X` is `ε`-optimal for the objective `f` if its objective gap above `fOpt` is at
most `ε`. -/
def is_epsilon_optimal_point
    (f : E → ℝ) (X : Set E) (fOpt ε : ℝ) (x : E) : Prop :=
  x ∈ X ∧ f x - fOpt ≤ ε

-- Proof sketch: unfold `is_epsilon_optimal_point`; this is definitionally the conjunction of
-- membership in `X` and the objective-gap bound `f x - fOpt ≤ ε`.
/-- Unfolding `is_epsilon_optimal_point` recovers membership in `X` together with the objective
gap bound `f x - fOpt ≤ ε`. -/
@[simp] theorem is_epsilon_optimal_point_iff
    {f : E → ℝ} {X : Set E} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_point f X fOpt ε x ↔ x ∈ X ∧ f x - fOpt ≤ ε := by
  -- The objective-side predicate is already defined as this conjunction.
  rfl

/-- The Euclidean norm of the positive part of the inequality-constraint vector `g x`. -/
def positive_constraint_violation
    (g : E → Fin m → ℝ) (x : E) : ℝ :=
  ‖(toLp 2 ((g x)⁺) : EuclideanSpace ℝ (Fin m))‖

-- Proof sketch: unfold `positive_constraint_violation`; it is definitionally the Euclidean norm
-- of the positive-part vector `[(g x)]_+`.
/-- Evaluating `positive_constraint_violation g x` gives the Euclidean norm of the positive part
of the constraint vector `g x`. -/
@[simp] theorem positive_constraint_violation_def
    {g : E → Fin m → ℝ} {x : E} :
    positive_constraint_violation g x =
      ‖(toLp 2 ((g x)⁺) : EuclideanSpace ℝ (Fin m))‖ := by
  -- The residual norm is the definition of `positive_constraint_violation`.
  rfl

/-- Definition 8.23: a vector `x ∈ X` is an `ε`-optimal and feasible solution of
`min f(x)` subject to `g(x) ≤ 0` and `x ∈ X` when it is `ε`-optimal in objective value and the
Euclidean norm of the positive part of the constraint vector `g x` is at most `ε`. -/
def is_epsilon_optimal_and_feasible_solution
    (f : E → ℝ) (X : Set E) (g : E → Fin m → ℝ) (fOpt ε : ℝ) (x : E) : Prop :=
  is_epsilon_optimal_point f X fOpt ε x ∧
    positive_constraint_violation g x ≤ ε

-- Proof sketch: unfold `is_epsilon_optimal_and_feasible_solution`; this is definitionally the
-- conjunction of `ε`-optimality in objective value and the residual bound
-- `positive_constraint_violation g x ≤ ε`.
/-- Unfolding `is_epsilon_optimal_and_feasible_solution` identifies it with the conjunction of
`is_epsilon_optimal_point f X fOpt ε x` and the bound on the positive-part constraint residual. -/
theorem is_epsilon_optimal_and_feasible_solution_def
    {f : E → ℝ} {X : Set E} {g : E → Fin m → ℝ} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_and_feasible_solution f X g fOpt ε x ↔
      is_epsilon_optimal_point f X fOpt ε x ∧
        positive_constraint_violation g x ≤ ε := by
  -- The main predicate is defined as the conjunction of the objective and feasibility pieces.
  rfl

-- Proof sketch: unfold `is_epsilon_optimal_and_feasible_solution`, then rewrite the first factor
-- with `is_epsilon_optimal_point_iff`.
/-- Unfolding `is_epsilon_optimal_and_feasible_solution` recovers the textbook conditions
`x ∈ X`, `f x - fOpt ≤ ε`, and `‖[(g x)]_+‖₂ ≤ ε`. -/
@[simp] theorem is_epsilon_optimal_and_feasible_solution_iff
    {f : E → ℝ} {X : Set E} {g : E → Fin m → ℝ} {fOpt ε : ℝ} {x : E} :
    is_epsilon_optimal_and_feasible_solution f X g fOpt ε x ↔
      x ∈ X ∧
        f x - fOpt ≤ ε ∧
        positive_constraint_violation g x ≤ ε := by
  -- First unfold the conjunction-valued definition to expose the two governing conditions.
  rw [is_epsilon_optimal_and_feasible_solution_def]
  -- Then rewrite the objective-side predicate into textbook form and reassociate conjunctions.
  rw [is_epsilon_optimal_point_iff]
  rw [and_assoc]

end
