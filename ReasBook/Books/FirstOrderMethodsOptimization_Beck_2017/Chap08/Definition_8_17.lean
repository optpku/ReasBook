/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {E : Type u} {m : ℕ}

/- Definition 8.17 is `source-facing`: it fixes the primal inequality-constrained optimization
problem with ambient set constraint `x ∈ X` and coordinatewise inequality constraint `g(x) ≤ 0`.
The canonical owner abstraction for optimality itself is mathlib's `IsMinOn`; the genuinely new
data here is the feasible set obtained by combining `X` with the coordinatewise inequalities. -/

/-- Definition 8.17: the feasible set of the problem `min f(x)` subject to `g(x) ≤ 0` and
`x ∈ X` consists of the points of `X` satisfying every coordinatewise inequality constraint
`g x i ≤ 0`. -/
def inequality_constrained_primal_feasible_set
    (X : Set E) (g : E → Fin m → ℝ) : Set E :=
  {x | x ∈ X ∧ ∀ i : Fin m, g x i ≤ 0}

-- Proof sketch: unfold `inequality_constrained_primal_feasible_set`; membership is exactly the
-- conjunction of `x ∈ X` and the coordinatewise inequalities `g x i ≤ 0`.
/-- Helper for Definition 8.17: membership in
`inequality_constrained_primal_feasible_set X g` means belonging to `X` and satisfying all
inequalities `g x i ≤ 0`. -/
@[simp] theorem mem_inequality_constrained_primal_feasible_set
    {X : Set E} {g : E → Fin m → ℝ} {x : E} :
    x ∈ inequality_constrained_primal_feasible_set X g ↔
      x ∈ X ∧ ∀ i : Fin m, g x i ≤ 0 := by
  -- Unfolding the set-builder exposes exactly the ambient-set and inequality constraints.
  rfl

section

variable {α : Type v} [Preorder α]

-- Proof sketch: `IsMinOn` only records the comparison inequalities on feasible points, so the
-- minimizer's own feasibility must be bundled separately to match the textbook constrained
-- problem statement.
/-- Helper for Definition 8.17: a feasible point `x` minimizes `f` on
`inequality_constrained_primal_feasible_set X g` exactly when `x` satisfies the inequality
constraints and beats every other feasible comparison point. -/
theorem isMinOn_inequality_constrained_primal_feasible_set_iff
    {f : E → α} {X : Set E} {g : E → Fin m → ℝ} {x : E} :
    x ∈ inequality_constrained_primal_feasible_set X g ∧
      IsMinOn f (inequality_constrained_primal_feasible_set X g) x ↔
      x ∈ X ∧
        (∀ i : Fin m, g x i ≤ 0) ∧
        ∀ y, y ∈ X → (∀ i : Fin m, g y i ≤ 0) → f x ≤ f y := by
  -- Route correction: mathlib's `IsMinOn` does not assert `x ∈ s`, so we keep feasibility
  -- explicit on the left-hand side before rewriting into the textbook constrained form.
  constructor
  · rintro ⟨hx, hmin⟩
    rcases (mem_inequality_constrained_primal_feasible_set.mp hx) with ⟨hxX, hxg⟩
    rw [isMinOn_iff] at hmin
    refine ⟨hxX, hxg, ?_⟩
    -- Every feasible comparison point is in the feasible set, so `IsMinOn` gives the inequality.
    intro y hyX hyg
    exact hmin y <| mem_inequality_constrained_primal_feasible_set.mpr ⟨hyX, hyg⟩
  · rintro ⟨hxX, hxg, hmin⟩
    refine ⟨mem_inequality_constrained_primal_feasible_set.mpr ⟨hxX, hxg⟩, ?_⟩
    rw [isMinOn_iff]
    -- Rewriting feasible-set membership for the comparison point reduces the goal to `hmin`.
    intro y hy
    rcases (mem_inequality_constrained_primal_feasible_set.mp hy) with ⟨hyX, hyg⟩
    exact hmin y hyX hyg

end

end
