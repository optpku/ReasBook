/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {m : ℕ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)

/- Definition 8.20 is `source-facing`: the textbook introduces the dual optimization problem for
the Chapter 8 inequality-constrained primal problem. Domain sampling against mathlib shows that
the canonical owner for the optimization viewpoint is `IsMaxOn`; the only genuinely new local
object is the nonnegative multiplier region `ℝ_+^m`, written here as the explicit coordinatewise
orthant in `EuclideanSpace ℝ (Fin m)`. As in Definition 8.17, the source-facing API is therefore
a feasible-set owner together with a companion `IsMaxOn` characterization, rather than a
surrogate package or an existential wrapper for optimal multipliers. -/

/-- Definition 8.20: the feasible multiplier region of the dual problem is the nonnegative
orthant `ℝ_+^m`. The dual problem maximizes the dual function `q` over this set. -/
def dual_problem_feasible_set (m : ℕ) : Set (EuclideanSpace ℝ (Fin m)) :=
  {lam | ∀ i : Fin m, 0 ≤ lam i}

-- Proof sketch: unfold `dual_problem_feasible_set`; membership is definitionally the
-- coordinatewise nonnegativity condition `∀ i, 0 ≤ λ i`.
/-- Helper for Definition 8.20: membership in `dual_problem_feasible_set m` means that every
coordinate of the multiplier vector is nonnegative. -/
@[simp] theorem mem_dual_problem_feasible_set {lam : Λ} :
    lam ∈ dual_problem_feasible_set m ↔ ∀ i : Fin m, 0 ≤ lam i := by
  -- Unfolding the set-builder exposes exactly the coordinatewise nonnegativity condition.
  rfl

section

variable {α : Type u} [Preorder α]

-- Proof sketch: rewrite `IsMaxOn q (dual_problem_feasible_set m) lam` using the canonical
-- characterization `isMaxOn_iff`, then keep the maximizer's feasibility explicit so the result
-- matches the textbook constrained maximization statement over `ℝ_+^m`.
/-- Helper for Definition 8.20: a feasible multiplier `lam` maximizes `q` on
`dual_problem_feasible_set m` exactly when it dominates every feasible comparison multiplier. -/
theorem isMaxOn_dual_problem_feasible_set_iff
    {q : Λ → α} {lam : Λ} :
    lam ∈ dual_problem_feasible_set m ∧
      IsMaxOn q (dual_problem_feasible_set m) lam ↔
      lam ∈ dual_problem_feasible_set m ∧
        ∀ μ, μ ∈ dual_problem_feasible_set m → q μ ≤ q lam := by
  -- Route correction: mathlib's `IsMaxOn` only gives comparison inequalities on feasible points,
  -- so the maximizer's own feasibility must be recorded explicitly on the left-hand side.
  constructor
  · rintro ⟨hlam, hmax⟩
    rw [isMaxOn_iff] at hmax
    refine ⟨hlam, ?_⟩
    -- Every feasible comparison multiplier lies in the same feasible set, so `IsMaxOn` applies.
    intro μ hμ
    exact hmax μ hμ
  · rintro ⟨hlam, hmax⟩
    refine ⟨hlam, ?_⟩
    rw [isMaxOn_iff]
    -- Rewriting the comparison premise to feasible-set membership reduces the goal to `hmax`.
    intro μ hμ
    exact hmax μ hμ

end

end
