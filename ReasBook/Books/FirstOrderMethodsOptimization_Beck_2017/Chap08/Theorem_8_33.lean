/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_31

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
variable (h_bound : SubgradientNormBoundOn f C)
variable (g : ℕ → C → E) (t : ℕ → ℝ) (x0 : C)

local notation "x[" k "]" =>
  projected_subgradient_method C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0 k
local notation "x̄" =>
  projected_subgradient_method_iterate C h_problem.feasible_nonempty h_problem.feasible_closed
    h_problem.feasible_convex g t x0
local notation "x̄[" k "]" => x̄ k

/- Theorem 8.33 is `source-facing`: it is the explicit `ε`-complexity corollary of the strongly
convex projected-subgradient rate from Theorem 8.31. The relevant owner abstractions are the
projected iterate sequence `projected_subgradient_method`, the running-best objective value
`best_achieved_function_value`, the standing problem package `IsConstrainedConvexProblem`, the
norm-bound package `SubgradientNormBoundOn`, the strong convexity predicate
`StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal)`, and the chapter owner
`projected_subgradient_strongly_convex_average_iterate` for the averaged iterate `x^(k)`. The
explicit coefficient formula for `x^(k)` remains available from Theorem 8.31 via
`projected_subgradient_strongly_convex_average_iterate_eq_sum`, so this file can stay a thin
corollary layer rather than duplicating that owner. -/

-- Proof sketch: rearrange the iteration threshold
-- `2 L_f^2 / (σ ε) - 1 ≤ k` into
-- `2 L_f^2 / (σ ε) ≤ k + 1`. Since `σ > 0` and `ε > 0`, multiply by the positive denominator
-- `σ ε` and divide by `σ (k + 1)` to obtain the desired bound.
/-- If `σ > 0`, the strongly-convex iteration threshold
`2 L_f^2 / (σ ε) - 1 ≤ k` implies the corresponding rate estimate
`2 L_f^2 / (σ (k + 1)) ≤ ε`. -/
theorem strongly_convex_stepsize_rate_bound_le_epsilon_of_iteration_count
    (Lf σ ε : ℝ) (k : ℕ) (hσ : 0 < σ) (hε : 0 < ε)
    (hk : 2 * Lf ^ (2 : ℕ) / (σ * ε) - 1 ≤ (k : ℝ)) :
    2 * Lf ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) ≤ ε := by
  have hk' : 2 * Lf ^ (2 : ℕ) / (σ * ε) ≤ (k : ℝ) + 1 := by
    nlinarith
  have hσε : 0 < σ * ε := mul_pos hσ hε
  have hnum : 2 * Lf ^ (2 : ℕ) ≤ ((k : ℝ) + 1) * (σ * ε) := by
    rw [div_le_iff₀ hσε] at hk'
    exact hk'
  have hdenom : 0 < σ * (k + 1 : ℝ) := by positivity
  rw [div_le_iff₀ hdenom]
  nlinarith [hnum]

-- Proof sketch: apply Theorem 8.31 (1) to obtain
-- `f_best^k - fOpt ≤ 2 L_f^2 / (σ (k + 1))`, then use the index lower bound
-- `2 L_f^2 / (σ ε) - 1 ≤ k` to rearrange this rate estimate into
-- `2 L_f^2 / (σ (k + 1)) ≤ ε`.
/-- Theorem 8.33 (1): under the setting and assumptions of Theorem 8.31, every index `k` with
`2 L_f^2 / (σ ε) - 1 ≤ k` guarantees that the best objective value attained among the first
`k + 1` projected-subgradient iterates differs from the optimum by at most `ε`, provided
`σ > 0`. -/
theorem projected_subgradient_best_value_gap_le_epsilon_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ) (ε : ℝ) (k : ℕ) (hε : 0 < ε)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (hk : 2 * h_bound.L_f ^ (2 : ℕ) / (σ * ε) - 1 ≤ (k : ℝ)) :
    best_achieved_function_value (fun x ↦ (f x).toReal) x̄ k - fOpt ≤ ε :=
  by
    rcases h_problem.optimal_set_nonempty with ⟨xStar, hxStar⟩
    have h_rate :
        best_achieved_function_value (fun x ↦ (f x).toReal) x̄ k - fOpt ≤
          2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) :=
      projected_subgradient_best_value_gap_le_of_strongly_convex_stepsize
        h_problem h_bound g t x0 h_strong hσ h_subgrad h_stepsize hxStar k
    have h_eps_rate :
        2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) ≤ ε :=
      strongly_convex_stepsize_rate_bound_le_epsilon_of_iteration_count
        h_bound.L_f σ ε k hσ hε hk
    exact h_rate.trans h_eps_rate

-- Proof sketch: apply Theorem 8.31 (3) to the weighted average iterate `x^(k)` to get
-- `f(x^(k)) - fOpt ≤ 2 L_f^2 / (σ (k + 1))`, and then use the same rearrangement of the lower
-- bound `2 L_f^2 / (σ ε) - 1 ≤ k` to conclude `f(x^(k)) - fOpt ≤ ε`.
/-- Theorem 8.33 (2): under the setting and assumptions of Theorem 8.31, the weighted average
iterate `x^(k)` also satisfies the `ε`-accuracy guarantee
`f(x^(k)) - fOpt ≤ ε` whenever `2 L_f^2 / (σ ε) - 1 ≤ k`, provided `σ > 0`. -/
theorem projected_subgradient_average_value_gap_le_epsilon_of_strongly_convex_stepsize
    (h_strong : StrongConvexOn (effective_domain f) σ (fun x ↦ (f x).toReal))
    (hσ : 0 < σ) (ε : ℝ) (k : ℕ) (hε : 0 < ε)
    (h_subgrad :
      ∀ n,
        toDualMap ℝ E (g n (x[n])) ∈ strongDualSubdifferential f x̄[n])
    (h_stepsize : ∀ n, t n = 2 / (σ * (n + 1 : ℝ)))
    (hk : 2 * h_bound.L_f ^ (2 : ℕ) / (σ * ε) - 1 ≤ (k : ℝ)) :
    (f (projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k)).toReal - fOpt ≤
      ε := by
  have h_rate :
      (f (projected_subgradient_strongly_convex_average_iterate h_problem g t x0 k)).toReal - fOpt ≤
        2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) :=
    projected_subgradient_average_value_gap_le_of_strongly_convex_stepsize
      h_problem h_bound g t x0 h_strong hσ h_subgrad h_stepsize k
  have h_eps_rate :
      2 * h_bound.L_f ^ (2 : ℕ) / (σ * (k + 1 : ℝ)) ≤ ε :=
    strongly_convex_stepsize_rate_bound_le_epsilon_of_iteration_count
      h_bound.L_f σ ε k hσ hε hk
  exact h_rate.trans h_eps_rate

end
