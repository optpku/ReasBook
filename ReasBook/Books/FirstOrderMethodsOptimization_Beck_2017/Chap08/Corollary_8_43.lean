/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_41
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_20
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_20
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Theorem_8_42

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]
variable {m : ℕ} [NeZero m]
variable {X XStar : Set E} {f : E → ℝ} {g : Fin m → E → ℝ} {fOpt : ℝ}

local notation "Λ" => EuclideanSpace ℝ (Fin m)
local notation "q" => lagrangian_dual_objective X f (dual_constraint_vector g)

/- Corollary 8.43 is `source-facing`: it bounds every optimal dual multiplier for the Chapter 8
dual problem under Assumption 8.41. The natural Chapter 8 owner for dual optimality is the
feasible-maximizer pair `lam ∈ dual_problem_feasible_set m ∧
IsMaxOn q (dual_problem_feasible_set m) lam`, equivalently characterized by
`isMaxOn_dual_problem_feasible_set_iff`; the norm estimate itself is the `μ = fOpt`
specialization of the Chapter 8 superlevel-set bound written using the reusable owner
`strict_feasibility_margin g xBar` rather than an inline finite minimum. -/

-- Proof sketch: use strong duality under `h_problem` to identify the dual optimal value with
-- `fOpt`. Since `lam` is a feasible maximizer of the dual objective on the nonnegative orthant,
-- it belongs to the superlevel set at level `fOpt`. Then apply the Chapter 8 norm bound for dual
-- superlevel sets at the strict feasible point `xBar`.
/-- Corollary 8.43: under Assumption 8.41, every optimal multiplier `λ` of the dual problem
`max {q(λ) : λ ∈ ℝ_+^m}` satisfies the bound
`‖λ‖ ≤ (f(xBar) - fOpt) / min_i {-g_i(xBar)}` for any strict feasible point `xBar ∈ X`. -/
theorem norm_le_div_strict_feasibility_margin_of_dual_optimal_multiplier
    (h_problem : IsDualProjectedSubgradientProblem X XStar f g fOpt)
    {xBar : E} (hxBar : xBar ∈ X) (hgBar : ∀ i : Fin m, g i xBar < 0)
    {lam : Λ}
    (hLam : lam ∈ dual_problem_feasible_set m ∧ IsMaxOn q (dual_problem_feasible_set m) lam) :
    ‖lam‖ ≤ (f xBar - fOpt) / strict_feasibility_margin g xBar := by
  rcases hLam with ⟨hLam_mem, hLam_max⟩
  -- Convert the feasible maximizer into the `IsLUB` witness required by strong duality.
  have hdual_value : IsLUB (q '' dual_problem_feasible_set m) (q lam) := by
    simpa using hLam_max.isLUB hLam_mem
  -- Strong duality identifies the dual value at an optimal multiplier with `fOpt`.
  have hq_eq : q lam = (fOpt : EReal) := by
    simpa using dual_projected_subgradient_problem_strong_duality h_problem hdual_value
  -- Repackage feasibility and the optimal-value identity as superlevel-set membership.
  have hsuperlevel : lam ∈ dual_objective_superlevel_set X f g fOpt := by
    rw [mem_dual_objective_superlevel_set]
    refine ⟨mem_dual_problem_feasible_set.mp hLam_mem, ?_⟩
    simp [hq_eq]
  -- The corollary is exactly Theorem 8.42 specialized to the optimal level `μ = fOpt`.
  exact
    norm_le_div_strict_feasibility_margin_of_mem_dual_objective_superlevel_set
      X f g fOpt xBar lam hxBar hgBar hsuperlevel

end
