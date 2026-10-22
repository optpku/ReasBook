/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_47
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped WithTopConvexAnalysis StronglyConvexProblemClass

/- Proposition 3.42 lies in the chapter's projected subgradient / strongly convex complexity
domain.

Mandatory domain-style sampling before refinement:
* `𝒫_s(x₀, μ, M)` and the owner projections
  `IsInStronglyConvexProblemClass.strongConvexOn_closedBall`,
  `IsInStronglyConvexProblemClass.isMinOn`, and
  `IsInStronglyConvexProblemClass.lipschitzOn_closedBall` in `Theorem_3_47`;
* `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`
  in `Theorem_3_2_6`, the earlier strong-convexity owner theorem for projected subgradient
  descent on a controlling set;
* `StrongConvexOn.norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem` in
  `Proposition_3_41`, the canonical radius bridge from the strongly convex / Lipschitz owner data
  to the parameter-only estimate `‖x₀ - x*‖ ≤ 2 M / μ`.

Best owner abstraction:
* source-facing: the projected-subgradient sampled-value guarantee on the strongly convex class
  `𝒫_s(x₀, μ, M)` with a parameter-only iteration budget depending only on `μ`, `M`, and `ε`;
* core/canonical:
  `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`;
* bridge/view: the radius estimate from Proposition 3.41 that replaces the instance-dependent term
  `‖x₀ - x*‖` in the logarithmic budget by the class parameter ratio `2 M / μ`.

Primitive data:
* the problem-class datum `hf : 𝒫_s(x₀, μ, M) f xStar`;
* the projection map, iterate sequence, and chosen constrained subgradients from the projected
  subgradient owner theorem in `Theorem_3_2_6`;
* the target accuracy `ε` and the iteration budget `N`.

Derived API:
* the owner-level logarithmic-budget guarantee from `Theorem_3_2_6`;
* the parameter-only budget obtained by substituting the Proposition 3.41 radius estimate into
  that owner theorem.

Source/core/bridge triage:
* source-facing: Proposition 3.42's parameter-only budget threshold;
* core/canonical: Theorem 3.2.6's owner theorem on a controlling closed ball;
* bridge/view: Proposition 3.41's radius estimate.

The previous file was centered on a fixed-step hard-instance corollary from `Theorem_3_47`. That
is an auxiliary bridge in the black-box lower-bound direction, not the source-facing statement of
Proposition 3.42. This refinement restores the proposition to the projected-subgradient owner
surface and keeps the hard-instance material out of the public API of this file. -/

section StronglyConvexProjectedSubgradient

variable {x0 xStar : E} {μ M : NNReal} {f : E → ℝ}

local notation "Q" => (Metric.closedBall xStar ‖x0 - xStar‖ : Set E)

open IsInStronglyConvexProblemClass

/-- Proposition 3.42: for projected subgradient descent on a problem in the strongly convex class
`𝒫_s(x₀, μ, M)`, the sampled-prefix owner value
`bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` is at most `f(x*) + ε` once the iteration budget
satisfies the parameter-only lower bound
`N ≥ (M² / (μ ε)) log (2 M² / (μ ε))`. This is exactly the earlier strong-convexity owner theorem
with the
instance-dependent factor `‖x₀ - x*‖` replaced by the class-level estimate `2 M / μ` from
Proposition 3.41. -/
theorem bestFunctionValueUpTo_le_optimalValue_add_eps_of_parameter_log_budget
    (hf : 𝒫_s(x0, μ, M) f xStar)
    {ε : ℝ} (hε : 0 < ε)
    (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    (xSeq g : ℕ → E) (hxSeq_zero : xSeq 0 = x0)
    (hsubgrad : ∀ k : ℕ, g k ∈ (∂[Q] f((xSeq k)) : Set E))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    {N : ℕ}
    (hN :
      ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log (((2 : ℝ) * (M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε)) ≤
        (N : ℝ)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N ≤ f xStar + ε := by
  -- Extract the real-valued parameter positivity recorded by the problem-class data.
  have hμ : 0 < (μ : ℝ) := by
    exact_mod_cast mu_pos hf
  -- The Lipschitz constant is nonzero, so multiplying inequalities by `M` preserves order.
  have hM : 0 < (M : ℝ) := by
    exact_mod_cast lipschitzConst_pos hf
  -- Restrict the global minimizer from the problem class to the controlling closed ball.
  have hxStarQ : IsMinOn f Q xStar :=
    (isMinOn hf).on_subset (by intro y _; simp)
  -- Proposition 3.41 supplies the parameter-only bound on the controlling-ball radius.
  have hdist :
      ‖x0 - xStar‖ ≤ 2 * (M : ℝ) / (μ : ℝ) := by
    simpa using
      (strongConvexOn_closedBall hf).norm_sub_le_two_mul_lipschitzOnWith_div_of_isMinOn_of_mem
        (mu_pos hf) (lipschitzOn_closedBall hf) (by simp) hxStarQ
        (by simp [dist_eq_norm_sub])
  -- Compare the owner theorem's logarithmic argument to the parameter-only argument.
  have hbudget :
      ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log ((M : ℝ) * ‖x0 - xStar‖ / ε) ≤
        (N : ℝ) := by
    have harg_le :
        (M : ℝ) * ‖x0 - xStar‖ / ε ≤
          ((2 : ℝ) * (M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) := by
      have hmul :
          (M : ℝ) * ‖x0 - xStar‖ ≤ (M : ℝ) * (2 * (M : ℝ) / (μ : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hdist hM.le
      have hdiv :
          ((M : ℝ) * ‖x0 - xStar‖) / ε ≤
            ((M : ℝ) * (2 * (M : ℝ) / (μ : ℝ))) / ε :=
        div_le_div_of_nonneg_right hmul hε.le
      simpa [pow_two, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
    have hcoeff_nonneg :
        0 ≤ ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) := by
      positivity
    by_cases harg : 0 < (M : ℝ) * ‖x0 - xStar‖ / ε
    · have hlog_le :
          Real.log ((M : ℝ) * ‖x0 - xStar‖ / ε) ≤
            Real.log (((2 : ℝ) * (M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε)) :=
        Real.log_le_log harg harg_le
      exact le_trans (mul_le_mul_of_nonneg_left hlog_le hcoeff_nonneg) hN
    · have hlog_eq :
          Real.log ((M : ℝ) * ‖x0 - xStar‖ / ε) = 0 := by
        have harg_nonneg : 0 ≤ (M : ℝ) * ‖x0 - xStar‖ / ε := by
          positivity
        have harg_eq : (M : ℝ) * ‖x0 - xStar‖ / ε = 0 :=
          le_antisymm (le_of_not_gt harg) harg_nonneg
        rw [harg_eq]
        simp
      rw [hlog_eq, mul_zero]
      positivity
  -- Route correction: apply the earlier controlling-ball theorem directly instead of routing
  -- through the later source-facing restatement from `Theorem_3_48`.
  have hbudget' :
      (N : ℝ) ≥
        ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log ((M : ℝ) * ‖xSeq 0 - xStar‖ / ε) := by
    simpa [hxSeq_zero] using hbudget
  exact
    bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn
      projQ hproj hμ hε (strongConvexOn_closedBall hf) hxStarQ
      xSeq g hsubgrad hsubgrad_norm hxSeq_succ hbudget'

end StronglyConvexProjectedSubgradient

end
