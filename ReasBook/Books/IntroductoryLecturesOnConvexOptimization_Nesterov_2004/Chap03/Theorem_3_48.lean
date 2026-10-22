/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_55
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_44
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open scoped WithTopConvexAnalysis StronglyConvexProblemClass

/- Theorem 3.48 lies in the chapter's projected subgradient / strongly convex complexity domain on
real inner-product spaces.

Mandatory domain-style sampling before refinement:
- `𝒫_s(x₀, μ, M)` and its owner projections
  `IsInStronglyConvexProblemClass.strongConvexOn_closedBall`,
  `IsInStronglyConvexProblemClass.isMinOn`, and
  `IsInStronglyConvexProblemClass.mu_pos` in `Theorem_3_47`;
- `bestFunctionValueUpTo` in `Definition_3_55`, the chapter owner for sampled-prefix minima;
- `∂[Q] f(x)` in `Theorem_3_44`, the chapter owner surface for real-valued constrained
  subgradients;
- `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`
  in `Theorem_3_2_6`, the explicit strong-convexity bridge theorem whose proof interface already
  uses the pointwise projection owner `IsProjectionPointOn Q x (π x)` and the sampled-value owner
  `bestFunctionValueUpTo`.

Best owner abstraction:
- source-facing: Theorem 3.48's logarithmic-budget guarantee for projected subgradient descent on
  the strongly convex class `𝒫_s(x₀, μ, M)`;
- core/canonical: the controlling ball `Q = B₂(x*, ‖x₀ - x*‖)`, the pointwise projection owner
  `IsProjectionPointOn Q x (π x)`, the constrained-subgradient owner `∂[Q] f(x)`, and the
  sampled-value owner `bestFunctionValueUpTo`;
- bridge/view: the explicit strong-convexity bridge theorem
  `bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn`
  from `Theorem_3_2_6`.

Primitive data:
- the objective `f : E → ℝ`, the minimizer `xStar`, and class membership `𝒫_s(x₀, μ, M) f xStar`;
- a chosen projection map on the controlling ball, the iterate sequence `xSeq`, and chosen
  constrained subgradients `g`.

Derived API:
- the strong-convexity and minimizer data on the controlling ball `Q`;
- the sampled-value conclusion on `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N`.

Source/core/bridge triage:
- source-facing: Theorem 3.48 stated on `𝒫_s(x₀, μ, M)`, `bestFunctionValueUpTo`, and
  `∂[Q] f(x)`;
- core/canonical: `IsProjectionPointOn`, `∂[Q] f(x)`, and `bestFunctionValueUpTo`;
- bridge/view: specialization from the `𝒫_s(x₀, μ, M)` owner surface to the explicit
  strong-convexity/minimizer data consumed by `Theorem_3_2_6`.

The previous version collapsed this later source-facing theorem to a direct recall of the earlier
legacy theorem. This file now keeps the public theorem surface on the chapter's current owner
objects and uses the older theorem only as an internal bridge. -/

section StronglyConvexProjectedSubgradient

variable {x0 xStar : E} {μ M : NNReal} {f : E → ℝ}

local notation "Q" => (Metric.closedBall xStar ‖x0 - xStar‖ : Set E)

open IsInStronglyConvexProblemClass
/-- Theorem 3.48: if `f` belongs to the strongly convex class `𝒫_s(x₀, μ, M)` with minimizer
`x*`, `π_Q` is a projection map on the controlling ball `Q = B₂(x*, ‖x₀ - x*‖)`, every selected
subgradient `g_k` lies in `∂[Q] f(x_k)`, satisfies `‖g_k‖ ≤ M`, and the projected subgradient
iteration
`x_{k+1} = π_Q (x_k - (2 ε / ‖g_k‖²) • g_k)`
is run for a budget
`N ≥ (M² / (μ ε)) log (M ‖x₀ - x*‖ / ε)`,
then the sampled best value `bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N` is at most
`f x* + ε`. -/
theorem bestFunctionValueUpTo_le_optimalValue_add_eps_of_log_budget_projected_subgradient_method
    (hf : 𝒫_s(x0, μ, M) f xStar)
    {ε : ℝ} (hε : 0 < ε)
    (projQ : E → E)
    (hproj : ∀ x : E, IsProjectionPointOn Q x (projQ x))
    (xSeq g : ℕ → E) (hxSeq_zero : xSeq 0 = x0)
    (hsubgrad : ∀ k : ℕ, g k ∈ ∂[Q] f((xSeq k)))
    (hsubgrad_norm : ∀ k : ℕ, ‖g k‖ ≤ M)
    (hxSeq_succ :
      ∀ k : ℕ,
        xSeq (k + 1) =
          projQ (xSeq k - ((2 * ε) / ‖g k‖ ^ (2 : ℕ)) • g k))
    {N : ℕ}
    (hN :
      (N : ℝ) ≥
        ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log ((M : ℝ) * ‖x0 - xStar‖ / ε)) :
    bestFunctionValueUpTo (fun i ↦ f (xSeq i)) N ≤ f xStar + ε := by
  -- Convert the stored `NNReal` positivity into the real-valued hypothesis expected by the
  -- strong-convexity bridge theorem.
  have hμ : 0 < (μ : ℝ) := by
    exact_mod_cast mu_pos hf
  -- Restrict the global minimizer recorded by the problem class to the controlling closed ball.
  have hQ_subset : Q ⊆ (Set.univ : Set E) := by
    intro y hy
    simp
  have hxStarQ : IsMinOn f Q xStar :=
    (isMinOn hf).on_subset hQ_subset
  -- Rewrite the budget assumption into the canonical `xSeq 0` form used by the imported theorem.
  have hN' :
      (N : ℝ) ≥
        ((M : ℝ) ^ (2 : ℕ)) / ((μ : ℝ) * ε) *
          Real.log ((M : ℝ) * ‖xSeq 0 - xStar‖ / ε) := by
    simpa [hxSeq_zero] using hN
  -- Apply the earlier bridge theorem on the controlling ball instead of re-running the
  -- contraction argument in this file.
  exact
    bestFunctionValueUpTo_le_optimalValue_add_eps_of_projected_subgradient_log_budget_strongConvexOn
      projQ hproj hμ hε (strongConvexOn_closedBall hf) hxStarQ
      xSeq g hsubgrad hsubgrad_norm hxSeq_succ hN'

end StronglyConvexProjectedSubgradient

end
