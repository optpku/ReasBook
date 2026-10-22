/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient StrongConvexSmooth
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The primary domain here is the linear convergence of the simple-set gradient method on a closed
convex feasible set in a real Hilbert space.

Owner abstractions sampled for this refinement:
* `f ∈ 𝓢[μ, L]¹¹` and `mem_S11_iff` from `Definition_2_17`, reexported through
  `Theorem_2_38`, provide the source-facing objective hypothesis and its bridge to the canonical
  owner predicate `IsStrongConvexSmoothObjective μ L f`;
* `simpleSetGradientMethod` together with
  `simpleSetGradientMethod_zero` and `simpleSetGradientMethod_succ_eq_gradientMapping` from
  `Algorithm_2_6` owns the recursive trajectory of Algorithm 2.6;
* `projectedGradientSequence_dist_le_geometric` from `Theorem_2_38` owns the ambient projected-
  gradient contraction statement.

Best owner abstraction:
* source-facing: `simpleSetGradientMethod`;
* core/canonical: `projectedGradientSequence_dist_le_geometric`;
* bridge/view: the identification `(γ : ℝ) = (L + μ) / 2`, which turns the generic contraction
  factor `1 - μ / γ` into `((L - μ) / (L + μ))`.

Primitive data are only the feasible set `Q`, objective `f`, feasible initial point `x0 ∈ Q`,
the constrained minimizer certificate `xStar ∈ argmin[Q] f`, and the Algorithm 2.6 owner
trajectory
`simpleSetGradientMethod ... γ`. The explicit start and recurrence laws are derived API imported
from `Algorithm_2_6`, so this file does not store them again as primitive public data. -/

/-- Remark 2.38.1: when Algorithm 2.6 uses the optimal inverse-stepsize parameter
`γ = (L + μ) / 2`, its canonical trajectory `simpleSetGradientMethod` contracts the distance to
the constrained minimizer at the same sharp linear rate as the unconstrained gradient method:
`‖x_k - xStar‖ ≤ ((L - μ) / (L + μ))^k ‖x₀ - xStar‖`. The textbook `ℝⁿ` statement is the
specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: apply `projectedGradientSequence_dist_le_geometric` to the recursive owner
-- `simpleSetGradientMethod`. The only bridge work is rewriting the parameter assumption
-- `(γ : ℝ) = (L + μ) / 2` and simplifying the contraction factor `1 - μ / γ`.
theorem simpleSetGradientMethod_dist_le_optimal_geometric_rate
    {μ L : ℝ} {Q : Set E} {f : E → ℝ} {γ : NNRealˣ}
    (hf : f ∈ 𝓢[μ, L]¹¹)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {x0 xStar : E}
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (hγ : (γ : ℝ) = (L + μ) / 2)
    (k : ℕ) :
    ‖simpleSetGradientMethod Q hQ_closed hQ_convex f x0 hx0_mem γ k - xStar‖ ≤
      ((L - μ) / (L + μ)) ^ k * ‖x0 - xStar‖ := by
  have hγ_pos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hLμ_pos : 0 < L + μ := by
    linarith [hγ_pos, hγ]
  have hrate : 1 - μ / ((L + μ) / 2) = (L - μ) / (L + μ) := by
    field_simp [hLμ_pos.ne']
    ring
  have hγ_bound : (L + μ) / 2 ≤ (γ : ℝ) := by
    rw [hγ]
  simpa [hγ, hrate] using
    projectedGradientSequence_dist_le_geometric Q hQ_closed hQ_convex
      hf hx0_mem hxStar
      (simpleSetGradientMethod Q hQ_closed hQ_convex f x0 hx0_mem γ)
      (simpleSetGradientMethod_zero Q hQ_closed hQ_convex f x0 hx0_mem γ)
      (simpleSetGradientMethod_succ_eq_gradientMapping Q hQ_closed hQ_convex f x0 hx0_mem γ)
      hγ_bound
      k

end
