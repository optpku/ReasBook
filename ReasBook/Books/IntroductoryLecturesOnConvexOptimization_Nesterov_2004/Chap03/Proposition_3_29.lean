/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis

universe u

/- Proposition 3.29 lies in the chapter's local subgradient-growth / Lipschitz-regularity domain.

Mandatory domain-style sampling before refinement:
- `dom` and `withTopRealPart` in `Definition_3_3`, the chapter owners for the effective domain and
  finite-value representative of an `ℝ ∪ {+∞}`-valued function;
- `IsSubgradientAt`, `subdifferential`, and `mem_subdifferential_iff` in `Definition_3_1_5`, the
  chapter owner surface for extended-valued subgradients and the textbook notation `∂ f(x)`;
- `LipschitzOnWith.of_le_add_mul`, the canonical mathlib bridge from one-sided difference bounds
  to a Lipschitz estimate on a set;
- nearby owner usage in `Theorem_3_1_11` and `Theorem_3_1_15`, which already organize local
  convex regularity around `dom f`, `withTopRealPart f`, and `∂ f(x)`.

Best owner abstraction:
- source-facing: the local ball estimate and Lipschitz consequence below;
- core/canonical: `dom f`, `∂ f(x)`, and `withTopRealPart f`;
- bridge/view: `LipschitzOnWith.of_le_add_mul`.

Primitive data:
- a ball `Metric.ball xStar ρ`;
- the domain-containment hypothesis on that ball;
- the subgradient-growth bound on that ball.

Derived API:
- the one-sided difference estimate for `withTopRealPart f`;
- the resulting Lipschitz estimate on the same ball.

The previous file rebuilt local copies of the effective domain, subgradient predicate, and
subdifferential, even though those notions are already owned upstream in `Definition_3_1_5`.
This refinement keeps Proposition 3.29 on the same mathematical content, but deletes that
duplicate wrapper layer and states the result directly on the chapter owner surface.
-/

variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Proposition 3.29: if every point of the ball `Metric.ball xStar ρ` lies in the effective
domain of `f` and every subgradient on that ball satisfies `‖g‖ ≤ μ * ‖y‖ + γ`, then for
`x, y ∈ Metric.ball xStar ρ` and any `g ∈ ∂ f(y)` one has the local estimate
`withTopRealPart f y - withTopRealPart f x ≤ (μ * ‖xStar‖ + μ * ρ + γ) * ‖y - x‖`. -/
-- Proof sketch: apply the subgradient inequality at `y` with comparison point `x`. Then bound
-- `⟪g, y - x⟫` by Cauchy-Schwarz, use the assumed estimate on `‖g‖`, and control `‖y‖` by
-- `‖xStar‖ + ρ` via the triangle inequality because `y ∈ Metric.ball xStar ρ`.
theorem subgradient_upper_difference_bound_on_ball
    {f : E → WithTop ℝ} {xStar x y g : E} {ρ μ γ : ℝ}
    (hμ : 0 ≤ μ)
    (hball_dom : Metric.ball xStar ρ ⊆ dom f)
    (hsubgrad_bound :
      ∀ ⦃z s : E⦄, z ∈ Metric.ball xStar ρ → s ∈ ∂ f(z) → ‖s‖ ≤ μ * ‖z‖ + γ)
    (hx : x ∈ Metric.ball xStar ρ) (hy : y ∈ Metric.ball xStar ρ)
    (hg : g ∈ ∂ f(y)) :
    withTopRealPart f y - withTopRealPart f x ≤
      (μ * ‖xStar‖ + μ * ρ + γ) * ‖y - x‖ := by
  have hx_dom : x ∈ dom f := hball_dom hx
  have hy_dom : y ∈ dom f := hball_dom hy
  have hsupport : f y + (inner ℝ g (x - y) : WithTop ℝ) ≤ f x := by
    exact (mem_subdifferential_iff.mp hg).2 hx_dom
  have hsupport_real : withTopRealPart f y + inner ℝ g (x - y) ≤ withTopRealPart f x := by
    rw [← coe_withTopRealPart hy_dom, ← coe_withTopRealPart hx_dom] at hsupport
    exact_mod_cast hsupport
  have hsubgrad_norm : ‖g‖ ≤ μ * ‖y‖ + γ := hsubgrad_bound hy hg
  have hy_ball : ‖y - xStar‖ < ρ := by
    simpa [Metric.mem_ball, dist_eq_norm] using hy
  have hy_norm : ‖y‖ ≤ ‖xStar‖ + ρ := by
    calc
      ‖y‖ = ‖(y - xStar) + xStar‖ := by abel_nf
      _ ≤ ‖y - xStar‖ + ‖xStar‖ := norm_add_le _ _
      _ = ‖xStar‖ + ‖y - xStar‖ := by ring
      _ ≤ ‖xStar‖ + ρ := by gcongr
  calc
    withTopRealPart f y - withTopRealPart f x ≤ inner ℝ g (y - x) := by
      have hinner : inner ℝ g (x - y) = -inner ℝ g (y - x) := by
        simp [inner_sub_right]
      linarith
    _ ≤ ‖g‖ * ‖y - x‖ := real_inner_le_norm _ _
    _ ≤ (μ * ‖y‖ + γ) * ‖y - x‖ := by
      gcongr
    _ ≤ (μ * ‖xStar‖ + μ * ρ + γ) * ‖y - x‖ := by
      have hbound : μ * ‖y‖ + γ ≤ μ * ‖xStar‖ + μ * ρ + γ := by
        have hmul : μ * ‖y‖ ≤ μ * (‖xStar‖ + ρ) := by gcongr
        linarith
      gcongr

/-- If every point of `Metric.ball xStar ρ` has a subgradient and all such subgradients satisfy
the same affine norm bound, then the finite-value representative `withTopRealPart f` is Lipschitz
on that ball. -/
-- Proof sketch: for each `y` in the ball choose some `g ∈ ∂ f(y)` using the nonemptiness
-- assumption, apply `subgradient_upper_difference_bound_on_ball` to get the one-sided estimate,
-- and conclude with `LipschitzOnWith.of_le_add_mul`.
theorem lipschitzOnWith_on_ball_of_subgradient_bound
    {f : E → WithTop ℝ} {xStar : E} {ρ μ γ : ℝ}
    (hμ : 0 ≤ μ)
    (hsubgrad_nonempty :
      ∀ y ∈ Metric.ball xStar ρ, (∂ f(y)).Nonempty)
    (hsubgrad_bound :
      ∀ ⦃y g : E⦄, y ∈ Metric.ball xStar ρ → g ∈ ∂ f(y) → ‖g‖ ≤ μ * ‖y‖ + γ) :
    LipschitzOnWith (Real.toNNReal (μ * ‖xStar‖ + μ * ρ + γ))
      (withTopRealPart f) (Metric.ball xStar ρ) := by
  have hball_dom : Metric.ball xStar ρ ⊆ dom f := by
    intro y hy
    rcases hsubgrad_nonempty y hy with ⟨g, hg⟩
    exact (mem_subdifferential_iff.mp hg).mem_dom
  refine LipschitzOnWith.of_le_add_mul' (μ * ‖xStar‖ + μ * ρ + γ) ?_
  intro x hx y hy
  rcases hsubgrad_nonempty x hx with ⟨g, hg⟩
  simpa [dist_eq_norm, add_comm, add_left_comm, add_assoc] using
    subgradient_upper_difference_bound_on_ball hμ hball_dom hsubgrad_bound hy hx hg

end
