/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_36
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_30

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable [FiniteDimensional ℝ E]

/- Primary domain: constrained projected-gradient inequalities on a nonempty closed convex
feasible set in a complete real inner-product space.

Owner declarations sampled for this refinement:
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`, which own the projected step
  point and residual;
* `gradientMapping_minimizes_objective` in `Definition_2_35`, the owner bridge from the projected
  step to the quadratically regularized affine model minimizer;
* `ConvexC1SeminormSmoothOn.tangentErrorBounds` in `Theorem_2_5`, the smooth owner used for the
  value-decrease inequality in part `(1)`;
* `StrongConvexSmoothOn.lower_tangent_quadratic` in `Definition_2_36`, the constrained
  `𝓢[μ, L]¹¹(Q)` owner theorem used for the minimizer inequality in part `(2)`.

Best owner abstraction:
* part `(1)`: a constrained owner problem `problem : SetConstrainedMinimizationProblem E`
  together with feasible-set geometry and the smooth owner
  `ConvexC1SeminormSmoothOn (normSeminorm ℝ E) L problem.feasibleSet problem`;
* part `(2)`: the same owner problem together with
  `h : problem.IsConstrainedStrongConvexSmooth μ L`, whose objective component is the source-facing
  membership `problem.objective ∈ 𝓢[μ, L]¹¹(problem.feasibleSet)`.

Source/core/bridge triage:
* source-facing: the two textbook one-step projected-gradient corollaries in Theorem 2.37;
* core/canonical: `problem`, `gradientMapping`, `reducedGradient`, and the smooth/strong owner
  predicates above;
* bridge/view: `gradientMapping_minimizes_objective`,
  `ConvexC1SeminormSmoothOn.tangentErrorBounds`, and
  `StrongConvexSmoothOn.lower_tangent_quadratic`.

Primitive data:
* the constrained owner problem together with the closed feasible-set hypothesis;
* the smooth owner for part `(1)` and the stronger owner for part `(2)`;
* the feasible base point `xBar`, which supplies the nonempty witness in part `(1)`, the positive
  stepsize `γ`, and the feasible minimizer `xStar` when present.

Derived API:
* the projected point `xQ`;
* the reduced gradient `gQ`;
* convexity of the feasible set, recovered from `ConvexC1SeminormSmoothOn.convex` and the
  strong-smooth owner in part `(2)`;
* the source-facing decrease and optimality inequalities below.

This file therefore stays a thin source-facing corollary layer over the chapter owners. It keeps
no parallel projected-step wrapper structure or duplicate owner declaration. -/

section

variable (problem : SetConstrainedMinimizationProblem E) {L : NNReal}
variable
    (hQ_closed : IsClosed problem.feasibleSet)
    (hSmooth :
      ConvexC1SeminormSmoothOn (normSeminorm ℝ E) L problem.feasibleSet problem)
    (xBar : E) (hxBar : xBar ∈ problem.feasibleSet) {γ : NNRealˣ}

local notation "xQ" =>
  x_Q[problem.feasibleSet; Exists.intro xBar hxBar; hQ_closed; hSmooth.convex | problem; γ](xBar)

local notation "gQ" =>
  g_Q[problem.feasibleSet; Exists.intro xBar hxBar; hQ_closed; hSmooth.convex | problem; γ](xBar)

/-- Helper for Theorem 2.37: projection optimality of `x_Q(xBar; γ)` yields the variational
inequality
`γ ⟪xBar - x_Q(xBar; γ), x - x_Q(xBar; γ)⟫ ≤ ⟪∇problem xBar, x - x_Q(xBar; γ)⟫`
for every feasible comparison point `x`. -/
lemma gradientMapping_projection_inner_le_gradient_inner
    (x : E) (hx : x ∈ problem.feasibleSet) :
    (γ : ℝ) * inner ℝ (xBar - xQ) (x - xQ) ≤
      inner ℝ (∇ problem xBar) (x - xQ) := by
  have hproj :
      IsProjectionPointOn problem.feasibleSet (gradientStep problem xBar γ) xQ := by
    simpa using
      gradientMapping_isProjectionPointOn
        problem.feasibleSet
        (Exists.intro xBar hxBar)
        hQ_closed
        hSmooth.convex
        problem
        γ
        xBar
  -- The projection point characterization converts the geometry of `xQ` into an inner-product
  -- inequality against every feasible comparison point.
  have hinner :
      0 ≤ inner ℝ (xQ - gradientStep problem xBar γ) (x - xQ) := by
    exact hproj.inner_sub_nonneg hSmooth.convex hx
  have hγ_pos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hscaled :
      0 ≤ (γ : ℝ) * inner ℝ (xQ - gradientStep problem xBar γ) (x - xQ) := by
    exact mul_nonneg hγ_pos.le hinner
  -- Expanding the explicit gradient step isolates the tangent term at `xBar`.
  have hrewrite :
      (γ : ℝ) * inner ℝ (xQ - gradientStep problem xBar γ) (x - xQ) =
        -(γ : ℝ) * inner ℝ (xBar - xQ) (x - xQ) +
          inner ℝ (∇ problem xBar) (x - xQ) := by
    rw [gradientStep]
    calc
      (γ : ℝ) * inner ℝ (xQ - (xBar - (γ : ℝ)⁻¹ • ∇ problem xBar)) (x - xQ)
          = (γ : ℝ) *
              inner ℝ ((xQ - xBar) + (γ : ℝ)⁻¹ • ∇ problem xBar) (x - xQ) := by
                congr 2
                abel_nf
      _ = (γ : ℝ) *
            (inner ℝ (xQ - xBar) (x - xQ) +
              inner ℝ ((γ : ℝ)⁻¹ • ∇ problem xBar) (x - xQ)) := by
              rw [inner_add_left]
      _ = (γ : ℝ) * inner ℝ (xQ - xBar) (x - xQ) +
            (γ : ℝ) * inner ℝ ((γ : ℝ)⁻¹ • ∇ problem xBar) (x - xQ) := by
              ring
      _ = -(γ : ℝ) * inner ℝ (xBar - xQ) (x - xQ) +
            inner ℝ (∇ problem xBar) (x - xQ) := by
              have hdisp :
                  (γ : ℝ) * inner ℝ (xQ - xBar) (x - xQ) =
                    -(γ : ℝ) * inner ℝ (xBar - xQ) (x - xQ) := by
                rw [show xQ - xBar = -(xBar - xQ) by abel, inner_neg_left]
                ring
              have hgrad :
                  (γ : ℝ) * inner ℝ ((γ : ℝ)⁻¹ • ∇ problem xBar) (x - xQ) =
                    inner ℝ (∇ problem xBar) (x - xQ) := by
                rw [real_inner_smul_left]
                field_simp [hγ_pos.ne']
              rw [hdisp, hgrad]
  rw [hrewrite] at hscaled
  linarith

/-- Theorem 2.37 (1): on a nonempty closed convex feasible set whose objective lies in
`𝓕_L^{1,1}(Q)`, the projected gradient step with parameter `γ ≥ L` decreases the objective by at
least `(2γ)⁻¹ ‖g_Q(xBar; γ)‖²`. -/
-- Proof sketch: `gradientMapping_minimizes_objective` identifies `xQ` as the minimizer of the
-- quadratic first-order model over `Q`, while `hSmooth.tangentErrorBounds` compares
-- `problem xQ` with that model value at the feasible point `xBar`. Evaluating the model at
-- `xBar` makes the displacement terms vanish. The feasible hypothesis `hxBar` supplies the needed
-- witness that `problem.feasibleSet` is nonempty, and rewriting the remaining quadratic term
-- through `gQ = γ • (xBar - xQ)` yields the displayed decrease estimate.
theorem gradientMapping_value_le_sub_reducedGradient_sq
    (hγ : (L : ℝ) ≤ (γ : ℝ)) :
    problem xQ ≤
      problem xBar -
        (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) := by
  have hxQ_mem :
      xQ ∈ problem.feasibleSet :=
    (gradientMapping_minimizes_objective
      (Q := problem.feasibleSet)
      (hQ_nonempty := Exists.intro xBar hxBar)
      hQ_closed
      hSmooth.convex
      (f := problem)
      (xBar := xBar)
      (γ := γ)).1
  -- The smooth upper tangent inequality controls the objective at the projected point.
  have hupper :
      problem xQ ≤
        problem xBar +
          inner ℝ (∇ problem xBar) (xQ - xBar) +
          ((L : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    have hupper_raw :
        problem xQ - problem xBar - inner ℝ (∇ problem xBar) (xQ - xBar) ≤
          ((L : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
      simpa [norm_sub_rev] using hSmooth.tangentErrorBounds.upperBound hxBar hxQ_mem
    linarith
  -- The projection inequality at `xBar` upgrades the tangent term to a full quadratic decrease.
  have hdir :
      inner ℝ (∇ problem xBar) (xQ - xBar) ≤
        -(γ : ℝ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    have hproj :=
      gradientMapping_projection_inner_le_gradient_inner
        (problem := problem)
        (hQ_closed := hQ_closed)
        (hSmooth := hSmooth)
        (xBar := xBar)
        (hxBar := hxBar)
        (γ := γ)
        xBar
        hxBar
    have hself :
        inner ℝ (xBar - xQ) (xBar - xQ) = ‖xQ - xBar‖ ^ (2 : ℕ) := by
      rw [real_inner_self_eq_norm_sq, norm_sub_rev]
    have hright :
        inner ℝ (∇ problem xBar) (xBar - xQ) =
          -inner ℝ (∇ problem xBar) (xQ - xBar) := by
      rw [show xBar - xQ = -(xQ - xBar) by abel, inner_neg_right]
    rw [hself, hright] at hproj
    nlinarith
  have hγ_pos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  -- Rewriting `gQ = γ • (xBar - xQ)` converts the quadratic distance term into `‖gQ‖² / (2γ)`.
  have hgQ_sq :
      ‖gQ‖ ^ (2 : ℕ) =
        (γ : ℝ) ^ (2 : ℕ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    calc
      ‖gQ‖ ^ (2 : ℕ) = ‖(γ : ℝ) • (xBar - xQ)‖ ^ (2 : ℕ) := by rfl
      _ = (((γ : ℝ) * ‖xBar - xQ‖) : ℝ) ^ (2 : ℕ) := by
            rw [norm_smul, Real.norm_of_nonneg hγ_pos.le]
      _ = (γ : ℝ) ^ (2 : ℕ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
            rw [norm_sub_rev]
            ring
  have hgQ_term :
      (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) =
        ((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    rw [hgQ_sq]
    field_simp [hγ_pos.ne']
  rw [hgQ_term]
  nlinarith [hupper, hdir, hγ, sq_nonneg ‖xQ - xBar‖]

end

section

variable (problem : SetConstrainedMinimizationProblem E) {μ L : ℝ}
variable
    (h : problem.IsConstrainedStrongConvexSmooth μ L)
    (xBar : E) {γ : NNRealˣ}

local notation "xQ" =>
  x_Q[problem.feasibleSet; h.nonempty; h.isClosed; h.convex | problem; γ](xBar)

local notation "gQ" =>
  g_Q[problem.feasibleSet; h.nonempty; h.isClosed; h.convex | problem; γ](xBar)

/-- Helper for Theorem 2.37: quadratic growth from a feasible minimizer lower-bounds the
objective at the projected point by the optimum value plus
`(μ / 2) ‖x_Q(xBar; γ) - xStar‖²`. -/
lemma objective_at_projected_point_ge_optimum_plus_sqdist
    (xStar : E) (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hxStar : IsMinOn problem problem.feasibleSet xStar) :
    problem xQ ≥
      problem xStar + (μ / 2) * ‖xQ - xStar‖ ^ (2 : ℕ) := by
  have hxQ_mem :
      xQ ∈ problem.feasibleSet :=
    (gradientMapping_minimizes_objective
      (Q := problem.feasibleSet)
      (hQ_nonempty := h.nonempty)
      h.isClosed
      h.convex
      (f := problem)
      (xBar := xBar)
      (γ := γ)).1
  -- Strong convexity at the feasible minimizer is exactly the quadratic-growth step
  -- from `(2.2.40)`.
  simpa using
    StrongConvexOn.quadratic_growth_of_isMinOn_of_mem
      (hf := StrongConvexSmoothOn.strongConvexOn h.objective_mem)
      hxStar_mem
      hxStar
      xQ
      hxQ_mem

/-- Theorem 2.37 (2): for a constrained `𝓢^{1,1}_{μ,L}(Q)` problem and a feasible optimal
solution `xStar`, the reduced gradient at a feasible base point `xBar` satisfies the lower bound
involving the squared distances from `xBar` and `x_Q(xBar; γ)` to `xStar` whenever `γ ≥ L`. -/
-- Proof sketch: compare the quadratic model minimized at `xQ` with its value at the feasible
-- minimizer `xStar` using `gradientMapping_minimizes_objective`. Then combine the minimizing
-- property of `xStar` with the quadratic-growth consequence of
-- `StrongConvexSmoothOn.lower_tangent_quadratic h.objective_mem` to recover the extra
-- `(μ / 2) ‖xQ - xStar‖²` term.
-- Rewriting the remaining model terms through `gQ = γ • (xBar - xQ)` gives the stated bound.
theorem reducedGradient_inner_sub_optimal_ge
    (hxBar_mem : xBar ∈ problem.feasibleSet) (hγ : L ≤ (γ : ℝ))
    (xStar : E) (hxStar_mem : xStar ∈ problem.feasibleSet)
    (hxStar : IsMinOn problem problem.feasibleSet xStar) :
    inner ℝ gQ (xBar - xStar) ≥
      (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) +
        (μ / 2) * ‖xQ - xStar‖ ^ (2 : ℕ) := by
  have hL_nonneg : 0 ≤ L := by
    exact le_trans (StrongConvexSmoothOn.mu_pos h.objective_mem).le
      (StrongConvexSmoothOn.mu_le_L h.objective_mem)
  have hγ' : ((Real.toNNReal L : NNReal) : ℝ) ≤ (γ : ℝ) := by
    simpa [Real.toNNReal_of_nonneg hL_nonneg] using hγ
  have hvalue_drop :
      problem xQ ≤
        problem xBar - (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) := by
    simpa using
      gradientMapping_value_le_sub_reducedGradient_sq
        (problem := problem)
        (L := Real.toNNReal L)
        (hQ_closed := h.isClosed)
        (hSmooth := StrongConvexSmoothOn.smooth h.objective_mem)
        (xBar := xBar)
        (hxBar := hxBar_mem)
        (γ := γ)
        hγ'
  have hprojected_growth :
      problem xQ ≥
        problem xStar + (μ / 2) * ‖xQ - xStar‖ ^ (2 : ℕ) := by
    simpa using
      objective_at_projected_point_ge_optimum_plus_sqdist
        (problem := problem)
        (h := h)
        (xBar := xBar)
        (γ := γ)
        xStar
        hxStar_mem
        hxStar
  have hxQ_mem :
      xQ ∈ problem.feasibleSet :=
    (gradientMapping_minimizes_objective
      (Q := problem.feasibleSet)
      (hQ_nonempty := h.nonempty)
      h.isClosed
      h.convex
      (f := problem)
      (xBar := xBar)
      (γ := γ)).1
  have hγ_pos : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hgQ_sq :
      ‖gQ‖ ^ (2 : ℕ) =
        (γ : ℝ) ^ (2 : ℕ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    calc
      ‖gQ‖ ^ (2 : ℕ) = ‖(γ : ℝ) • (xBar - xQ)‖ ^ (2 : ℕ) := by rfl
      _ = (((γ : ℝ) * ‖xBar - xQ‖) : ℝ) ^ (2 : ℕ) := by
            rw [norm_smul, Real.norm_of_nonneg hγ_pos.le]
      _ = (γ : ℝ) ^ (2 : ℕ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
            rw [norm_sub_rev]
            ring
  have hgQ_term :
      (1 / (2 * (γ : ℝ))) * ‖gQ‖ ^ (2 : ℕ) =
        ((γ : ℝ) / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    rw [hgQ_sq]
    field_simp [hγ_pos.ne']
  have hupper_xQ :
      problem xQ ≤
        problem xBar +
          inner ℝ (∇ problem xBar) (xQ - xBar) +
          (L / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
    have hupper_raw :
        problem xQ - problem xBar - inner ℝ (∇ problem xBar) (xQ - xBar) ≤
          (L / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
      simpa [Real.toNNReal_of_nonneg hL_nonneg, norm_sub_rev] using
        (StrongConvexSmoothOn.smooth h.objective_mem).tangentErrorBounds.upperBound
          hxBar_mem
          hxQ_mem
    linarith
  -- Strong convexity at `xStar`, projection optimality at `xStar`, and the smooth upper tangent
  -- bound at `xQ` together produce the source inequality.
  have hmain :
      inner ℝ gQ (xBar - xStar) ≥
        problem xQ - problem xStar +
          ((γ : ℝ) - L / 2) * ‖xQ - xBar‖ ^ (2 : ℕ) +
          (μ / 2) * ‖xBar - xStar‖ ^ (2 : ℕ) := by
    have hlower :
        problem xStar ≥
          problem xBar +
            inner ℝ (∇ problem xBar) (xStar - xBar) +
            (μ / 2) * ‖xStar - xBar‖ ^ (2 : ℕ) := by
      simpa using
        StrongConvexSmoothOn.lower_tangent_quadratic
          h.objective_mem
          hxBar_mem
          hxStar_mem
    have hproj_star :
        inner ℝ gQ (xStar - xQ) ≤
          inner ℝ (∇ problem xBar) (xStar - xQ) := by
      have hproj_star_raw :=
        gradientMapping_projection_inner_le_gradient_inner
          (problem := problem)
          (L := Real.toNNReal L)
          (hQ_closed := h.isClosed)
          (hSmooth := StrongConvexSmoothOn.smooth h.objective_mem)
          (xBar := xBar)
          (hxBar := hxBar_mem)
          (γ := γ)
          xStar
          hxStar_mem
      simpa [show gQ = (γ : ℝ) • (xBar - xQ) by rfl, real_inner_smul_left] using hproj_star_raw
    have hsplit_grad :
        inner ℝ (∇ problem xBar) (xStar - xBar) =
          inner ℝ (∇ problem xBar) (xStar - xQ) +
            inner ℝ (∇ problem xBar) (xQ - xBar) := by
      have hsplit_vec :
          xStar - xBar = (xStar - xQ) + (xQ - xBar) := by
        abel_nf
      rw [hsplit_vec, inner_add_right]
    have hsplit_gQ :
        inner ℝ gQ (xStar - xQ) =
          -inner ℝ gQ (xBar - xStar) +
            (γ : ℝ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
      have hsplit_vec :
          xStar - xQ = (xStar - xBar) + (xBar - xQ) := by
        abel_nf
      rw [hsplit_vec, inner_add_right]
      have hneg :
          inner ℝ gQ (xStar - xBar) = -inner ℝ gQ (xBar - xStar) := by
        rw [show xStar - xBar = -(xBar - xStar) by abel, inner_neg_right]
      have hself :
          inner ℝ gQ (xBar - xQ) = (γ : ℝ) * ‖xQ - xBar‖ ^ (2 : ℕ) := by
        rw [show gQ = (γ : ℝ) • (xBar - xQ) by rfl, real_inner_smul_left,
          real_inner_self_eq_norm_sq, norm_sub_rev]
      rw [hneg, hself]
    have hnorm :
        ‖xStar - xBar‖ ^ (2 : ℕ) = ‖xBar - xStar‖ ^ (2 : ℕ) := by
      rw [norm_sub_rev]
    rw [hsplit_grad, hnorm] at hlower
    nlinarith [hlower, hproj_star, hupper_xQ, hsplit_gQ]
  rw [hgQ_term]
  nlinarith [hmain, hprojected_growth, hγ, sq_nonneg ‖xQ - xBar‖]

end

end
