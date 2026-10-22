/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_7

noncomputable section

universe u v

/- Proposition 6.7 lies in the chapter's prox-smoothed primal-objective approximation domain.

Relevant sampled owner declarations in this domain:
- `smoothedPrimalObjectiveMaximand` in `Chap06/Definition_6_30`, the chapter owner for the
  regularized dual maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d₂(u)`;
- `smoothedPrimalObjective` in `Chap06/Definition_6_30`, the chapter owner for the smoothed primal
  objective `f_μ`;
- `NesterovIsProxCenter` in `Chap06/Definition_6_31`, the canonical owner for the normalized prox-center
  data used to derive `0 ≤ D₂`;
- `Real.sSup_le`, `le_csSup`, and `csSup_le` in mathlib, the canonical supremum API for passing
  from pointwise maximand bounds to the owner-level error bound.

Best owner abstraction:
- source-facing: Proposition 6.7's approximation bound comparing the zero-smoothed objective
  `f₀ = smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0` with the prox-smoothed objective
  `f_μ = smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ`;
- core/canonical: `smoothedPrimalObjective` and `smoothedPrimalObjectiveMaximand`;
- bridge/view: the prox-budget hypothesis `d₂(u) ≤ D₂` on `Q₂`, together with the normalized
  prox-center witness `NesterovIsProxCenter Q₂ d₂ u₀` that forces `0 ≤ D₂`.

Primitive data:
- the linear map `A`, feasible set `Q₂`, dual term `hatφ`, prox term `d₂`, and smoothing
  parameter `μ`;
- the normalized prox-center `u₀`;
- the prox budget `D₂` as an upper bound for `d₂` on `Q₂`.

Derived API:
- the pointwise owner-level sandwich
  `f₀(x) ≥ f_μ(x) ≥ f₀(x) - μ D₂`;
- the pointwise absolute-error bound
  `|f_μ(x) - f₀(x)| ≤ μ D₂`;
- the uniform error bound on the range supremum of that absolute error.

Source/core/bridge triage:
- source-facing: `smoothedPrimalObjective_error_bounds`;
- core/canonical: `smoothedPrimalObjective`;
- bridge/view: `smoothedPrimalObjective_pointwiseErrorBound` and
  `smoothedPrimalObjective_uniformErrorBound`.

The previous revision erased the Chapter 6 smoothing owner and restated the proposition as a
generic theorem about arbitrary functions `f₀` and `fμ`. This refinement restores the proposition
to the canonical smoothing object from Definition 6.7 and derives the range-supremum error bound
from the owner-level pointwise estimate, using the prox-center normalization to discharge the
nonnegativity side condition on `μ D₂`.
-/

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

private theorem smoothedPrimalObjectiveMaximand_le_zeroSmoothed
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ} {μ : ℝ} {u₀ : E₂}
    (hμ : 0 ≤ μ) (hu₀ : NesterovIsProxCenter Q₂ d₂ u₀) (x : E₁) {u : E₂} (hu : u ∈ Q₂) :
    smoothedPrimalObjectiveMaximand A hatφ d₂ μ x u ≤
      smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x u := by
  rw [smoothedPrimalObjectiveMaximand, smoothedPrimalObjectiveMaximand]
  have hd₂_nonneg : 0 ≤ d₂ u := by
    have hmin := hu₀.isMinOn hu
    simpa [hu₀.value_eq_zero] using hmin
  nlinarith [mul_nonneg hμ hd₂_nonneg]

private theorem zeroSmoothedMaximand_le_smoothed_add_budget
    {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ} {μ D₂ : ℝ}
    (hμ : 0 ≤ μ) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂) (x : E₁) {u : E₂} (hu : u ∈ Q₂) :
    smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x u ≤
      smoothedPrimalObjectiveMaximand A hatφ d₂ μ x u + μ * D₂ := by
  rw [smoothedPrimalObjectiveMaximand, smoothedPrimalObjectiveMaximand]
  have hmul : μ * d₂ u ≤ μ * D₂ := mul_le_mul_of_nonneg_left (hD₂ u hu) hμ
  linarith

omit [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] in
private theorem smoothedPrimalObjective_budget_nonneg
    {Q₂ : Set E₂} {d₂ : E₂ → ℝ} {μ D₂ : ℝ} {u₀ : E₂}
    (hμ : 0 ≤ μ) (hu₀ : NesterovIsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂) :
    0 ≤ μ * D₂ := by
  have hD₂_nonneg : 0 ≤ D₂ := by
    have hbound := hD₂ u₀ hu₀.mem
    simpa [hu₀.value_eq_zero] using hbound
  exact mul_nonneg hμ hD₂_nonneg

section

variable
  {A : E₁ →L[ℝ] StrongDual ℝ E₂} {Q₂ : Set E₂} {hatφ d₂ : E₂ → ℝ}
  {μ D₂ : ℝ} {u₀ : E₂}

-- Proof sketch: compare the zero-smoothed and `μ`-smoothed maximands pointwise on `Q₂`, then pass
-- to the corresponding suprema. The prox-center normalization supplies `0 ≤ μ D₂` in the
-- unbounded-above fallback branch of the real `sSup` API.
/-- Proposition 6.7: if `μ ≥ 0`, `u₀` is a prox-center of `d₂` on `Q₂`, and `d₂(u) ≤ D₂` for
every `u ∈ Q₂`, then the Chapter 6 zero-smoothed objective
`smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0` and the prox-smoothed objective
`smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ` satisfy
`f₀(x) ≥ f_μ(x) ≥ f₀(x) - μ D₂` for every `x`. -/
theorem smoothedPrimalObjective_error_bounds
    (hμ : 0 ≤ μ) (hu₀ : NesterovIsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂)
    (x : E₁) :
    smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x ≥
      smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x ∧
    smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x ≥
      smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x - μ * D₂ := by
  let S0 := smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x '' Q₂
  let Sμ := smoothedPrimalObjectiveMaximand A hatφ d₂ μ x '' Q₂
  have hQ : Q₂.Nonempty := ⟨u₀, hu₀.mem⟩
  have hμD₂ : 0 ≤ μ * D₂ := smoothedPrimalObjective_budget_nonneg hμ hu₀ hD₂
  by_cases hS0 : BddAbove S0
  · have hSμ : BddAbove Sμ := by
      refine ⟨sSup S0, ?_⟩
      rintro y ⟨u, hu, rfl⟩
      exact
        (smoothedPrimalObjectiveMaximand_le_zeroSmoothed hμ hu₀ x hu).trans
          (le_csSup hS0 (Set.mem_image_of_mem _ hu))
    have hsSup_upper : sSup Sμ ≤ sSup S0 := by
      refine csSup_le ?_ ?_
      · simpa [Sμ] using hQ.image (smoothedPrimalObjectiveMaximand A hatφ d₂ μ x)
      · rintro y ⟨u, hu, rfl⟩
        exact
          (smoothedPrimalObjectiveMaximand_le_zeroSmoothed hμ hu₀ x hu).trans
            (le_csSup hS0 (Set.mem_image_of_mem _ hu))
    have hsSup_lower : sSup S0 ≤ sSup Sμ + μ * D₂ := by
      refine csSup_le ?_ ?_
      · simpa [S0] using hQ.image (smoothedPrimalObjectiveMaximand A hatφ d₂ 0 x)
      · rintro y ⟨u, hu, rfl⟩
        exact
          (zeroSmoothedMaximand_le_smoothed_add_budget hμ hD₂ x hu).trans
            (by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_right (le_csSup hSμ (Set.mem_image_of_mem _ hu)) (μ * D₂))
    constructor
    · simpa [smoothedPrimalObjective, S0, Sμ] using hsSup_upper
    · simpa [smoothedPrimalObjective, S0, Sμ, sub_le_iff_le_add] using hsSup_lower
  · have hSμ : ¬ BddAbove Sμ := by
      intro hSμ
      apply hS0
      refine ⟨sSup Sμ + μ * D₂, ?_⟩
      rintro y ⟨u, hu, rfl⟩
      exact
        (zeroSmoothedMaximand_le_smoothed_add_budget hμ hD₂ x hu).trans
          (by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (le_csSup hSμ (Set.mem_image_of_mem _ hu)) (μ * D₂))
    constructor
    · rw [smoothedPrimalObjective, smoothedPrimalObjective, Real.sSup_of_not_bddAbove hS0,
        Real.sSup_of_not_bddAbove hSμ]
    · rw [smoothedPrimalObjective, smoothedPrimalObjective, Real.sSup_of_not_bddAbove hS0,
        Real.sSup_of_not_bddAbove hSμ]
      linarith

/-- The owner-level error bounds of Proposition 6.7 imply the pointwise absolute approximation
estimate `|f_μ(x) - f₀(x)| ≤ μ D₂`. -/
theorem smoothedPrimalObjective_pointwiseErrorBound
    (hμ : 0 ≤ μ) (hu₀ : NesterovIsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂)
    (x : E₁) :
    |smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x -
        smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x| ≤
      μ * D₂ := by
  rcases smoothedPrimalObjective_error_bounds hμ hu₀ hD₂ x with ⟨hupper, hlower⟩
  refine abs_le.2 ?_
  constructor
  · linarith
  · linarith [sub_nonpos.mpr hupper]

-- Proof sketch: `NesterovIsProxCenter` and the budget hypothesis give `0 ≤ μ D₂`; then apply
-- `Real.sSup_le` to the range of the pointwise absolute error bound.
/-- The approximation estimate of Proposition 6.7 is uniform:
`sup_x |f_μ(x) - f₀(x)| ≤ μ D₂` for the canonical Chapter 6 smoothing owner. -/
theorem smoothedPrimalObjective_uniformErrorBound
    (hμ : 0 ≤ μ) (hu₀ : NesterovIsProxCenter Q₂ d₂ u₀) (hD₂ : ∀ u ∈ Q₂, d₂ u ≤ D₂) :
    sSup
        (Set.range fun x ↦
          |smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x -
              smoothedPrimalObjective A Q₂ 0 hatφ d₂ 0 x|) ≤
      μ * D₂ := by
  have hμD₂ : 0 ≤ μ * D₂ := smoothedPrimalObjective_budget_nonneg hμ hu₀ hD₂
  refine Real.sSup_le ?_ hμD₂
  rintro y ⟨x, rfl⟩
  exact smoothedPrimalObjective_pointwiseErrorBound hμ hu₀ hD₂ x

end
