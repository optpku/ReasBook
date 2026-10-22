/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_7
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_21

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient Topology WithTopConvexAnalysis

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Lemma 3.10 lies in the chapter's extended-valued convex-analysis / continuous-subgradient
selection domain.

Mandatory domain-style sampling before refinement:
- `subdifferential` and the notation `∂ f(x)` in `Definition_3_1_5`, the chapter owner for
  extended-valued subgradients;
- `HasGradientAt` and `gradient` from mathlib's gradient API, the canonical owner for
  differentiability together with a specified gradient vector;
- `subdifferential_eq_singleton_gradient` in `Lemma_3_1_7`, the chapter theorem relating
  differentiability to the singleton subdifferential owner;
- `convexDirectionalDerivativeReal_isGreatest_subgradientPairing_of_mem_interior` and
  `subdifferential_convexDirectionalDerivativeReal_at_zero_eq_subdifferential` in `Theorem_3_21`,
  the chapter owner theorems controlling directional derivatives and subdifferentials at interior
  points.

Best owner abstraction:
- source-facing: the continuous subgradient selection theorem below;
- core/canonical: `HasGradientAt (withTopRealPart f) (g x0) x0`;
- bridge/view: the derived differentiability and gradient-identification consequences.

Primitive data:
- a convex extended-real-valued function `f`;
- an interior base point `x0 ∈ interior (dom f)`;
- a local subgradient selection `g`;
- eventual owner membership `g x ∈ ∂ f(x)` near `x0`;
- continuity of `g` at `x0`.

Derived API:
- `hasGradientAt_withTopRealPart_of_continuous_subgradient_selection`;
- `differentiableAt_withTopRealPart_of_continuous_subgradient_selection`;
- `gradient_eq_of_continuous_subgradient_selection`.

Source/core/bridge triage:
- source-facing: Lemma 3.10's differentiability conclusion from a continuous subgradient
  selection;
- core/canonical: `HasGradientAt`, `withTopRealPart`, and `subdifferential`;
- bridge/view: the differentiability and explicit-gradient corollaries derived from the owner
  `HasGradientAt` statement.

The finite-maximum API from `Lemma_3_13` belongs to a later and unrelated source item. This file
therefore returns to the actual Chapter 3.10 domain and states the result directly on the chapter
owners `∂ f(x)`, `withTopRealPart f`, and the canonical gradient owner `HasGradientAt`, instead
of recalling later active-maximum machinery.
-/

section ContinuousSubgradientSelection

variable {f : E → WithTop ℝ} {x0 : E} {g : E → E}

/-- Lemma 3.10: if `f : E → ℝ ∪ {+∞}` is convex, `x₀` lies in the interior of its effective
domain, and a subgradient selection `g` is continuous at `x₀`, then the finite real
representative `withTopRealPart f` has gradient `g x₀` at `x₀`. This is the canonical owner form
of the textbook statement that `f` is differentiable at `x₀` with `∇f(x₀) = g(x₀)`. -/
-- Proof sketch: for each direction `p`, apply the subgradient inequality at nearby points
-- carrying the chosen subgradient `g x`, compare with the interior-point directional-derivative
-- owner from `Theorem_3_21`, and pass to the limit using `hcont`. The resulting directional
-- derivatives are the linear functional `p ↦ ⟪g x₀, p⟫`, which is exactly the
-- `HasGradientAt` owner statement.
theorem hasGradientAt_withTopRealPart_of_continuous_subgradient_selection
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f))
    (hsub : ∀ᶠ x in 𝓝 x0, g x ∈ ∂ f(x))
    (hcont : ContinuousAt g x0) :
    HasGradientAt (withTopRealPart f) (g x0) x0 := by
  rw [hasGradientAt_iff_tendsto]
  -- Read the goal through the explicit inner-product remainder from the gradient API.
  change Filter.Tendsto
    (fun y : E ↦
      ‖y - x0‖⁻¹ *
        ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖)
    (𝓝 x0) (𝓝 0)
  let _ := hf
  -- Extract the base-point subgradient from the neighborhood selection hypothesis.
  have hx0_sub : g x0 ∈ ∂ f(x0) :=
    hsub.self_of_nhds
  have hx0_sub' : IsSubgradientAt f x0 (g x0) :=
    mem_subdifferential_iff.mp hx0_sub
  have hx0_dom : x0 ∈ dom f := hx0_sub'.mem_dom
  -- Continuity of the selected subgradient makes the variation term tend to `0`.
  have hvariation_tendsto :
      Filter.Tendsto (fun y : E ↦ ‖g y - g x0‖) (𝓝 x0) (𝓝 0) := by
    have hconst : ContinuousAt (fun _ : E ↦ g x0) x0 := continuousAt_const
    have hcontDiff : ContinuousAt (fun y : E ↦ g y - g x0) x0 :=
      hcont.sub hconst
    simpa using hcontDiff.norm.tendsto
  have hnonneg :
      ∀ᶠ y : E in 𝓝 x0,
        0 ≤
          ‖y - x0‖⁻¹ *
            ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖ := by
    exact Filter.Eventually.of_forall fun y ↦ by
      positivity
  have herror_bound :
      ∀ᶠ y : E in 𝓝 x0,
        ‖y - x0‖⁻¹ *
            ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖
          ≤ ‖g y - g x0‖ := by
    filter_upwards [hsub] with y hy
    have hy_sub : IsSubgradientAt f y (g y) :=
      mem_subdifferential_iff.mp hy
    have hy_dom : y ∈ dom f := hy_sub.mem_dom
    -- The two support inequalities trap the linearization error between `0` and the subgradient
    -- variation paired with the displacement.
    have hlower :
        withTopRealPart f x0 + inner ℝ (g x0) (y - x0) ≤ withTopRealPart f y := by
      have hlower_top :
          (((withTopRealPart f x0 : ℝ) : WithTop ℝ) +
              (inner ℝ (g x0) (y - x0) : WithTop ℝ)) ≤
            (((withTopRealPart f y : ℝ) : WithTop ℝ)) := by
        have hineq := hx0_sub'.2 hy_dom
        rw [← coe_withTopRealPart hx0_dom, ← coe_withTopRealPart hy_dom] at hineq
        exact hineq
      exact_mod_cast hlower_top
    have hupper_aux :
        withTopRealPart f y - inner ℝ (g y) (y - x0) ≤ withTopRealPart f x0 := by
      have hupper_add :
          withTopRealPart f y + inner ℝ (g y) (x0 - y) ≤ withTopRealPart f x0 := by
        have hupper_top :
            (((withTopRealPart f y : ℝ) : WithTop ℝ) +
                (inner ℝ (g y) (x0 - y) : WithTop ℝ)) ≤
              (((withTopRealPart f x0 : ℝ) : WithTop ℝ)) := by
          have hineq := hy_sub.2 hx0_dom
          rw [← coe_withTopRealPart hy_dom, ← coe_withTopRealPart hx0_dom] at hineq
          exact hineq
        exact_mod_cast hupper_top
      simpa [sub_eq_add_neg, inner_add_right, inner_neg_right, add_assoc, add_left_comm, add_comm]
        using hupper_add
    have hupper :
        withTopRealPart f y - withTopRealPart f x0 ≤ inner ℝ (g y) (y - x0) := by
      linarith
    have herror_nonneg :
        0 ≤ withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0) := by
      linarith
    have herror_le_pairing :
        withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0) ≤
          inner ℝ (g y - g x0) (y - x0) := by
      rw [inner_sub_left]
      linarith
    have herror_norm_le :
        ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖ ≤
          ‖g y - g x0‖ * ‖y - x0‖ := by
      calc
        ‖withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0)‖ =
            withTopRealPart f y - withTopRealPart f x0 - inner ℝ (g x0) (y - x0) := by
              rw [Real.norm_eq_abs, abs_of_nonneg herror_nonneg]
        _ ≤ inner ℝ (g y - g x0) (y - x0) := herror_le_pairing
        _ ≤ |inner ℝ (g y - g x0) (y - x0)| := le_abs_self _
        _ ≤ ‖g y - g x0‖ * ‖y - x0‖ := by
              simpa using abs_real_inner_le_norm (g y - g x0) (y - x0)
    by_cases hyx0 : y = x0
    · subst hyx0
      simp
    · have hy_norm_pos : 0 < ‖y - x0‖ := by
        exact norm_pos_iff.mpr (sub_ne_zero.mpr hyx0)
      exact (inv_mul_le_iff₀ hy_norm_pos).2 <| by
        simpa [mul_comm, mul_left_comm, mul_assoc] using herror_norm_le
  -- Squeeze the normalized remainder by the subgradient variation, which vanishes by continuity.
  exact squeeze_zero' hnonneg herror_bound hvariation_tendsto

/-- Companion consequence: under the hypotheses of Lemma 3.10, `withTopRealPart f` is
differentiable at `x₀`. -/
theorem differentiableAt_withTopRealPart_of_continuous_subgradient_selection
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f))
    (hsub : ∀ᶠ x in 𝓝 x0, g x ∈ ∂ f(x))
    (hcont : ContinuousAt g x0) :
    DifferentiableAt ℝ (withTopRealPart f) x0 := by
  have hgrad : HasGradientAt (withTopRealPart f) (g x0) x0 :=
    hasGradientAt_withTopRealPart_of_continuous_subgradient_selection hf hx0 hsub hcont
  exact hgrad.differentiableAt

/-- Companion consequence: under the hypotheses of Lemma 3.10, the gradient of
`withTopRealPart f` at `x₀` is the selected subgradient `g x₀`. -/
theorem gradient_eq_of_continuous_subgradient_selection
    (hf : ConvexOn ℝ (dom f) (withTopRealPart f))
    (hx0 : x0 ∈ interior (dom f))
    (hsub : ∀ᶠ x in 𝓝 x0, g x ∈ ∂ f(x))
    (hcont : ContinuousAt g x0) :
    ∇ (withTopRealPart f) x0 = g x0 := by
  have hgrad : HasGradientAt (withTopRealPart f) (g x0) x0 :=
    hasGradientAt_withTopRealPart_of_continuous_subgradient_selection hf hx0 hsub hcont
  exact hgrad.gradient

end ContinuousSubgradientSelection

end
