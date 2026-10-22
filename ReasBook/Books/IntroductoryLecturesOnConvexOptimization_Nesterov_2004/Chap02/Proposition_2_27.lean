/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_41
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_19
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_13

open scoped Gradient StrongConvexSmooth

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section

variable {μ : ℝ} {L : NNReal} {f : E → ℝ}

local notation "shiftedObjective" => fun t : ℝ ↦ fun x : E ↦ f x - t
local notation "shiftedFamily" => fun t : ℝ ↦ fun _ x : E ↦ f x - t
local notation "modelOptimalValue" => fun t : ℝ ↦ fun xBar : E ↦ fun γ : ℝ ↦
  SetConstrainedMinimizationProblem.optimalValue
    (SetConstrainedMinimizationProblem.unconstrained
      (quadraticallyRegularizedObjective (shiftedObjective t) γ xBar))
local notation "modelValue" => fun t : ℝ ↦ fun xBar : E ↦ fun γ : ℝ ↦
  EReal.toReal (modelOptimalValue t xBar γ)

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem quadraticallyRegularizedObjective_shifted_eq_sub
    (t γ : ℝ) (xBar x : E) :
    quadraticallyRegularizedObjective (shiftedObjective t) γ xBar x =
      quadraticallyRegularizedObjective f γ xBar x - t := by
  change
    quadraticallyRegularizedObjective (fun y : E ↦ f y - t) γ xBar x =
      quadraticallyRegularizedObjective f γ xBar x - t
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

section SourceFacing

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
private theorem regularizedShiftedObjective_isMinOn_of_isMinOn
    {t γ : ℝ} {xBar x : E}
    (hx : IsMinOn (quadraticallyRegularizedObjective f γ xBar) Set.univ x) :
    IsMinOn (quadraticallyRegularizedObjective (shiftedObjective t) γ xBar) Set.univ x := by
  convert hx.sub (isMaxOn_const : IsMaxOn (fun _ : E ↦ t) Set.univ x) using 1
  ext y
  simpa using quadraticallyRegularizedObjective_shifted_eq_sub t γ xBar y

/-
Primary domain: parameter comparison for exact values of shifted quadratically regularized
objectives on a proper real Hilbert space.

Owner declarations sampled before refining:
* `quadraticallyRegularizedObjective` and `quadraticallyRegularizedObjective_apply` in
  `FirstOrderTaylorModel`, the owner regularized objective;
* `reducedGradientOf` in `Definition_2_41`, the owner reduced-gradient residual
  `γ • (xBar - xPlus)`;
* `exactValue_ge_of_lowerQuadraticModel` in `Lemma_2_19`, the owner exact-value comparison on
  `sInf ((quadraticallyRegularizedObjective ...) '' Q)`;
* `gradient_add_quadratic_regularization_eq_zero_of_isMinOn` in `Proposition_2_13`, the owner
  first-order identity at an exact regularized step;
* `f ∈ 𝓢[μ, (L : ℝ)]¹¹` and `mem_S11_iff` in `Definition_2_17`, the source-facing class surface.

Best owner abstraction:
* source-facing: Proposition 2.27's shifted exact values `modelValue t xBar γ`;
* core/canonical: the unshifted exact-step predicate
  `IsMinOn (quadraticallyRegularizedObjective f γ xBar) Set.univ xL`;
* bridge/view: subtracting the scalar shift `t` from the regularized objective and the derived
  residual `reducedGradientOf (L : ℝ) xBar xL`.

Primitive data:
* the source objective hypothesis `hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹`;
* the shifted parameter `t`, base point `xBar`, exact `L`-step `xL`, and the owner minimizer
  proof `hxL`.

Derived API:
* the unshifted reduced gradient
  `reducedGradientOf (L : ℝ) xBar xL`;
* the exact regularized values `modelValue t xBar γ = f^*(t; xBar; γ)`.

The previous version exposed a chosen-step wrapper indexed by the inert shift parameter `t` and
the source package `hf`. This refinement deletes that duplicate surface and states Proposition 2.27
directly from the unshifted exact-step owner `hxL`.
-/

/-- Proposition 2.27: if `xL` minimizes the unshifted regularized objective
`x ↦ f x + (L / 2) ‖x - xBar‖²` and
`gL := reducedGradientOf (L : ℝ) xBar xL`, then the shifted exact regularized values satisfy
`f^*(t; xBar; μ) ≥ f^*(t; xBar; L) - ((L - μ) / (2 μ L)) ‖gL‖²`.
The textbook `ℝⁿ` statement is recovered by
specializing `E := EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: the source class hypothesis gives the lower tangent quadratic bound at the exact
-- step `xL`. Proposition 2.13 identifies the gradient there with the reduced gradient
-- `reducedGradientOf (L : ℝ) xBar xL`. This is exactly the lower-model
-- hypothesis
-- required by Lemma 2.19 for the shifted objective, so the comparison of exact values follows.
theorem regularizedModelValue_mu_ge_L_sub_sq_norm
    (hf : f ∈ 𝓢[μ, (L : ℝ)]¹¹) (t : ℝ) (xBar xL : E)
    (hxL : IsMinOn (quadraticallyRegularizedObjective f (L : ℝ) xBar) Set.univ xL) :
    let gL := reducedGradientOf (L : ℝ) xBar xL
    modelValue t xBar μ ≥
      modelValue t xBar (L : ℝ) -
        (((L : ℝ) - μ) / (2 * μ * (L : ℝ))) *
          ‖gL‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxL_eq : xL = xBar := hE.elim _ _
    subst xL
    let gL : E := reducedGradientOf (L : ℝ) xBar xBar
    change
      modelValue t xBar μ ≥
        modelValue t xBar (L : ℝ) -
          (((L : ℝ) - μ) / (2 * μ * (L : ℝ))) *
            ‖gL‖ ^ (2 : ℕ)
    have hgL : gL = 0 := by
      simp [gL, reducedGradientOf]
    have hmin (γ : ℝ) :
        IsMinOn
          (quadraticallyRegularizedObjective (shiftedObjective t) γ xBar)
          Set.univ
          xBar := by
      rw [isMinOn_univ_iff]
      intro x
      have hx : x = xBar := hE.elim _ _
      simp [hx]
    have hmodel_eq (γ : ℝ) : modelValue t xBar γ = shiftedObjective t xBar := by
      calc
        modelValue t xBar γ =
            quadraticallyRegularizedObjective (shiftedObjective t) γ xBar xBar := by
              simpa [SetConstrainedMinimizationProblem.unconstrained] using
                regularizedModelOptimalValue_toReal_eq_of_isMinOn
                  Set.univ
                  (shiftedFamily t)
                  xBar
                  xBar
                  γ
                  (Set.mem_univ xBar)
                  (hmin γ)
        _ = shiftedObjective t xBar := by
              simp [quadraticallyRegularizedObjective_apply]
    rw [hmodel_eq μ, hmodel_eq (L : ℝ), hgL]
    simp
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let gL : E := reducedGradientOf (L : ℝ) xBar xL
    change
      modelValue t xBar μ ≥
        modelValue t xBar (L : ℝ) -
          (((L : ℝ) - μ) / (2 * μ * (L : ℝ))) *
            ‖gL‖ ^ (2 : ℕ)
    have hf' : IsStrongConvexSmoothObjective μ (L : ℝ) f := mem_S11_iff.mp hf
    have hμ_le_L : μ ≤ (L : ℝ) := hf'.mu_le_L
    have hL_pos : 0 < (L : ℝ) := by
      exact lt_of_lt_of_le hf'.mu_pos hμ_le_L
    have hxL_shifted :
        IsMinOn
          (quadraticallyRegularizedObjective (shiftedObjective t) (L : ℝ) xBar)
          Set.univ
          xL := by
      exact regularizedShiftedObjective_isMinOn_of_isMinOn hxL
    have hgL : gL = (L : ℝ) • (xBar - xL) := by
      simp [gL, reducedGradientOf]
    have hgrad_eq : ∇ f xL = gL := by
      have hreg :=
        gradient_add_quadratic_regularization_eq_zero_of_isMinOn
          f
          (L : ℝ)
          xBar
          xL
          (hf'.contDiff.differentiable_one xL)
          hxL
      have hgrad_eq' : ∇ f xL = (L : ℝ) • (xBar - xL) := by
        simpa [sub_eq_add_neg, smul_sub, add_comm, add_left_comm, add_assoc] using
          eq_neg_of_add_eq_zero_left hreg
      calc
        ∇ f xL = (L : ℝ) • (xBar - xL) := hgrad_eq'
        _ = gL := hgL.symm
    have hvalue_L_eq :
        modelValue t xBar (L : ℝ) =
          quadraticallyRegularizedObjective (shiftedObjective t) (L : ℝ) xBar xL := by
      simpa [SetConstrainedMinimizationProblem.unconstrained] using
        regularizedModelOptimalValue_toReal_eq_of_isMinOn
          Set.univ
          (shiftedFamily t)
          xBar
          xL
          (L : ℝ)
          (Set.mem_univ xL)
          hxL_shifted
    have hlower_aux :
        ∀ x : E,
          shiftedObjective t x ≥
            quadraticallyRegularizedObjective (shiftedObjective t) (L : ℝ) xBar xL +
              inner ℝ gL (x - xBar) +
                (1 / (2 * (L : ℝ))) * ‖gL‖ ^ (2 : ℕ) := by
      intro x
      have hstrong := hf'.lower_tangent_quadratic xL x
      have hstrong' :
          shiftedObjective t x ≥
            shiftedObjective t xL +
              inner ℝ gL (x - xL) +
                (μ / 2) * ‖x - xL‖ ^ (2 : ℕ) := by
        linarith [show
            f x ≥
              f xL + inner ℝ gL (x - xL) +
                (μ / 2) * ‖x - xL‖ ^ (2 : ℕ) by
          simpa [hgrad_eq] using hstrong]
      have hg_inner :
          inner ℝ gL (xBar - xL) = (1 / (L : ℝ)) * ‖gL‖ ^ (2 : ℕ) := by
        rw [hgL]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_smul, Real.norm_eq_abs,
          abs_of_pos hL_pos]
        field_simp [hL_pos.ne']
      have hdecomp : x - xL = (x - xBar) + (xBar - xL) := by
        abel
      have hgnorm :
          ‖gL‖ ^ (2 : ℕ) = (L : ℝ) ^ (2 : ℕ) * ‖xBar - xL‖ ^ (2 : ℕ) := by
        calc
          ‖gL‖ ^ (2 : ℕ) = ‖(L : ℝ) • (xBar - xL)‖ ^ (2 : ℕ) := by rw [hgL]
          _ = (((L : ℝ) * ‖xBar - xL‖) : ℝ) ^ (2 : ℕ) := by
                rw [norm_smul, Real.norm_eq_abs, abs_of_pos hL_pos]
          _ = (L : ℝ) ^ (2 : ℕ) * ‖xBar - xL‖ ^ (2 : ℕ) := by ring
      have hquad :
          (1 / (L : ℝ)) * ‖gL‖ ^ (2 : ℕ) =
            (L : ℝ) / 2 * ‖xBar - xL‖ ^ (2 : ℕ) +
              (1 / (2 * (L : ℝ))) * ‖gL‖ ^ (2 : ℕ) := by
        rw [hgnorm]
        field_simp [hL_pos.ne']
        ring
      have hshift' :
          shiftedObjective t xL + inner ℝ gL (x - xL) =
            quadraticallyRegularizedObjective (shiftedObjective t) (L : ℝ) xBar xL +
              inner ℝ gL (x - xBar) +
                (1 / (2 * (L : ℝ))) * ‖gL‖ ^ (2 : ℕ) := by
        rw [hdecomp, inner_add_right, hg_inner, quadraticallyRegularizedObjective_apply,
          norm_sub_rev]
        linarith [hquad]
      have hμ_term_nonneg : 0 ≤ (μ / 2) * ‖x - xL‖ ^ (2 : ℕ) := by
        have hμ_nonneg : 0 ≤ μ / 2 := by
          nlinarith [hf'.mu_pos]
        exact mul_nonneg hμ_nonneg (by positivity)
      linarith [hstrong', hμ_term_nonneg, hshift']
    have hlower :
        ∀ x ∈ (Set.univ : Set E),
          shiftedObjective t x ≥
            modelValue t xBar (L : ℝ) +
              inner ℝ gL (x - xBar) +
                (1 / (2 * (L : ℝ))) * ‖gL‖ ^ (2 : ℕ) := by
      intro x _
      rw [hvalue_L_eq]
      exact hlower_aux x
    have hcomparison :
        modelValue t xBar μ ≥
          modelValue t xBar (L : ℝ) +
            ((μ - (L : ℝ)) / (2 * (L : ℝ) * μ)) * ‖gL‖ ^ (2 : ℕ) := by
      change
        (modelOptimalValue t xBar μ).toReal ≥
          (modelOptimalValue t xBar (L : ℝ)).toReal +
            ((μ - (L : ℝ)) / (2 * (L : ℝ) * μ)) * ‖gL‖ ^ (2 : ℕ)
      simpa [SetConstrainedMinimizationProblem.unconstrained] using
        exactValue_ge_of_lowerQuadraticModel
          Set.univ
          (shiftedFamily t)
          xBar
          Set.univ_nonempty
          (L : ℝ)
          μ
          gL
          hL_pos
          hf'.mu_pos
          (by
            intro x hx
            change shiftedFamily t xBar x ≥
              (modelOptimalValue t xBar (L : ℝ)).toReal +
                inner ℝ gL (x - xBar) +
                  (1 / (2 * (L : ℝ))) * ‖gL‖ ^ (2 : ℕ)
            simpa using hlower x hx)
    calc
      modelValue t xBar μ ≥
          modelValue t xBar (L : ℝ) +
            ((μ - (L : ℝ)) / (2 * (L : ℝ) * μ)) * ‖gL‖ ^ (2 : ℕ) :=
        hcomparison
      _ = modelValue t xBar (L : ℝ) -
          (((L : ℝ) - μ) / (2 * μ * (L : ℝ))) * ‖gL‖ ^ (2 : ℕ) := by
            ring

end SourceFacing

end

end
