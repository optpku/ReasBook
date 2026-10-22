/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_15
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Proposition_4_1_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_12
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_2_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient CubicRegularizationModelNotation ConstrainedArgmin StrongConvex

noncomputable section

universe u

variable {E : Type u}

/- Text 4.2.11 lies in the whole-space cubic-regularization / strong-convexity quadratic-rate
domain on real Hilbert spaces.

Sampled owner-style declarations:
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model minimized by the step;
* `cubicRegularizationQuadraticApproximation_apply` in `Definition_4_1_3`, the owner expansion of
  that cubic model;
* `CubicRegularizationMapping` in `Definition_4_2_12`, the chapter owner for a chosen cubic-step
  map together with its minimizing property;
* `HasLipschitzContinuousHessian` / `f ∈ C22[L3]` in `Definition_4_2_7`, the canonical whole-space
  Hessian-Lipschitz owner;
* `StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn` in `Proposition_4_1_4`, the
  canonical Polyak-type gap bound used in the proof sketch.

Best owner abstraction:
* source-facing: the quadratic-decrease region from Text 4.2.11 and its invariance estimate;
* core/canonical: `CubicRegularizationMapping f (L3 : ℝ)`,
  `cubicRegularizationQuadraticApproximation f (L3 : ℝ) x`,
  `StrongConvexOn Set.univ σ f`, and `f ∈ C22[L3]`;
* bridge/view: the pointwise minimizing relation `step.isMinOn_apply x` for a chosen cubic-step
  owner, or a single trial point `T` satisfying the same owner relation.

Primitive data:
* the objective `f`;
* the strong-convexity modulus `σ`;
* the Hessian-Lipschitz constant `L3`;
* the global minimizer witness `IsMinOn f Set.univ xStar`;
* for the one-step gap lemmas, a cubic-model minimizing witness
  `IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T`;
* for the region invariance theorem, the chosen step owner
  `CubicRegularizationMapping f (L3 : ℝ)`.

Derived API:
* the displayed cubic model itself, reused directly from `Definition_4_1_3`;
* the whole-space `C22[L3]` smoothness owner instead of repeating `ContDiff` and a raw Hessian
  Lipschitz predicate;
* the quadratic-decrease region and its invariance theorem.

This refinement removes the duplicate local wrapper `cubicStepObjective`, rewrites the theorem
surface directly on the chapter owners `m[f; (L3 : ℝ)](x)` and `C22[L3]`, and replaces the raw
pair `(stepMap, hstep)` by the existing owner `CubicRegularizationMapping f (L3 : ℝ)`. The
quadratic-decrease region remains the source-facing declaration owned by this file. -/

section CubicRegularization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Text 4.2.11 uses the existing Chapter 4 cubic-model owner and its expansion directly; this file
keeps no parallel local copy. -/
recall cubicRegularizationQuadraticApproximation
recall cubicRegularizationQuadraticApproximation_apply

end CubicRegularization

/-- The sublevel set on which the cubic-Newton gap estimate has coefficient at most `1`. It is
written in the multiplication form `2 L₃² (f x - f xStar) ≤ σ³`, which avoids division-by-zero
artifacts when `L₃ = 0`. -/
def cubicNewtonQuadraticDecreaseRegion
    (f : E → ℝ) (xStar : E) (σ : ℝ) (L3 : NNReal) : Set E :=
  {x | (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ ^ (3 : ℕ)}

-- Proof sketch: unfold `cubicNewtonQuadraticDecreaseRegion`.
/-- Membership in `cubicNewtonQuadraticDecreaseRegion f xStar σ L3` is exactly the displayed
sublevel inequality `2 L₃² (f x - f xStar) ≤ σ³`. -/
theorem mem_cubicNewtonQuadraticDecreaseRegion
    {f : E → ℝ} {xStar x : E} {σ : ℝ} {L3 : NNReal} :
    x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 ↔
      (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * (f x - f xStar) ≤ σ ^ (3 : ℕ) :=
  Iff.rfl

section CubicRegularization

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Helper for Text 4 2 11: whole-space strong convexity forces the frozen Hessian at each base
point to dominate `σ • id`, hence every Hessian quadratic form is bounded below by
`σ ‖d‖²`. -/
lemma strong_convex_hessian_quadratic_lower_bound
    {f : E → ℝ} {σ : ℝ} (hσ : 0 < σ)
    (hf_strong : StrongConvexOn Set.univ σ f)
    (hf_C2 : ContDiff ℝ 2 f)
    (x d : E) :
    σ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x d) d := by
  -- Translate strong convexity into the Chapter 2 Loewner lower bound for the Hessian.
  have hbound :
      σ • (1 : E →L[ℝ] E) ≤ hessian f x := by
    have hiff :=
      (strongConvexOn_iff_hessian_lower_bound
        (E := E) (μ := σ) (Q := Set.univ) (f := f)
        hσ convex_univ
        (by simp)
        hf_C2.continuous.continuousOn
        (by simpa using hf_C2.contDiffOn)).1 hf_strong
    simpa using hiff x (by simp)
  -- Then read the operator inequality as the corresponding quadratic-form inequality.
  exact
    (hessian_loewner_lower_bound_iff_quadratic_form_lower_bound
      (E := E) (Q := Set.univ) (f := f) hσ
      (by simpa using hf_C2.contDiffOn) (x := x) (by simp)).1 hbound d

-- Route correction: this file only needs the cubic-model stationarity pairing, so we reconstruct
-- that pairing directly from the owner model expansion instead of importing the currently broken
-- `Text_4_2_8` module.
/-- Helper for Text 4 2 11: pairing first-order optimality of a cubic-model minimizer with the
displacement `T - x` rewrites the linear Taylor term in terms of the Hessian quadratic form and
the cubic penalty. -/
lemma cubic_model_stationarity_pairing_at_minimizer
    {f : E → ℝ} {M : ℝ} {x T : E}
    (hT : IsMinOn (m[f; M](x)) Set.univ T) :
    -inner ℝ (∇ f x) (T - x) =
      inner ℝ (hessian f x (T - x)) (T - x) +
        ((M / 2 : ℝ) * ‖T - x‖ ^ (3 : ℕ)) := by
  let d : E := T - x
  have hstationary_inner :
      inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
        ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) = 0 := by
    have hlineMin :
        IsLocalMin (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) 1 := by
      -- The affine slice reaches the cubic-model minimizer at the parameter `1`.
      have hlocal : IsLocalMin (m[f; M](x)) T :=
        hT.isLocalMin (by simp)
      have hlocal1 : IsLocalMin (m[f; M](x)) (x + (1 : ℝ) • d) := by
        simpa [d, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hlocal
      have hline : ContinuousAt (fun t : ℝ ↦ x + t • d) 1 := by
        simpa [one_smul] using
          (HasDerivAt.const_add x
            ((hasDerivAt_id (1 : ℝ)).smul_const d)).continuousAt
      change IsLocalMin (((m[f; M](x)) ∘ fun t : ℝ ↦ x + t • d)) 1
      exact hlocal1.comp_continuous (g := fun t : ℝ ↦ x + t • d) (b := 1) hline
    have hmodel :
        HasDerivAt
          (fun t : ℝ ↦ (m[f; M](x)) (x + t • d))
          (inner ℝ (∇ f x) d + inner ℝ (hessian f x d) d +
            (M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
          1 := by
      have hslice :
          (fun t : ℝ ↦ (m[f; M](x)) (x + t • d)) =
            fun t : ℝ ↦
              f x +
                inner ℝ (∇ f x) d * t +
                ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ) +
                (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ) := by
        -- Expanding the cubic model on the affine slice produces a scalar cubic polynomial.
        funext t
        rw [cubicRegularizationQuadraticApproximation_apply, secondOrderTaylorModelAt_apply]
        have hdisp : x + t • d - x = t • d := by
          simp [sub_eq_add_neg, add_assoc]
        rw [hdisp, norm_smul, mul_pow]
        simp [inner_smul_right, inner_smul_left, mul_assoc]
        ring
      rw [hslice]
      have hlin :
          HasDerivAt (fun t : ℝ ↦ inner ℝ (∇ f x) d * t) (inner ℝ (∇ f x) d) 1 := by
        -- Differentiate the linear Taylor term along the line.
        simpa using (HasDerivAt.const_mul (inner ℝ (∇ f x) d) (hasDerivAt_id (1 : ℝ)))
      have hquad :
          HasDerivAt
            (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
            (inner ℝ (hessian f x d) d)
            1 := by
        -- Differentiate the quadratic Taylor term and evaluate at `t = 1`.
        have hquadBase :
            HasDerivAt
              (fun t : ℝ ↦ ((inner ℝ (hessian f x d) d) / 2 : ℝ) * t ^ (2 : ℕ))
              ((((inner ℝ (hessian f x d) d) / 2 : ℝ) * (2 * 1)) : ℝ)
              1 := by
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
            (HasDerivAt.const_mul (((inner ℝ (hessian f x d) d) / 2 : ℝ))
              ((hasDerivAt_id (1 : ℝ)).pow 2))
        convert hquadBase using 1
        ring
      have habsCube :
          HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℕ)) (3 : ℝ) 1 := by
        -- Near the positive point `1`, the cubic penalty reduces to the ordinary cubic.
        convert
          (hasDerivAt_abs_rpow (1 : ℝ) (by norm_num) :
            HasDerivAt (fun t : ℝ ↦ |t| ^ (3 : ℝ)) _ 1) using 1
        · ext t
          rw [show (3 : ℝ) = (3 : ℕ) by norm_num, Real.rpow_natCast]
        · norm_num
      have hcubic :
          HasDerivAt
            (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
            ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ))
            1 := by
        -- Differentiate the cubic regularization penalty and simplify the coefficient.
        have hbase :
            HasDerivAt
              (fun t : ℝ ↦ (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * |t| ^ (3 : ℕ))
              ((((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) * 3)
              1 := by
          simpa [mul_comm, mul_left_comm, mul_assoc] using
            (HasDerivAt.const_mul (((M / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) : ℝ) habsCube)
        convert hbase using 1
        ring
      -- Summing the differentiated model terms yields the scalar stationarity identity.
      simpa [add_assoc, add_left_comm, add_comm] using
        (HasDerivAt.const_add (f x) (hlin.add hquad |>.add hcubic))
    exact hlineMin.hasDerivAt_eq_zero hmodel
  have hlinear :
      -inner ℝ (∇ f x) d =
        inner ℝ (hessian f x d) d + ((M / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Solve the scalar stationarity equation for the linear term.
    linarith
  simpa [d] using hlinear

-- Proof sketch: compare `f T` with the cubic model value at `T`, rewrite the model gap using the
-- cubic first-order optimality condition, and then use the strong-convexity Hessian lower bound.
/-- Helper for Text 4 2 11: a cubic-step minimizer yields an objective decrease at least
`(σ / 2) ‖x - T‖²`. -/
lemma cubic_step_objective_drop_ge_strong_convex_quadratic
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {x T : E}
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    (σ / 2 : ℝ) * ‖x - T‖ ^ (2 : ℕ) ≤ f x - f T := by
  let d : E := T - x
  have hHL : HessianLipschitzOn L3 Set.univ f :=
    hf.toHessianLipschitzOn isOpen_univ convex_univ
  have htrial_le_model : f T ≤ m[f; (L3 : ℝ)](x; T) := by
    -- The global Hessian-Lipschitz owner controls the true objective by the cubic model.
    exact
      objective_le_cubicRegularizationQuadraticApproximation_of_mem_of_le_hessianLipschitz
        (𝓕 := Set.univ) (f := f) (L := L3) (M := (L3 : ℝ))
        (x := x) (y := T)
        (hf := hHL)
        (by simp) (by simp) le_rfl
  have hquad_lower :
      σ * ‖d‖ ^ (2 : ℕ) ≤ inner ℝ (hessian f x d) d :=
    strong_convex_hessian_quadratic_lower_bound hσ hf_strong hf.contDiff x d
  have hlinear :
      -inner ℝ (∇ f x) d =
        inner ℝ (hessian f x d) d + (((L3 : ℝ) / 2 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Re-express the linear Taylor term through the paired cubic-model stationarity identity.
    simpa [d] using
      cubic_model_stationarity_pairing_at_minimizer
        (f := f) (M := (L3 : ℝ)) (x := x) (T := T) hT
  have htrial_le_model_expanded :
      f T ≤
        f x + inner ℝ (∇ f x) d + (1 / 2 : ℝ) * inner ℝ (hessian f x d) d +
          (((L3 : ℝ) / 6 : ℝ) * ‖d‖ ^ (3 : ℕ)) := by
    -- Expanding the cubic model isolates the Hessian and cubic-penalty contributions.
    rw [
      cubicRegularizationQuadraticApproximation_apply,
      secondOrderTaylorModelAt_apply
    ] at htrial_le_model
    simpa [d, add_assoc, add_left_comm, add_comm] using htrial_le_model
  have hcube_nonneg : 0 ≤ ((L3 : ℝ) / 3 : ℝ) * ‖d‖ ^ (3 : ℕ) := by
    positivity
  have hmodel_gap :
      (1 / 2 : ℝ) * inner ℝ (hessian f x d) d + (((L3 : ℝ) / 3 : ℝ) * ‖d‖ ^ (3 : ℕ)) ≤
        f x - f T := by
    -- Substituting the stationarity identity rewrites the model upper bound as a gap lower bound.
    linarith [htrial_le_model_expanded, hlinear]
  -- The objective is below the model, and the model gap dominates the strong-convexity term.
  have hdrop_d : (σ / 2 : ℝ) * ‖d‖ ^ (2 : ℕ) ≤ f x - f T := by
    linarith [hmodel_gap, hquad_lower, hcube_nonneg]
  simpa [d, norm_sub_rev] using hdrop_d

-- Proof sketch: combine the cubic-step gradient estimate
-- `‖∇ f T‖ ≤ L₃ ‖T - x‖²` with the previous quadratic lower bound on `f x - f T`.
/-- Helper for Text 4 2 11: the gradient at a cubic-step minimizer is controlled linearly by the
one-step objective decrease. -/
lemma cubic_step_gradient_norm_le_linear_objective_drop
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {x T : E}
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    ‖∇ f T‖ ≤ (((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T) := by
  have hHL : HessianLipschitzOn L3 Set.univ f :=
    hf.toHessianLipschitzOn isOpen_univ convex_univ
  have hgrad_bound_raw :=
    gradient_norm_le_of_isMinOn_cubicRegularizationQuadraticApproximation
      (f := f) (𝓕 := Set.univ) (L := L3) (M := (L3 : ℝ))
      (x := x) (y := T)
      (hf := hHL)
      (by positivity) hT (by simp) (by simp)
  have hgrad_bound : ‖∇ f T‖ ≤ (L3 : ℝ) * ‖T - x‖ ^ (2 : ℕ) := by
    have hcoeff : (((L3 : ℝ) + (L3 : ℝ)) / 2 : ℝ) = (L3 : ℝ) := by ring
    simpa [hcoeff] using hgrad_bound_raw
  have hdrop :=
    cubic_step_objective_drop_ge_strong_convex_quadratic hσ hf hf_strong hT
  have hdrop' : (σ / 2 : ℝ) * ‖T - x‖ ^ (2 : ℕ) ≤ f x - f T := by
    simpa [norm_sub_rev] using hdrop
  have hscaled : σ * ‖T - x‖ ^ (2 : ℕ) ≤ (2 : ℝ) * (f x - f T) := by
    linarith
  have hnorm_sq_le' :
      ‖T - x‖ ^ (2 : ℕ) ≤ ((2 : ℝ) * (f x - f T)) / σ := by
    exact (le_div_iff₀ hσ).2 (by simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled)
  have hnorm_sq_le :
      ‖T - x‖ ^ (2 : ℕ) ≤ ((2 : ℝ) / σ) * (f x - f T) := by
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hnorm_sq_le'
  -- Substitute the quadratic radius bound into the gradient estimate.
  calc
    ‖∇ f T‖ ≤ (L3 : ℝ) * ‖T - x‖ ^ (2 : ℕ) := hgrad_bound
    _ ≤ (L3 : ℝ) * (((2 : ℝ) / σ) * (f x - f T)) := by
      exact mul_le_mul_of_nonneg_left hnorm_sq_le (by positivity)
    _ = (((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T) := by ring

-- Proof sketch: combine strong convexity with the Polyak-type estimate
-- `f T - f xStar ≤ (1 / (2 * σ)) ‖∇ f T‖²`, apply Text 4.2.8 (1) with `M = L₃` to bound
-- `‖∇ f T‖` by `L₃ ‖x - T‖²`, and then use Text 4.2.8 (2) with `M = L₃` to convert
-- `‖x - T‖²` into the objective drop `f x - f T`.
/-- For a cubic-step minimizer `T`, the next optimality gap is bounded by the square of the
current one-step objective decrease. -/
theorem cubicStep_gap_le_square_of_objective_drop
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar x T : E} (hxStar : IsMinOn f Set.univ xStar)
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    f T - f xStar ≤
      ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f T) ^ (2 : ℕ) := by
  have hstrong_class : f ∈ 𝓛^1[σ] := by
    exact mem_strongConvexClass_iff.mpr ⟨hσ, hf_strong⟩
  let hf_C1 : ContDiff ℝ 1 f := hf.contDiff.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)
  have hdiff : Differentiable ℝ f := fun y ↦ hf_C1.differentiable_one y
  have hxStar_argmin : xStar ∈ argmin[Set.univ] f := by
    exact mem_constrainedArgmin_iff.mpr ⟨by simp, hxStar⟩
  have hpolyak :
      f T - f xStar ≤ (1 / (2 * σ)) * ‖∇ f T‖ ^ (2 : ℕ) :=
    StrongConvexOn.sub_le_inv_two_mul_norm_gradient_sq_of_isMinOn
      (f := f) (μ := σ) hstrong_class hdiff hxStar_argmin
  have hgrad_linear :=
    cubic_step_gradient_norm_le_linear_objective_drop hσ hf hf_strong hT
  have hdrop_nonneg : 0 ≤ f x - f T := by
    have hdrop :=
      cubic_step_objective_drop_ge_strong_convex_quadratic hσ hf hf_strong hT
    have hleft_nonneg : 0 ≤ (σ / 2 : ℝ) * ‖x - T‖ ^ (2 : ℕ) := by
      positivity
    linarith
  have hcoef_nonneg : 0 ≤ (((2 : ℝ) * (L3 : ℝ)) / σ) := by
    positivity
  have hgrad_sq :
      ‖∇ f T‖ ^ (2 : ℕ) ≤
        ((((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T)) ^ (2 : ℕ) := by
    have hrhs_nonneg : 0 ≤ (((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T) := by
      positivity
    exact
      (sq_le_sq).2 <| by
        rw [abs_of_nonneg (norm_nonneg _), abs_of_nonneg hrhs_nonneg]
        exact hgrad_linear
  have hmain :
      f T - f xStar ≤
        (1 / (2 * σ)) * ((((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T)) ^ (2 : ℕ) := by
    calc
      f T - f xStar ≤ (1 / (2 * σ)) * ‖∇ f T‖ ^ (2 : ℕ) := hpolyak
      _ ≤ (1 / (2 * σ)) *
            ((((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T)) ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hgrad_sq (by positivity)
  -- Expand the squared linear bound into the displayed quadratic coefficient.
  have hcoeff :
      (1 / (2 * σ)) * ((((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T)) ^ (2 : ℕ) =
        ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f T) ^ (2 : ℕ) := by
    field_simp [hσ.ne']
  calc
    f T - f xStar ≤
        (1 / (2 * σ)) * ((((2 : ℝ) * (L3 : ℝ)) / σ) * (f x - f T)) ^ (2 : ℕ) := hmain
    _ = ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f T) ^ (2 : ℕ) := hcoeff

-- Proof sketch: apply `cubicStep_gap_le_square_of_objective_drop`, then use
-- `f xStar ≤ f T` from `hxStar` to get `f x - f T ≤ f x - f xStar`.
/-- For a cubic-step minimizer `T`, the next optimality gap is bounded by a quadratic function of
the current optimality gap. -/
theorem cubicStep_gap_le_square_of_current_gap
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar x T : E} (hxStar : IsMinOn f Set.univ xStar)
    (hT : IsMinOn (m[f; (L3 : ℝ)](x)) Set.univ T) :
    f T - f xStar ≤
      ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := by
  have hstep :=
    cubicStep_gap_le_square_of_objective_drop hσ hf hf_strong hxStar hT
  have hxStar_le_T : f xStar ≤ f T := hxStar (by simp)
  have hdrop_le_gap : f x - f T ≤ f x - f xStar := by
    linarith
  have hdrop_nonneg : 0 ≤ f x - f T := by
    have hdrop :=
      cubic_step_objective_drop_ge_strong_convex_quadratic hσ hf hf_strong hT
    have hleft_nonneg : 0 ≤ (σ / 2 : ℝ) * ‖x - T‖ ^ (2 : ℕ) := by
      positivity
    linarith
  have hsquare_le :
      (f x - f T) ^ (2 : ℕ) ≤ (f x - f xStar) ^ (2 : ℕ) := by
    nlinarith
  have hcoeff_nonneg :
      0 ≤ ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) := by
    positivity
  -- Replace the one-step drop by the larger current optimality gap.
  calc
    f T - f xStar ≤
        ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f T) ^ (2 : ℕ) := hstep
    _ ≤ ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := by
      exact mul_le_mul_of_nonneg_left hsquare_le hcoeff_nonneg

-- Proof sketch: for `x` in the displayed set, the defining inequality gives
-- `((2 * L₃²) / σ³) * (f x - f xStar) ≤ 1`. Combine this with
-- `cubicStep_gap_le_square_of_current_gap` to show
-- `f (step x) - f xStar ≤ f x - f xStar`, then rewrite the latter inequality back as
-- membership in `cubicNewtonQuadraticDecreaseRegion f xStar σ L3`.
/-- Text 4 2 11: if `f ∈ C22[L3]` is `σ`-strongly convex and `step` is a cubic regularization
mapping with parameter `L₃`, then
`f (step x) - f xStar ≤ (2 L₃² / σ³) (f x - f (step x))² ≤ (2 L₃² / σ³) (f x - f xStar)²`; in
particular, the sublevel set `{x | 2 L₃² (f x - f xStar) ≤ σ³}` is invariant and is a region of
quadratic decrease for `step`. -/
theorem cubicNewton_quadraticDecreaseRegion
    {f : E → ℝ} {σ : ℝ} {L3 : NNReal} (hσ : 0 < σ)
    (hf : f ∈ C22[L3])
    (hf_strong : StrongConvexOn Set.univ σ f)
    {xStar : E} (hxStar : IsMinOn f Set.univ xStar)
    (step : CubicRegularizationMapping f (L3 : ℝ))
    {x : E} (hx : x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3) :
    step x ∈ cubicNewtonQuadraticDecreaseRegion f xStar σ L3 ∧
      f (step x) - f xStar ≤
        ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ)) * (f x - f xStar) ^ (2 : ℕ) := by
  let gap : ℝ := f x - f xStar
  let nextGap : ℝ := f (step x) - f xStar
  let coeff : ℝ := ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) / σ ^ (3 : ℕ))
  have hx_ineq :
      (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * gap ≤ σ ^ (3 : ℕ) := by
    simpa [gap] using (mem_cubicNewtonQuadraticDecreaseRegion.mp hx)
  have hgap_nonneg : 0 ≤ gap := by
    have hxStar_le_x : f xStar ≤ f x := hxStar (by simp)
    linarith [hxStar_le_x]
  have hnext :=
    cubicStep_gap_le_square_of_current_gap hσ hf hf_strong hxStar (step.isMinOn_apply x)
  have hnext' : nextGap ≤ coeff * gap ^ (2 : ℕ) := by
    simpa [gap, nextGap, coeff] using hnext
  have hσcube_pos : 0 < σ ^ (3 : ℕ) := by
    positivity
  have hcoeff_gap_le_one : coeff * gap ≤ 1 := by
    have hdiv :
        ((2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * gap) / σ ^ (3 : ℕ) ≤ 1 := by
      exact (div_le_iff₀ hσcube_pos).2 (by simpa using hx_ineq)
    simpa [coeff, gap, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hnext_le_gap : nextGap ≤ gap := by
    calc
      nextGap ≤ coeff * gap ^ (2 : ℕ) := hnext'
      _ = gap * (coeff * gap) := by
        simp [gap, coeff]
        ring
      _ ≤ gap * 1 := by
        gcongr
      _ = gap := by ring
  have hfactor_nonneg : 0 ≤ (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) := by
    positivity
  have hregion_ineq :
      (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * nextGap ≤ σ ^ (3 : ℕ) := by
    have hmul :
        (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * nextGap ≤
          (2 : ℝ) * (L3 : ℝ) ^ (2 : ℕ) * gap := by
      exact mul_le_mul_of_nonneg_left hnext_le_gap hfactor_nonneg
    exact le_trans hmul hx_ineq
  -- The quantitative estimate gives the new gap, and the region inequality follows from
  -- `nextGap ≤ gap` together with the defining inequality of the current region.
  refine ⟨?_, ?_⟩
  · simpa [nextGap] using (mem_cubicNewtonQuadraticDecreaseRegion.mpr hregion_ineq)
  · simpa [gap, nextGap, coeff] using hnext

end CubicRegularization
