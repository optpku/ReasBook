/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Algorithm_4_1_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Lemma_4_1_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped CubicRegularizationResidual Gradient

noncomputable section

universe u

/- Lemma 4.1.8 lies in the chapter cubic-regularization / gradient-`3/2` descent domain.

Sampled owner declarations:
* `CubicRegularizationMethod` in `Algorithm_4_1_5`, the source-facing owner for the iterate and
  regularization sequences;
* `cubicRegularizationResidual` in `Lemma_4_1_5`, with notation `r[trialPoint] x`;
* `objective_sub_cubicRegularizationValue_ge_residual_cube` in `Lemma_4_1_5`, the owner-level
  descent estimate for a minimizing cubic trial point;
* `CubicRegularizationMethod.L0_le_regularization` and
  `CubicRegularizationMethod.regularization_le_two_mul_L` in `Algorithm_4_1_5`, the canonical
  bounds `L₀ ≤ M_k ≤ 2L`.

Source/core/bridge triage:
* source-facing: the textbook gradient-`3/2` lower bound for one cubic-regularization step;
* core/canonical: `CubicRegularizationMethod`, `cubicRegularizationValue`, and the residual owner
  `r[trialPoint]`;
* bridge/view: transport the owner-level residual-cube decrease estimate to the trajectory and
  combine it with the residual lower bound in terms of `‖∇ f(x_{k+1})‖`.

Primitive data:
* a cubic-regularization method `method`, whose owner data already supplies the minimizing cubic
  trial point at each step;
* a chosen step index `k`;
* the residual lower bound at the accepted step `k`.

Derived API:
* the objective-drop lower bound by `‖∇ f(x_{k+1})‖^(3/2)`.

The previous file duplicated the chapter owner data by taking separate sequences `x`, `M`, and an
arbitrary residual function together with standalone bounds `L₀ ≤ M_k ≤ 2L`. This refinement
reuses the canonical method owner and the canonical residual owner directly, and treats the
residual-cube objective drop as derived API rather than primitive input. -/

section CubicRegularizationGradientThreeHalvesDrop

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable {f : E → ℝ} {stepMap : ℝ → E → E} {L0 L : ℝ} {x0 : E}

namespace CubicRegularizationMethod

/-- Helper for Lemma 4.1.8: the accepted trial point inherits the residual-cube objective drop
from the cubic-model minimizing inequality. -/
lemma objective_sub_acceptedTrialPoint_ge_regularization_mul_residual_cube
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 L x0)
    (k : ℕ) :
    f (method k) - f (method.acceptedTrialPoint k) ≥
      ((method.regularization k) / 12 : ℝ) * r[method.acceptedTrialPoint k] (method k) ^ (3 : ℕ) := by
  let modelValue :=
    EReal.toReal
      (SetConstrainedMinimizationProblem.optimalValue
        (cubicRegularizationProblem f (method.regularization k) (method k)))
  -- First rewrite the owner-level cubic decrease estimate at the accepted trial point.
  have hmodel :
      f (method k) - modelValue ≥
        ((method.regularization k) / 12 : ℝ) * r[method.acceptedTrialPoint k] (method k) ^ (3 : ℕ) := by
    simpa [CubicRegularizationMethod.acceptedTrialPoint, modelValue] using
      objective_sub_cubicRegularizationValue_ge_residual_cube
        (f := f)
        (M := method.regularization k)
        (x := method k)
        (trialPoint := method.acceptedTrialPoint k)
        (method.regularization_pos k).le
        (by
          simpa [CubicRegularizationMethod.acceptedTrialPoint] using method.step_isMinOn k)
  -- Then replace the model value by the actual accepted objective value.
  have haccept : f (method.acceptedTrialPoint k) ≤ modelValue := by
    simpa [CubicRegularizationMethod.acceptedTrialPoint, modelValue] using method.objective_step_le_value k
  have hdrop :
      f (method k) - modelValue ≤ f (method k) - f (method.acceptedTrialPoint k) := by
    simpa [modelValue] using sub_le_sub_left haccept (f (method k))
  exact le_trans hmodel hdrop

/-- Helper for Lemma 4.1.8: cubing the residual square-root lower bound produces the canonical
`‖∇ f‖^(3/2)` factor. -/
lemma sqrt_drop_factor_eq_gradient_norm_rpow_threeHalves
    {M g L : ℝ}
    (hg : 0 ≤ g)
    (hLM : 0 < L + M) :
    ((M / 12 : ℝ) * (Real.sqrt (2 * g / (L + M))) ^ (3 : ℕ)) =
      (M / (3 * Real.sqrt 2 * Real.rpow (L + M) (3 / 2 : ℝ)) : ℝ) *
        Real.rpow g (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow]
  have hdiv_nonneg : 0 ≤ 2 * g / (L + M) := by
    exact div_nonneg (by nlinarith) hLM.le
  -- Collapse the cubic power of the square root into a single `3 / 2` exponent.
  rw [show ((2 * g / (L + M)) ^ (1 / 2 : ℝ)) ^ (3 : ℕ) = (2 * g / (L + M)) ^ (3 / 2 : ℝ) by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hdiv_nonneg]
    norm_num]
  rw [Real.div_rpow (by nlinarith) hLM.le, Real.mul_rpow (by norm_num) hg]
  have htwo : (2 : ℝ) ^ (3 / 2 : ℝ) = 2 * Real.sqrt 2 := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num]
    rw [Real.rpow_add (by norm_num : 0 < (2 : ℝ)), Real.sqrt_eq_rpow]
    norm_num [Real.rpow_natCast]
  rw [htwo]
  have hsqrt2_ne : Real.sqrt 2 ≠ 0 := by
    positivity
  have hrpow_ne : Real.rpow (L + M) (3 / 2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hLM _)
  -- Clearing the positive denominators leaves a purely scalar identity.
  field_simp [hsqrt2_ne, hrpow_ne]
  rw [Real.sq_sqrt (by norm_num : 0 ≤ (2 : ℝ))]
  ring_nf
  simp [mul_comm, mul_left_comm, mul_assoc]

/-- Helper for Lemma 4.1.8: on the admissible interval `L₀ ≤ M ≤ 2L`, the scalar coefficient
`M / (L + M)^(3/2)` is bounded below by its value at `L₀`. -/
lemma regularization_ratio_lower_bound
    {M L0 L : ℝ}
    (hL0 : 0 < L0)
    (hL0M : L0 ≤ M)
    (hM : M ≤ 2 * L) :
    L0 / Real.rpow (L + L0) (3 / 2 : ℝ) ≤ M / Real.rpow (L + M) (3 / 2 : ℝ) := by
  have hL_pos : 0 < L := by
    linarith
  have hLM0_pos : 0 < L + L0 := by
    linarith
  have hLM_pos : 0 < L + M := by
    linarith
  have hleft_nonneg : 0 ≤ L0 / Real.rpow (L + L0) (3 / 2 : ℝ) := by
    exact div_nonneg hL0.le (Real.rpow_nonneg hLM0_pos.le _)
  have hright_nonneg : 0 ≤ M / Real.rpow (L + M) (3 / 2 : ℝ) := by
    have hM_nonneg : 0 ≤ M := le_trans hL0.le hL0M
    exact div_nonneg hM_nonneg (Real.rpow_nonneg hLM_pos.le _)
  apply (sq_le_sq₀ hleft_nonneg hright_nonneg).1
  have hpoly : L0 ^ (2 : ℕ) * (L + M) ^ (3 : ℕ) ≤ M ^ (2 : ℕ) * (L + L0) ^ (3 : ℕ) := by
    have h_ab_le_Lsum : L0 * M ≤ L * (L0 + M) := by
      have h1 : L0 * M ≤ 2 * L * L0 := by
        nlinarith
      have h2 : 2 * L * L0 ≤ L * (L0 + M) := by
        have : 2 * L0 ≤ L0 + M := by
          linarith
        nlinarith [hL_pos]
      exact h1.trans h2
    have h_ab_le_fourL2 : L0 * M ≤ 4 * L ^ (2 : ℕ) := by
      have h1 : L0 * M ≤ M ^ (2 : ℕ) := by
        nlinarith
      have h2 : M ^ (2 : ℕ) ≤ 4 * L ^ (2 : ℕ) := by
        nlinarith
      exact h1.trans h2
    have hfactor_nonneg :
        0 ≤ L ^ (3 : ℕ) * (L0 + M) + 3 * L ^ (2 : ℕ) * L0 * M - L0 ^ (2 : ℕ) * M ^ (2 : ℕ) := by
      have hterm1 : 0 ≤ L ^ (2 : ℕ) * (L * (L0 + M) - L0 * M) := by
        exact mul_nonneg (sq_nonneg L) (sub_nonneg.mpr h_ab_le_Lsum)
      have hterm2 : 0 ≤ L0 * M * (4 * L ^ (2 : ℕ) - L0 * M) := by
        have hLM_nonneg : 0 ≤ L0 * M := mul_nonneg hL0.le (le_trans hL0.le hL0M)
        exact mul_nonneg hLM_nonneg (sub_nonneg.mpr h_ab_le_fourL2)
      have hEq :
          L ^ (3 : ℕ) * (L0 + M) + 3 * L ^ (2 : ℕ) * L0 * M - L0 ^ (2 : ℕ) * M ^ (2 : ℕ) =
            L ^ (2 : ℕ) * (L * (L0 + M) - L0 * M) + L0 * M * (4 * L ^ (2 : ℕ) - L0 * M) := by
        ring
      rw [hEq]
      exact add_nonneg hterm1 hterm2
    -- After squaring, the coefficient difference factors by `M - L₀`.
    have hdiff : 0 ≤ M ^ (2 : ℕ) * (L + L0) ^ (3 : ℕ) - L0 ^ (2 : ℕ) * (L + M) ^ (3 : ℕ) := by
      have hba : 0 ≤ M - L0 := by
        linarith
      have hEq :
          M ^ (2 : ℕ) * (L + L0) ^ (3 : ℕ) - L0 ^ (2 : ℕ) * (L + M) ^ (3 : ℕ) =
            (M - L0) *
              (L ^ (3 : ℕ) * (L0 + M) + 3 * L ^ (2 : ℕ) * L0 * M - L0 ^ (2 : ℕ) * M ^ (2 : ℕ)) := by
        ring
      rw [hEq]
      exact mul_nonneg hba hfactor_nonneg
    linarith
  have hleft_sq :
      (L0 / Real.rpow (L + L0) (3 / 2 : ℝ)) ^ (2 : ℕ) =
        L0 ^ (2 : ℕ) / (L + L0) ^ (3 : ℕ) := by
    rw [div_pow]
    have hsq : (Real.rpow (L + L0) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + L0) ^ (3 : ℕ) := by
      calc
        (Real.rpow (L + L0) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + L0) ^ ((3 / 2 : ℝ) * 2) := by
          symm
          exact Real.rpow_mul_natCast hLM0_pos.le (3 / 2 : ℝ) 2
        _ = (L + L0) ^ (3 : ℕ) := by
          norm_num [Real.rpow_natCast]
    rw [hsq]
  have hright_sq :
      (M / Real.rpow (L + M) (3 / 2 : ℝ)) ^ (2 : ℕ) =
        M ^ (2 : ℕ) / (L + M) ^ (3 : ℕ) := by
    rw [div_pow]
    have hsq : (Real.rpow (L + M) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + M) ^ (3 : ℕ) := by
      calc
        (Real.rpow (L + M) (3 / 2 : ℝ)) ^ (2 : ℕ) = (L + M) ^ ((3 / 2 : ℝ) * 2) := by
          symm
          exact Real.rpow_mul_natCast hLM_pos.le (3 / 2 : ℝ) 2
        _ = (L + M) ^ (3 : ℕ) := by
          norm_num [Real.rpow_natCast]
    rw [hsq]
  rw [hleft_sq, hright_sq]
  exact
    (div_le_div_iff₀
      (show 0 < (L + L0) ^ (3 : ℕ) by positivity)
      (show 0 < (L + M) ^ (3 : ℕ) by positivity)).2 hpoly

-- Proof sketch: first combine the method acceptance inequality with
-- `objective_sub_cubicRegularizationValue_ge_residual_cube` to obtain
-- `f(x_k) - f(x_{k+1}) ≥ (M_k / 12) r_{M_k}(x_k)^3`. Then use the residual lower bound
-- `r_{M_k}(x_k) ≥ sqrt (2 ‖∇ f(x_{k+1})‖ / (L + M_k))` to rewrite the right-hand side as
-- `(M_k / (3 * sqrt 2 * (L + M_k)^(3/2))) * ‖∇ f(x_{k+1})‖^(3/2)`, and finally use the owner
-- bounds `L₀ ≤ M_k ≤ 2L` to replace that coefficient by its lower bound at `L₀`.
/-- Lemma 4.1.8: if a cubic-regularization method uses at step `k` a global minimizer of the
cubic model, and if the residual at that step satisfies
`r_{M_k}(x_k) ≥ sqrt (2 ‖∇ f(x_{k+1})‖ / (L + M_k))`, then the one-step objective drop obeys
the gradient-`3/2` lower bound
`f(x_k) - f(x_{k+1}) ≥ [L0 / (3 sqrt 2 (L + L0)^(3/2))] ‖∇ f(x_{k+1})‖^(3/2)`. -/
theorem objective_sub_succ_ge_gradient_norm_rpow_threeHalves
    (method :
      CubicRegularizationMethod
        f
        stepMap
        L0 L x0)
    (k : ℕ)
    (hresidual_lower :
      r[method.acceptedTrialPoint k] (method k) ≥
        Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) :
    f (method k) - f (method (k + 1)) ≥
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ) *
        Real.rpow ‖∇ f (method (k + 1))‖ (3 / 2 : ℝ) := by
  have hdrop :=
    objective_sub_acceptedTrialPoint_ge_regularization_mul_residual_cube method k
  have hreg_nonneg : 0 ≤ (method.regularization k / 12 : ℝ) := by
    linarith [method.regularization_pos k]
  have hsqrt_nonneg :
      0 ≤
        Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k)) :=
    Real.sqrt_nonneg _
  have hresidual_cube :
      (Real.sqrt
          (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) ^ (3 : ℕ) ≤
        r[method.acceptedTrialPoint k] (method k) ^ (3 : ℕ) := by
    -- Cube the residual lower bound on the nonnegative square-root branch.
    exact pow_le_pow_left₀ hsqrt_nonneg hresidual_lower 3
  have hsqrt_drop :
      ((method.regularization k / 12 : ℝ) *
          (Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) ^ (3 : ℕ)) ≤
        f (method k) - f (method.acceptedTrialPoint k) := by
    -- Scale the cubed residual estimate by the nonnegative regularization coefficient.
    have hscaled :=
      mul_le_mul_of_nonneg_left hresidual_cube hreg_nonneg
    exact le_trans hscaled hdrop
  have hLM_pos : 0 < L + method.regularization k := by
    linarith [method.L0_pos, method.L0_le_L, method.regularization_pos k]
  have hsqrt_rewrite :
      ((method.regularization k / 12 : ℝ) *
          (Real.sqrt
            (2 * ‖∇ f (method.acceptedTrialPoint k)‖ / (L + method.regularization k))) ^ (3 : ℕ)) =
        ((method.regularization k /
              (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) :=
    sqrt_drop_factor_eq_gradient_norm_rpow_threeHalves
      (g := ‖∇ f (method.acceptedTrialPoint k)‖)
      (M := method.regularization k)
      (L := L)
      (norm_nonneg _)
      hLM_pos
  have hgradient_drop :
      ((method.regularization k /
            (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) ≤
        f (method k) - f (method.acceptedTrialPoint k) := by
    rw [hsqrt_rewrite] at hsqrt_drop
    exact hsqrt_drop
  have hratio :
      L0 / Real.rpow (L + L0) (3 / 2 : ℝ) ≤
        method.regularization k / Real.rpow (L + method.regularization k) (3 / 2 : ℝ) :=
    regularization_ratio_lower_bound
      method.L0_pos
      (method.L0_le_regularization k)
      (method.regularization_le_two_mul_L k)
  have hscale_ratio :
      (L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ) ≤
        (method.regularization k /
            (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) := by
    -- The scalar coefficient is minimized by replacing `M_k` with the lower endpoint `L₀`.
    have hscale :=
      mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ 1 / (3 * Real.sqrt 2))
    simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hscale
  have hgrad_nonneg :
      0 ≤ Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ) :=
    Real.rpow_nonneg (norm_nonneg _) _
  have hfinal_coeff :
      ((L0 / (3 * Real.sqrt 2 * Real.rpow (L + L0) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) ≤
        ((method.regularization k /
              (3 * Real.sqrt 2 * Real.rpow (L + method.regularization k) (3 / 2 : ℝ)) : ℝ) *
          Real.rpow ‖∇ f (method.acceptedTrialPoint k)‖ (3 / 2 : ℝ)) := by
    exact mul_le_mul_of_nonneg_right hscale_ratio hgrad_nonneg
  -- Chaining the scalar lower bound with the owner-level descent estimate gives the target step.
  have hfinal :=
    le_trans hfinal_coeff hgradient_drop
  simpa [method.acceptedTrialPoint_eq_succ k] using hfinal

end CubicRegularizationMethod

end CubicRegularizationGradientThreeHalvesDrop

end
