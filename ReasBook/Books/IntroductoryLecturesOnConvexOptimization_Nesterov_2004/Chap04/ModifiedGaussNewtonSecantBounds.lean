/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_4_12

noncomputable section

open scoped ModifiedGaussNewtonStep.ModifiedGaussNewtonStepWholeSpaceNotation

universe u

variable {E₁ : Type u} [NormedAddCommGroup E₁]

/-- Helper for Proposition 4.4.6: evaluating the quadratic model with parameter `M` at a step
chosen for parameter `M₀` changes only the residual-square coefficient. -/
theorem quadraticallyRegularizedObjective_at_step_eq_modelValue_add_penalty_shift
    {ψ : E₁ → E₁ → ℝ} {M₀ : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M₀) (x : E₁) (M : ℝ) :
    quadraticallyRegularizedObjective (ψ x) M x (step.point x) =
      f[step](x) + ((M - M₀) / 2 : ℝ) * (r[step](x)) ^ (2 : ℕ) := by
  -- Expand the trial value and the attained model value at the same point, then collect the
  -- change in the quadratic coefficient.
  rw [quadraticallyRegularizedObjective_apply,
    ModifiedGaussNewtonStep.modelValueAtUniv_def,
    ModifiedGaussNewtonStep.residualAtUniv_def]
  ring

/-- Helper for Proposition 4.4.6: evaluating the quadratic model at a step with its own
regularization parameter recovers the textbook model value `f_M(x)`. -/
@[simp] theorem quadraticallyRegularizedObjective_at_step_eq_modelValue
    {ψ : E₁ → E₁ → ℝ} {M : ℝ}
    (step : ModifiedGaussNewtonStep ψ Set.univ M) (x : E₁) :
    quadraticallyRegularizedObjective (ψ x) M x (step.point x) = f[step](x) := by
  rw [quadraticallyRegularizedObjective_at_step_eq_modelValue_add_penalty_shift
    (step := step) (x := x) (M := M)]
  ring

/-- Helper for Proposition 4.4.6: comparing the endpoint owner values against the opposite
endpoint minimizers sandwiches the value-function increment between the two residual squares. -/
theorem modifiedGaussNewton_secant_bounds_of_steps
    {ψ : E₁ → E₁ → ℝ} {x : E₁} {M₁ M₂ : ℝ}
    (step₁ : ModifiedGaussNewtonStep ψ Set.univ M₁)
    (step₂ : ModifiedGaussNewtonStep ψ Set.univ M₂) :
    f[step₁](x) + ((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) ≤ f[step₂](x) ∧
      f[step₂](x) ≤
        f[step₁](x) + ((M₂ - M₁) / 2 : ℝ) * (r[step₁](x)) ^ (2 : ℕ) := by
  have hstep₁ :
      quadraticallyRegularizedObjective (ψ x) M₁ x (step₁.point x) ≤
        quadraticallyRegularizedObjective (ψ x) M₁ x (step₂.point x) :=
    (isMinOn_univ_iff.mp (step₁.isMinOn_point x)) (step₂.point x)
  have hstep₂ :
      quadraticallyRegularizedObjective (ψ x) M₂ x (step₂.point x) ≤
        quadraticallyRegularizedObjective (ψ x) M₂ x (step₁.point x) :=
    (isMinOn_univ_iff.mp (step₂.isMinOn_point x)) (step₁.point x)
  -- Rewriting the opposite-endpoint comparisons produces the two secant bounds directly.
  have hlower' :
      f[step₁](x) ≤
        f[step₂](x) + ((M₁ - M₂) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) := by
    rw [quadraticallyRegularizedObjective_at_step_eq_modelValue,
      quadraticallyRegularizedObjective_at_step_eq_modelValue_add_penalty_shift
        (step := step₂) (x := x) (M := M₁)] at hstep₁
    exact hstep₁
  have hupper :
      f[step₂](x) ≤
        f[step₁](x) + ((M₂ - M₁) / 2 : ℝ) * (r[step₁](x)) ^ (2 : ℕ) := by
    rw [quadraticallyRegularizedObjective_at_step_eq_modelValue,
      quadraticallyRegularizedObjective_at_step_eq_modelValue_add_penalty_shift
        (step := step₁) (x := x) (M := M₂)] at hstep₂
    exact hstep₂
  have hlower :
      f[step₁](x) + ((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) ≤ f[step₂](x) := by
    -- Move the correction term from the right-hand side to the left-hand side.
    have hshift :
        f[step₁](x) + ((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) ≤
          f[step₂](x) +
            (((M₁ - M₂) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) +
              ((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ)) := by
      simpa [add_assoc, add_left_comm, add_comm] using
        add_le_add_right hlower' (((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ))
    calc
      f[step₁](x) + ((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) ≤
          f[step₂](x) +
            (((M₁ - M₂) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ) +
              ((M₂ - M₁) / 2 : ℝ) * (r[step₂](x)) ^ (2 : ℕ)) := hshift
      _ = f[step₂](x) := by ring
  exact ⟨hlower, hupper⟩

end
