/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_15

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Text 9.7 is `bridge/view`: the chapter owner for the constant minimizing step family is already
`fixed_iteration_uniform_steps` from Lemma 9.15. This file keeps the mirror-descent specialization
and the textbook closed forms, but does not introduce a second owner for the same family. -/

/-- The textbook constant step family from Text 9.7, indexed by the first `N + 1` iterations. -/
def mirror_descent_textbook_stepsize (Theta0 Lf σ : ℝ) (N : ℕ) : Fin (N + 1) → ℝ :=
  fun _ ↦ Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N + 1 : ℝ))

/-- Evaluating the textbook step family at any iteration index returns the same constant value. -/
@[simp] theorem mirror_descent_textbook_stepsize_apply
    (Theta0 Lf σ : ℝ) (N : ℕ) (i : Fin (N + 1)) :
    mirror_descent_textbook_stepsize Theta0 Lf σ N i =
      Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N + 1 : ℝ)) := rfl

-- Proof sketch: specialize `fixed_iteration_uniform_steps_apply` to `ι = Fin (N + 1)` and
-- `β = Lf ^ 2 / (2 * σ)`, then use positivity of `Lf` and `σ` to rewrite the resulting
-- denominator to `Lf`, obtaining the textbook constant stepsize
-- `√(2 * Theta0 * σ) / (Lf * √(N + 1))`.
/-- For positive `Lf` and `σ`, specializing the Lemma 9.15 uniform minimizer to the
mirror-descent coefficients gives the textbook constant stepsize
`√(2 * Theta0 * σ) / (Lf * √(N + 1))`. -/
theorem fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize
    (Theta0 Lf σ : ℝ) (N : ℕ)
    (hLf : 0 < Lf) (hσ : 0 < σ) :
    fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ)) =
      mirror_descent_textbook_stepsize Theta0 Lf σ N := by
  ext i
  by_cases hTheta0 : 0 ≤ Theta0
  · have hNpos : 0 < (N + 1 : ℝ) := by positivity
    have hDenSqrt :
        Real.sqrt (Lf ^ 2 * (N + 1 : ℝ)) = Real.sqrt (Lf ^ 2) * Real.sqrt (N + 1 : ℝ) := by
      rw [Real.sqrt_mul (by positivity)]
    -- For nonnegative `Theta0`, rewrite the canonical minimizer into the textbook square-root form.
    calc
      fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ)) i
          = Real.sqrt (Theta0 / ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ))) := by
              simp [fixed_iteration_uniform_steps_apply, Fintype.card_fin]
      _ = Real.sqrt ((2 * Theta0 * σ) / (Lf ^ 2 * (N + 1 : ℝ))) := by
            congr 1
            field_simp [hLf.ne', hσ.ne', hNpos.ne']
      _ = Real.sqrt (2 * Theta0 * σ) / Real.sqrt (Lf ^ 2 * (N + 1 : ℝ)) := by
            rw [Real.sqrt_div (by positivity)]
      _ = Real.sqrt (2 * Theta0 * σ) / (Real.sqrt (Lf ^ 2) * Real.sqrt (N + 1 : ℝ)) := by
            rw [hDenSqrt]
      _ = Real.sqrt (2 * Theta0 * σ) / (Lf * Real.sqrt (N + 1 : ℝ)) := by
            rw [Real.sqrt_sq_eq_abs, abs_of_pos hLf]
      _ = mirror_descent_textbook_stepsize Theta0 Lf σ N i := by
            simp [mirror_descent_textbook_stepsize_apply]
  · have hTheta0_nonpos : Theta0 ≤ 0 := le_of_not_ge hTheta0
    have hDenPos : 0 < ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ)) := by
      positivity
    have hLeftArgNonpos :
        Theta0 / ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ)) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hTheta0_nonpos hDenPos.le
    have hRightArgNonpos : 2 * Theta0 * σ ≤ 0 := by
      nlinarith
    -- For negative `Theta0`, both square-root arguments are nonpositive, so both sides vanish.
    simp [
      fixed_iteration_uniform_steps_apply,
      Fintype.card_fin,
      mirror_descent_textbook_stepsize_apply,
      Real.sqrt_eq_zero_of_nonpos hLeftArgNonpos,
      Real.sqrt_eq_zero_of_nonpos hRightArgNonpos
    ]

-- Proof sketch: use positivity of `Theta0`, `Lf`, and `σ` together with positivity of
-- `Real.sqrt` on positive inputs to show that the displayed constant is positive.
/-- The optimal constant stepsize from Text 9.7 is positive at every iteration index when
`Theta0`, `Lf`, and `σ` are positive. -/
theorem mirror_descent_optimal_constant_stepsize_pos
    (Theta0 Lf σ : ℝ) (N : ℕ) (hTheta0 : 0 < Theta0) (hLf : 0 < Lf) (hσ : 0 < σ) :
    ∀ i : Fin (N + 1),
      0 < mirror_descent_textbook_stepsize Theta0 Lf σ N i := by
  have hβ : 0 < Lf ^ 2 / (2 * σ) := by
    positivity
  -- Transport positivity from the canonical uniform minimizer of Lemma 9.15.
  intro i
  have hcanonical :
      0 < fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ)) i :=
    fixed_iteration_uniform_steps_pos (ι := Fin (N + 1)) (α := Theta0)
      (β := Lf ^ 2 / (2 * σ)) hTheta0 hβ i
  have hstep :
      fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ)) i =
        mirror_descent_textbook_stepsize Theta0 Lf σ N i := by
    simpa using congrArg (fun t : Fin (N + 1) → ℝ => t i)
      (fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize
        Theta0 Lf σ N hLf hσ)
  rw [hstep] at hcanonical
  simpa using hcanonical

/-- Helper for Text 9.7: the closed form from Lemma 9.15 simplifies to the textbook
mirror-descent bound. -/
lemma mirrorDescentUniformObjectiveValueEqTextbookBound
    (Theta0 Lf σ : ℝ) (N : ℕ) (hTheta0 : 0 < Theta0) (hLf : 0 < Lf) (hσ : 0 < σ) :
    2 * Real.sqrt (Theta0 * (Lf ^ 2 / (2 * σ)) / (N + 1 : ℝ)) =
      Lf * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
  have hLfSqrt : Lf = Real.sqrt (Lf ^ 2) := by
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hLf]
  have hSqrtFour : Real.sqrt 4 = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    norm_num
  symm
  -- Rewrite the textbook expression into one square root and then simplify the inside scalar.
  calc
    Lf * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ))
        = Real.sqrt (Lf ^ 2) * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
            rw [← hLfSqrt]
    _ = Real.sqrt (Lf ^ 2) * (Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ))) := by
          rw [← mul_div_assoc]
    _ = Real.sqrt (Lf ^ 2) * Real.sqrt ((2 * Theta0) / (σ * (N + 1 : ℝ))) := by
          rw [← Real.sqrt_div (by positivity)]
    _ = Real.sqrt ((Lf ^ 2) * ((2 * Theta0) / (σ * (N + 1 : ℝ)))) := by
          rw [← Real.sqrt_mul (by positivity)]
    _ = Real.sqrt (4 * (Theta0 * (Lf ^ 2 / (2 * σ)) / (N + 1 : ℝ))) := by
          congr 1
          field_simp [hσ.ne']
          ring
    _ = Real.sqrt 4 * Real.sqrt (Theta0 * (Lf ^ 2 / (2 * σ)) / (N + 1 : ℝ)) := by
          rw [Real.sqrt_mul (by positivity)]
    _ = 2 * Real.sqrt (Theta0 * (Lf ^ 2 / (2 * σ)) / (N + 1 : ℝ)) := by
          rw [hSqrtFour]

-- Proof sketch: apply `fixed_iteration_objective_minimized_by_uniform_steps` and
-- `fixed_iteration_objective_uniform_step_value` from Lemma 9.15 with
-- `α = Theta0`, `β = Lf ^ 2 / (2 * σ)`, and `ι = Fin (N + 1)`, then simplify the uniform
-- optimizer to the textbook formula `√(2 * Theta0 * σ) / (Lf * √(N + 1))`.
/-- Text 9.7: with `α = Theta0`, `β = Lf ^ 2 / (2 * σ)`, and `m = N + 1`, the mirror-descent
fixed-iteration bound is minimized by the constant stepsize
`√(2 * Theta0 * σ) / (Lf * √(N + 1))`, and the attained value is
`Lf * √(2 * Theta0) / √(σ * (N + 1))`, which is the explicit `O(1 / √N)` bound. -/
theorem mirror_descent_optimal_constant_stepsize_minimizes_fixed_iteration_bound
    (Theta0 Lf σ : ℝ) (N : ℕ) (hTheta0 : 0 < Theta0) (hLf : 0 < Lf) (hσ : 0 < σ) :
    IsMinOn (fixed_iteration_objective Theta0 (Lf ^ 2 / (2 * σ)))
        {t : Fin (N + 1) → ℝ | ∀ i, 0 < t i}
        (mirror_descent_textbook_stepsize Theta0 Lf σ N) ∧
      fixed_iteration_objective Theta0 (Lf ^ 2 / (2 * σ))
          (mirror_descent_textbook_stepsize Theta0 Lf σ N) =
        Lf * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
  have hβ : 0 < Lf ^ 2 / (2 * σ) := by
    positivity
  constructor
  · -- Transport the minimizer statement from Lemma 9.15 through the bridge equality of stepsizes.
    simpa [fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize
      Theta0 Lf σ N hLf hσ] using
      fixed_iteration_objective_minimized_by_uniform_steps (ι := Fin (N + 1))
        (α := Theta0) (β := Lf ^ 2 / (2 * σ)) hTheta0 hβ
  · -- Evaluate the canonical minimizer, rewrite the schedule, and normalize the closed form.
    calc
      fixed_iteration_objective Theta0 (Lf ^ 2 / (2 * σ))
          (mirror_descent_textbook_stepsize Theta0 Lf σ N)
          =
            fixed_iteration_objective Theta0 (Lf ^ 2 / (2 * σ))
              (fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ))) := by
                rw [fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize
                  Theta0 Lf σ N hLf hσ]
      _ = 2 * Real.sqrt (Theta0 * (Lf ^ 2 / (2 * σ)) / (N + 1 : ℝ)) := by
            simpa using
              fixed_iteration_objective_uniform_step_value (ι := Fin (N + 1))
                (α := Theta0) (β := Lf ^ 2 / (2 * σ)) hTheta0 hβ
      _ = Lf * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
            exact mirrorDescentUniformObjectiveValueEqTextbookBound
              Theta0 Lf σ N hTheta0 hLf hσ

end
