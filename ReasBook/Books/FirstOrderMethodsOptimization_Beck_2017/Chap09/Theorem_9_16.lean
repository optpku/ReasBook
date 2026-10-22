/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_7
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Assumption_8_12
import FirstOrderMethodsOptimization_Beck_2017.Chap08.Definition_8_8
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_3
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_14
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Lemma_9_15
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Text_9_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f ω : E → EReal} {C XStar : Set E} {fOpt σ : ℝ}
variable {x g : ℕ → E} {t : ℕ → ℝ}

/- `prompt_add/` is absent in this workspace, so the API review is based on the existing Chapter 8
and Chapter 9 owner files. Theorem 9.16 is `source-facing`: it gives the fixed-horizon
`O(1 / √N)` running-best gap estimate for a concrete mirror-descent trajectory under the standing
constrained-problem assumptions of Definition 9.1, the Bregman-potential assumptions of Definition
9.2, and a uniform subgradient norm bound. The canonical owners already present are
`IsConstrainedConvexProblem`, `IsBregmanPotentialOn`, `SubgradientNormBoundOn`,
`is_mirror_descent_trajectory`, `B[ω]`, `best_achieved_function_value`, and the Text 9.7
specialization `mirror_descent_textbook_stepsize`, which bridges to the core owner
`fixed_iteration_uniform_steps`. -/

-- Proof sketch: start from the fixed-horizon mirror-descent estimate from Lemma 9.14, apply it to
-- the chosen optimizer `xStar ∈ XStar`, and bound the Bregman term by `Theta0` using
-- `h_bregman_upper`. The
-- subgradient correction term is controlled by `h_bound.norm_le`, and substituting the constant
-- schedule from Lemma 9.15 reduces the resulting ratio to the explicit `O(1 / √N)` expression.
/-- Helper for Theorem 9.16: if a positive realized mirror-descent step agrees with the finite-
horizon uniform steps from Lemma 9.15, then the horizon parameter `Theta0` is positive. -/
lemma theta0_pos_of_prefix_eq_fixedIterationUniformSteps
    {Theta0 Lf σ : ℝ} {N : ℕ} {t : ℕ → ℝ}
    (hLf : 0 < Lf) (hσ : 0 < σ) (ht0 : 0 < t 0)
    (h_stepsize :
      (fun n : Fin (N + 1) ↦ t n) =
        fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (Lf ^ 2 / (2 * σ))) :
    0 < Theta0 := by
  -- Read the prefix equality at the first iteration to identify `t 0` with the uniform constant.
  have h_zero :
      t 0 =
        Real.sqrt (Theta0 / ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ))) := by
    simpa [fixed_iteration_uniform_steps_apply, Fintype.card_fin] using
      congrArg (fun s : Fin (N + 1) → ℝ => s 0) h_stepsize
  have hsqrt_pos :
      0 <
        Real.sqrt (Theta0 / ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ))) := by
    rw [← h_zero]
    exact ht0
  have hden_pos : 0 < (Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ) := by
    positivity
  have harg_pos :
      0 < Theta0 / ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ)) := by
    exact Real.sqrt_pos.1 hsqrt_pos
  -- A positive quotient with positive denominator forces `Theta0` itself to be positive.
  by_contra hTheta0_nonpos
  have hsqrt_eq_zero :
      Real.sqrt (Theta0 / ((Lf ^ 2 / (2 * σ)) * (N + 1 : ℝ))) = 0 := by
    apply Real.sqrt_eq_zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hTheta0_nonpos) hden_pos.le
  rw [hsqrt_eq_zero] at hsqrt_pos
  exact lt_irrefl 0 hsqrt_pos

/-- Companion to Theorem 9.16: the same fixed-horizon running-best gap estimate, but stated using
the canonical finite-horizon constant-step owner `fixed_iteration_uniform_steps` on the prefix
`0, …, N`. -/
theorem mirror_descent_best_value_gap_le_one_div_sqrt_of_uniform_steps
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (Theta0 : ℝ)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ}
    (h_bregman_upper : B[ω] xStar (x 0) ≤ Theta0)
    (h_stepsize :
      (fun n : Fin (N + 1) ↦ t n) =
        fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (h_bound.L_f ^ 2 / (2 * σ))) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      h_bound.L_f * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
  let β : ℝ := h_bound.L_f ^ 2 / (2 * σ)
  have hβ : 0 < β := by
    -- The fixed-horizon coefficient is positive from the Lipschitz and strong-convexity moduli.
    dsimp [β]
    exact div_pos
      (by simpa [pow_two] using mul_pos h_bound.L_f_pos h_bound.L_f_pos)
      (mul_pos (by norm_num) hω.sigma_pos)
  have hTheta0_pos : 0 < Theta0 :=
    theta0_pos_of_prefix_eq_fixedIterationUniformSteps
      h_bound.L_f_pos hω.sigma_pos (h_traj.stepsize_pos 0) h_stepsize
  have hsum_pos : 0 < Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
    -- A prefix sum of positive steps is positive.
    have hmem : 0 ∈ Finset.range (N + 1) := by simp
    have hle :
        t 0 ≤ Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
      simpa using
        Finset.single_le_sum (fun k hk ↦ le_of_lt (h_traj.stepsize_pos k)) hmem
    exact lt_of_lt_of_le (h_traj.stepsize_pos 0) hle
  have hnum_le :
      B[ω] xStar (x 0) +
          β * Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ))
        ≤
      Theta0 + β * Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ)) := by
    -- Replace the Bregman diameter by the prescribed upper bound `Theta0`.
    simpa [β] using add_le_add_right h_bregman_upper
      (β * Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ)))
  have h_prefix_objective :
      (Theta0 + β * Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ))) /
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) =
        fixed_iteration_objective Theta0 β (fun n : Fin (N + 1) ↦ t n) := by
    -- Convert the `range` sums from Lemma 9.14 into the canonical `Fin`-indexed objective.
    have hsq :
        (∑ k : Fin (N + 1), t k ^ (2 : ℕ)) =
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ)) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ t k ^ (2 : ℕ)) (N + 1))
    have hsum :
        (∑ k : Fin (N + 1), t k) =
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
      simpa using (Fin.sum_univ_eq_sum_range (fun k : ℕ ↦ t k) (N + 1))
    rw [fixed_iteration_objective, hsq, hsum]
  -- Route correction: normalize Lemma 9.14 to the finite-horizon objective before evaluating it.
  calc
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt
        ≤
          (B[ω] xStar (x 0) +
              β * Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ))) /
            Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
            simpa [β] using
              mirror_descent_best_value_gap_le h_problem hω hω_diff h_bound h_traj hxStar N
    _ ≤
        (Theta0 + β * Finset.sum (Finset.range (N + 1)) (fun k ↦ t k ^ (2 : ℕ))) /
          Finset.sum (Finset.range (N + 1)) (fun k ↦ t k) := by
          exact div_le_div_of_nonneg_right hnum_le hsum_pos.le
    _ =
        fixed_iteration_objective Theta0 β (fun n : Fin (N + 1) ↦ t n) := by
          exact h_prefix_objective
    _ =
        fixed_iteration_objective Theta0 β
          (fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 β) := by
          rw [h_stepsize]
    _ = 2 * Real.sqrt (Theta0 * β / (N + 1 : ℝ)) := by
          simpa [β, Fintype.card_fin] using
            fixed_iteration_objective_uniform_step_value (ι := Fin (N + 1))
              (α := Theta0) (β := β) hTheta0_pos hβ
    _ = h_bound.L_f * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
          simpa [β] using
            mirrorDescentUniformObjectiveValueEqTextbookBound
              Theta0 h_bound.L_f σ N hTheta0_pos h_bound.L_f_pos hω.sigma_pos

-- Proof sketch: apply the companion theorem
-- `mirror_descent_best_value_gap_le_one_div_sqrt_of_uniform_steps` and identify the source-facing
-- textbook family with the canonical finite-horizon constant-step owner via
-- `fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize`.
/-- Theorem 9.16: under the standing constrained-problem assumptions of Definition 9.1 and the
Bregman-potential assumptions of Definition 9.2, if every subgradient of `f` on `C` has norm at
most `L_f = h_bound.L_f`, if some optimizer `xStar ∈ X^*` satisfies
`B_ω(xStar, x⁰) ≤ Theta0`, and if the mirror descent stepsizes are fixed to
`√(2 * Theta0 * σ) / (L_f * √(N + 1))` on the first `N + 1` iterations, equivalently if the
restricted prefix `n ↦ t n` on `Fin (N + 1)` agrees with
`mirror_descent_textbook_stepsize Theta0 h_bound.L_f σ N`, then the running-best objective gap
after `N` iterations is bounded by the standard `O(1 / √N)` estimate. -/
theorem mirror_descent_best_value_gap_le_one_div_sqrt_of_constant_stepsizes
    (h_problem : IsConstrainedConvexProblem f C XStar fOpt)
    (hω : IsBregmanPotentialOn ω C σ)
    (hω_diff : ∀ z ∈ subdifferential_domain ω,
      DifferentiableAt ℝ (fun w ↦ (ω w).toReal) z)
    (h_bound : SubgradientNormBoundOn f C)
    (h_traj :
      is_mirror_descent_trajectory (fun y ↦ (f y).toReal) (fun y ↦ (ω y).toReal) C x g t)
    (Theta0 : ℝ)
    {xStar : E} (hxStar : xStar ∈ XStar)
    {N : ℕ}
    (h_bregman_upper : B[ω] xStar (x 0) ≤ Theta0)
    (h_stepsize :
      (fun n : Fin (N + 1) ↦ t n) =
        mirror_descent_textbook_stepsize Theta0 h_bound.L_f σ N) :
    best_achieved_function_value (fun y ↦ (f y).toReal) x N - fOpt ≤
      h_bound.L_f * Real.sqrt (2 * Theta0) / Real.sqrt (σ * (N + 1 : ℝ)) := by
  have h_uniform_steps :
      (fun n : Fin (N + 1) ↦ t n) =
        fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (h_bound.L_f ^ 2 / (2 * σ)) := by
    -- Rewrite the textbook constant family back to the canonical fixed-horizon owner from Text 9.7.
    calc
      (fun n : Fin (N + 1) ↦ t n)
          = mirror_descent_textbook_stepsize Theta0 h_bound.L_f σ N := h_stepsize
      _ =
          fixed_iteration_uniform_steps (Fin (N + 1)) Theta0 (h_bound.L_f ^ 2 / (2 * σ)) := by
            symm
            exact fixed_iteration_uniform_steps_eq_mirror_descent_textbook_stepsize
              Theta0 h_bound.L_f σ N h_bound.L_f_pos hω.sigma_pos
  -- Reuse the uniform-step theorem after transporting the source-facing textbook schedule.
  exact mirror_descent_best_value_gap_le_one_div_sqrt_of_uniform_steps
    h_problem hω hω_diff h_bound h_traj Theta0 hxStar h_bregman_upper h_uniform_steps

end
