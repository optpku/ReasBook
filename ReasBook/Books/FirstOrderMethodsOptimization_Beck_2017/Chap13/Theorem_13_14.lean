/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Assumption_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_7
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_12
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_13

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the statement design is checked directly against
the existing Chapter 13 API.

This item is `source-facing`: it gives the convex-rate bounds for a generalized
conditional-gradient trajectory under one of the three textbook stepsize rules. The canonical
owners already present in the project are:

- `IsGeneralizedConditionalGradientProblem` for the regularity and domain hypotheses that
  drive the Chapter 13 analysis;
- `is_generalized_conditional_gradient_trajectory` for the generated sequence;
- `uses_generalized_conditional_gradient_standard_stepsize_rule` from Definition 13.6 for the
  admissible textbook stepsize choice;
- `generalized_conditional_gradient_norm` for the chapter gap quantity `S(x)`;
- `generalized_conditional_gradient_optimal_value` for the objective infimum `F_opt`.

Accordingly, this file adds only the atomic theorem statements for the two rate bounds, reusing
the Definition 13.6 stepsize-rule owners directly. The stronger Assumption 13.1 owner
already stores exactly the regularity package used here; optimizer nonemptiness is a derived
Text 13.1 consequence rather than primitive data. -/

variable
  {f : E → ℝ} {g : E → EReal} {Lf : NNReal}
  (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
  (hf_convex : ConvexOn ℝ Set.univ f)
  {x p : ℕ → E} {t : ℕ → Set.Icc (0 : ℝ) 1}
  (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
  (hsteps : uses_generalized_conditional_gradient_standard_stepsize_rule f g Lf x p t)
  {Ω : ℝ}
  (hΩ : ∀ u ∈ effective_domain g, ∀ v ∈ effective_domain g, ‖u - v‖ ≤ Ω)

local notation "F" => composite_model_objective f.toEReal g
local notation "F_opt" => generalized_conditional_gradient_optimal_value f.toEReal g

/-- Helper for Theorem 13.14: every optimizer attains the canonical Chapter 13 optimal value
`F_opt`. -/
private lemma generalized_conditional_gradient_optimal_value_eq_of_mem_optimal_set
    {xStar : E} (hxStar : xStar ∈ unconstrained_problem_solutions F) :
    F_opt = F xStar := by
  -- Rewrite optimizer membership as global minimality, then identify the infimum with that value.
  have hxmin : IsMinOn F Set.univ xStar := by
    simpa using hxStar
  have hglb : IsGLB (Set.range F) (F xStar) := by
    simpa using hxmin.isGLB (by simp : xStar ∈ (Set.univ : Set E))
  rw [generalized_conditional_gradient_optimal_value_eq_sInf]
  exact hglb.csInf_eq ⟨F xStar, ⟨xStar, rfl⟩⟩

/-- Helper for Theorem 13.14: the predefined diminishing comparison stepsize `2 / (k + 2)`
always belongs to `[0, 1]`. -/
lemma conditional_gradient_predefined_diminishing_stepsize_mem_Icc
    (k : ℕ) :
    conditional_gradient_predefined_diminishing_stepsize k ∈ Set.Icc (0 : ℝ) 1 := by
  -- Expand the formula and bound `2 / (k + 2)` between `0` and `1`.
  rw [Set.mem_Icc, conditional_gradient_predefined_diminishing_stepsize_eq]
  constructor
  · positivity
  · have hden_pos : 0 < (k + 2 : ℝ) := by
      positivity
    have htwo_le : (2 : ℝ) ≤ (k + 2 : ℝ) := by
      exact_mod_cast (show 2 ≤ k + 2 by omega)
    have hmul : 2 ≤ 1 * (k + 2 : ℝ) := by
      simpa using htwo_le
    exact (div_le_iff₀ hden_pos).2 hmul

/-- Helper for Theorem 13.14: every generalized conditional-gradient iterate stays in
`effective_domain g`. -/
private lemma generalized_conditional_gradient_trajectory_mem_effective_domain
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (k : ℕ) :
    x k ∈ effective_domain g := by
  -- The route correction is local: instead of importing the broken Lemma 13.8 file, rebuild the
  -- iterate-feasibility induction directly from the trajectory owner and convexity of `g`.
  induction' k with k hk
  · -- The initial iterate is feasible by the trajectory owner.
    exact htraj.zero_mem_effective_domain
  · -- The next iterate is the convex combination of two feasible points.
    rcases is_generalized_conditional_gradient_trajectory_step htraj k with ⟨hp, hstep⟩
    have hpdom :
        p k ∈ effective_domain g :=
      generalized_conditional_gradient_argmin_mem_effective_domain hk hp
    have hcombo :
        (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k ∈ effective_domain g :=
      combo_mem_effective_domain_of_is_convex_function hproblem.g_convex hpdom hk (t k).2
    have hrewrite :
        x (k + 1) = (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k := by
      have hxscale :
          x k - (t k : ℝ) • x k = (1 - (t k : ℝ)) • x k := by
        simpa using (sub_smul (1 : ℝ) (t k : ℝ) (x k)).symm
      calc
        x (k + 1) = x k + (t k : ℝ) • (p k - x k) := hstep
        _ = x k + ((t k : ℝ) • p k - (t k : ℝ) • x k) := by
          rw [smul_sub]
        _ = (t k : ℝ) • p k + (x k - (t k : ℝ) • x k) := by
          abel
        _ = (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k := by
          rw [hxscale]
    rw [hrewrite]
    exact hcombo

/-- Helper for Theorem 13.14: the composite objective is finite at every point of
`effective_domain g`, so it is the coercion of the corresponding real sum. -/
private lemma composite_model_objective_eq_coe_real_of_mem_effective_domain
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y : E} (hy : y ∈ effective_domain g) :
    F y = (((f y) + (g y).toReal : ℝ) : EReal) := by
  -- At feasible points, `g y` is finite and `f y` is already real-valued.
  have hgy :
      (((g y).toReal : ℝ) : EReal) = g y :=
    EReal.coe_toReal
      (mem_effective_domain.mp hy).ne
      (hproblem.toIsProperExtendedRealFunction.ne_bot y)
  rw [composite_model_objective_apply, ← hgy]
  simpa [Function.toEReal] using (EReal.coe_add (f y) (g y).toReal).symm

/-- Helper for Theorem 13.14: the composite objective has the expected real `toReal` formula at
every feasible point. -/
lemma composite_model_objective_toReal_eq_of_mem_effective_domain
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y : E} (hy : y ∈ effective_domain g) :
    (F y).toReal = f y + (g y).toReal := by
  -- Apply `toReal` to the finite-value normalization from the previous lemma.
  rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hproblem hy]
  simpa using EReal.toReal_coe (f y + (g y).toReal)

/-- Helper for Theorem 13.14: at a feasible argmin point, the generalized conditional-gradient
norm is the explicit real gap formula. -/
private lemma generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g) (hq : q ∈ effective_domain g)
    (hqmin : q ∈ generalized_conditional_gradient_argmin f g y) :
    S[f, g](y) =
      (((inner ℝ (∇ f y) (y - q) + (g y).toReal - (g q).toReal : ℝ)) : EReal) := by
  -- Realize the canonical norm by the chosen argmin and then rewrite the finite `g` values.
  rw [generalized_conditional_gradient_norm_eq_of_mem_argmin hqmin,
    generalized_conditional_gradient_gap_objective_apply]
  have hgy :
      (((g y).toReal : ℝ) : EReal) = g y :=
    EReal.coe_toReal
      (mem_effective_domain.mp hy).ne
      (hproblem.toIsProperExtendedRealFunction.ne_bot y)
  have hgq :
      (((g q).toReal : ℝ) : EReal) = g q :=
    EReal.coe_toReal
      (mem_effective_domain.mp hq).ne
      (hproblem.toIsProperExtendedRealFunction.ne_bot q)
  have hgap :
      (((inner ℝ (∇ f y) (y - q) + (g y).toReal - (g q).toReal : ℝ)) : EReal) =
        ((inner ℝ (∇ f y) (y - q) : ℝ) : EReal) + g y - g q := by
    rw [EReal.coe_sub, EReal.coe_add, hgy, hgq]
  exact hgap.symm

/-- Helper for Theorem 13.14: the real-valued conditional-gradient gap formula is the `toReal`
image of the canonical norm at a feasible argmin point. -/
private lemma generalized_conditional_gradient_norm_toReal_eq_gap_real_of_mem_argmin
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g) (hq : q ∈ effective_domain g)
    (hqmin : q ∈ generalized_conditional_gradient_argmin f g y) :
    (S[f, g](y)).toReal =
      inner ℝ (∇ f y) (y - q) + (g y).toReal - (g q).toReal := by
  -- The previous finite `EReal` representation turns `toReal` into the displayed real formula.
  rw [generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin hproblem hy hq hqmin]
  simpa using
    EReal.toReal_coe (inner ℝ (∇ f y) (y - q) + (g y).toReal - (g q).toReal)

/-- Helper for Theorem 13.14: every iterate gap value is finite, hence equal to the coercion of
its `toReal`. -/
lemma generalized_conditional_gradient_norm_eq_coe_toReal
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (k : ℕ) :
    S[f, g](x k) = (((S[f, g](x k)).toReal : ℝ) : EReal) := by
  -- Rewrite the canonical norm at the chosen argmin point by the explicit real gap formula.
  have hxk :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj k
  have hpk :
      p k ∈ generalized_conditional_gradient_argmin f g (x k) :=
    htraj.argmin_mem k
  have hpk_dom :
      p k ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hxk hpk
  rw [generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin
    hproblem hxk hpk_dom hpk]
  exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm

/-- Helper for Theorem 13.14: the adaptive conditional-gradient stepsize lies in `[0, 1]`
whenever the current gap value is nonnegative. -/
private lemma conditional_gradient_adaptive_stepsize_mem_Icc
    {Sx : ℝ} (hSx : 0 ≤ Sx) (y q : E) :
    conditional_gradient_adaptive_stepsize Sx Lf y q ∈ Set.Icc (0 : ℝ) 1 := by
  -- Split the explicit fallback branch from the clipped-ratio branch in Definition 13.6.
  by_cases hdeg : ‖q - y‖ = 0 ∨ Lf = 0
  · simpa [Set.mem_Icc, conditional_gradient_adaptive_stepsize, if_pos hdeg] using
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
  · have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
      exact_mod_cast Lf.2
    have hdiv_nonneg :
        0 ≤ Sx / ((Lf : ℝ) * ‖q - y‖ ^ (2 : ℕ)) := by
      exact div_nonneg hSx (mul_nonneg hLf_nonneg (sq_nonneg ‖q - y‖))
    rw [Set.mem_Icc, conditional_gradient_adaptive_stepsize, if_neg hdeg]
    constructor
    · exact le_min zero_le_one hdiv_nonneg
    · exact min_le_left _ _

/-- Helper for Theorem 13.14: the adaptive stepsize minimizes the scalar upper model from the
source proof on the interval `[0, 1]`, so its upper-model value is bounded above by the value at
any comparison stepsize `α ∈ [0, 1]`. -/
lemma adaptive_stepsize_upper_model_value_le_of_mem_Icc
    {Sx alpha : ℝ} (hSx : 0 ≤ Sx) (halpha : alpha ∈ Set.Icc (0 : ℝ) 1)
    (y q : E) :
    -(conditional_gradient_adaptive_stepsize Sx Lf y q) * Sx +
        ((((conditional_gradient_adaptive_stepsize Sx Lf y q) ^ (2 : ℕ) * (Lf : ℝ)) / 2) *
          ‖q - y‖ ^ (2 : ℕ)) ≤
      -alpha * Sx + (((alpha ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖q - y‖ ^ (2 : ℕ)) := by
  -- Route correction: isolate the source equation (13.28) as a pure scalar minimization lemma,
  -- so the main recurrence proof only has to invoke this comparison after the fundamental
  -- inequality.
  set s := conditional_gradient_adaptive_stepsize Sx Lf y q with hs
  by_cases hdeg : ‖q - y‖ = 0 ∨ Lf = 0
  · -- On the degenerate branch the quadratic term vanishes, so the model is just `-t Sx`.
    have hquad_zero (t : ℝ) :
        (((t ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖q - y‖ ^ (2 : ℕ)) = 0 := by
      rcases hdeg with hnorm | hLf
      · simp [hnorm]
      · simp [hLf]
    rw [hs, conditional_gradient_adaptive_stepsize_eq, if_pos hdeg, hquad_zero 1, hquad_zero alpha]
    nlinarith [hSx, halpha.2]
  · -- On the nondegenerate branch, complete the square around the unclipped minimizer
    -- `r = Sx / (L_f ‖q - y‖²)` and compare squared distances to that center.
    have hnorm_ne : ‖q - y‖ ≠ 0 := by
      intro hnorm
      exact hdeg (Or.inl hnorm)
    have hq_ne : q ≠ y := by
      intro hq
      apply hnorm_ne
      simpa [hq]
    have hLf_ne : Lf ≠ 0 := by
      intro hLf
      exact hdeg (Or.inr hLf)
    rw [hs, conditional_gradient_adaptive_stepsize_of_ne Sx hq_ne hLf_ne]
    let D : ℝ := (Lf : ℝ) * ‖q - y‖ ^ (2 : ℕ)
    let r : ℝ := Sx / D
    have hLf_pos : 0 < (Lf : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr hLf_ne)
    have hnorm_pos : 0 < ‖q - y‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hq_ne)
    have hD_pos : 0 < D := by
      dsimp [D]
      positivity
    have hrS : Sx = D * r := by
      dsimp [r]
      field_simp [hD_pos.ne']
    have hquad_rewrite (t : ℝ) :
        -t * Sx + (((t ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖q - y‖ ^ (2 : ℕ)) =
          -t * Sx + D * t ^ (2 : ℕ) / 2 := by
      dsimp [D]
      ring
    by_cases hr_le_one : r ≤ 1
    · -- If `r ≤ 1`, the adaptive stepsize is exactly the unclipped minimizer `r`.
      rw [min_eq_right hr_le_one, hquad_rewrite r, hquad_rewrite alpha, hrS]
      have hsq : 0 ≤ (alpha - r) ^ (2 : ℕ) := sq_nonneg (alpha - r)
      nlinarith [hD_pos.le, hsq]
    · -- If `r > 1`, the interval minimizer is the clipped endpoint `1`.
      have hr_one_lt : 1 < r := lt_of_not_ge hr_le_one
      rw [min_eq_left (le_of_lt hr_one_lt), hquad_rewrite 1, hquad_rewrite alpha, hrS]
      have hsq :
          (r - 1) ^ (2 : ℕ) ≤ (r - alpha) ^ (2 : ℕ) := by
        have hr_sub_one_nonneg : 0 ≤ r - 1 := by
          linarith
        have hmono : r - 1 ≤ r - alpha := by
          linarith [halpha.2]
        nlinarith
      nlinarith [hD_pos.le, hsq]

/-- Helper for Theorem 13.14: every objective gap `F(xᵏ) - F_opt` is the coercion of the
corresponding real difference of finite values. -/
lemma generalized_conditional_gradient_objective_gap_eq_coe_sub_optimal_value
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (k : ℕ) :
    F (x k) - F_opt =
      ((((F (x k)).toReal - (F_opt).toReal : ℝ)) : EReal) := by
  -- Rewrite the iterate value and the optimal value through finite feasible witnesses.
  obtain ⟨xStar, hxStar⟩ := generalized_conditional_gradient_optimal_set_nonempty hproblem
  have hxmin : IsMinOn F Set.univ xStar := by
    simpa using hxStar
  obtain ⟨y0, hy0⟩ :=
    hproblem.toIsProperExtendedRealFunction.effective_domain_nonempty
  have hFy0_lt_top : F y0 < ⊤ := by
    rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hproblem hy0]
    exact EReal.coe_lt_top _
  have hFxStar_ne_top : F xStar ≠ ⊤ := by
    rw [isMinOn_iff] at hxmin
    have hle : F xStar ≤ F y0 := by
      exact hxmin y0 (by simp)
    exact ne_of_lt (lt_of_le_of_lt hle hFy0_lt_top)
  have hxStar_dom : xStar ∈ effective_domain g := by
    refine mem_effective_domain.mpr ?_
    refine lt_top_iff_ne_top.mpr ?_
    intro hg_top
    have htop : F xStar = ⊤ := by
      rw [composite_model_objective_apply, hg_top]
      simpa [Function.toEReal] using EReal.add_top_of_ne_bot (EReal.coe_ne_bot (f xStar))
    exact hFxStar_ne_top htop
  have hxk_dom :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj k
  have hxk_val :
      F (x k) = (((F (x k)).toReal : ℝ) : EReal) := by
    rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hproblem hxk_dom]
    exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm
  have hopt_eq :
      F_opt = F xStar :=
    generalized_conditional_gradient_optimal_value_eq_of_mem_optimal_set hxStar
  have hopt_val :
      F_opt = (((F_opt).toReal : ℝ) : EReal) := by
    rw [hopt_eq, composite_model_objective_eq_coe_real_of_mem_effective_domain hproblem hxStar_dom]
    exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm
  rw [hxk_val, hopt_val, ← EReal.coe_sub]
  simp

/-- Helper for Theorem 13.14: the real objective gap is the ordinary difference of the finite
iterate and optimal values. -/
lemma generalized_conditional_gradient_objective_gap_toReal_eq_sub_optimal_value
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (k : ℕ) :
    (F (x k) - F_opt).toReal = (F (x k)).toReal - (F_opt).toReal := by
  -- Apply `toReal` to the finite `EReal` normalization of the objective gap.
  rw [generalized_conditional_gradient_objective_gap_eq_coe_sub_optimal_value hproblem htraj k]
  simpa using EReal.toReal_coe ((F (x k)).toReal - (F_opt).toReal)

/-- Helper for Theorem 13.14: Assumption 13.1 restricts the smoothness of the real-valued term
`f` from `effective_domain f.toEReal` to the smaller set `effective_domain g`. -/
lemma generalized_conditional_gradient_smooth_on_effective_domain_g
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf) :
    is_l_smooth_on f (effective_domain g) Lf := by
  -- Rewrite the smoothness owner once, then restrict both differentiability and Lipschitz
  -- control along the domain inclusion `effective_domain g ⊆ effective_domain f`.
  have hsmooth := hproblem.f_toReal_smooth_on_effective_domain
  rw [is_l_smooth_on_iff] at hsmooth ⊢
  constructor
  · intro y hy
    simpa using
      hsmooth.1 y
        (hproblem.g_effective_domain_subset_f_effective_domain hy)
  · intro y hy z hz
    simpa using
      hsmooth.2 y
        (hproblem.g_effective_domain_subset_f_effective_domain hy) z
        (hproblem.g_effective_domain_subset_f_effective_domain hz)

/-- Helper for Theorem 13.14: every feasible trial point on the conditional-gradient segment
remains in `effective_domain g`. -/
private lemma conditional_gradient_trial_mem_effective_domain_of_mem_Icc
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g) (hq : q ∈ effective_domain g)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    y + α • (q - y) ∈ effective_domain g := by
  -- Rewrite the affine step as the convex combination from Lemma 13.7, then use convexity of
  -- `g` to stay in the effective domain.
  have hcombo :
      α • q + (1 - α) • y ∈ effective_domain g :=
    combo_mem_effective_domain_of_is_convex_function hproblem.g_convex hq hy hα
  simpa [conditional_gradient_segment_eq_convex_combo, add_comm, add_left_comm, add_assoc] using
    hcombo

/-- Helper for Theorem 13.14: the composite objective is the coercion of its real value at every
feasible point. -/
private lemma composite_model_objective_eq_coe_toReal_of_mem_effective_domain
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y : E} (hy : y ∈ effective_domain g) :
    F y = (((F y).toReal : ℝ) : EReal) := by
  -- First rewrite `F y` through the explicit finite real formula, then fold it back as a
  -- coercion of `toReal`.
  rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hproblem hy]
  exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm

/-- Helper for Theorem 13.14: at a feasible argmin point, the generalized conditional-gradient
norm is the coercion of its real `toReal` value. -/
private lemma generalized_conditional_gradient_norm_eq_coe_toReal_of_mem_argmin
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g) (hq : q ∈ effective_domain g)
    (hqmin : q ∈ generalized_conditional_gradient_argmin f g y) :
    S[f, g](y) = (((S[f, g](y)).toReal : ℝ) : EReal) := by
  -- Rewrite the norm by the explicit finite real gap formula, then read that formula back as the
  -- coercion of its `toReal`.
  rw [generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin hproblem hy hq hqmin]
  exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm

/-- Helper for Theorem 13.14: argmin membership implies the real-valued linearized subproblem at
`q` is no larger than the comparison value at the base point `y`. -/
private lemma generalized_conditional_gradient_subproblem_toReal_le_of_mem_argmin
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g)
    (hqmin : q ∈ generalized_conditional_gradient_argmin f g y) :
    inner ℝ (∇ f y) q + (g q).toReal ≤ inner ℝ (∇ f y) y + (g y).toReal := by
  -- Compare the minimizing subproblem value at `q` with the comparison point `y`, then rewrite
  -- both finite `EReal` values as real coercions.
  have hq :
      q ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hy hqmin
  have hmin :
      generalized_conditional_gradient_subproblem f g y q ≤
        generalized_conditional_gradient_subproblem f g y y := by
    exact (isMinOn_univ_iff.mp (mem_generalized_conditional_gradient_argmin_iff.mp hqmin)) y
  have hgq :
      (((g q).toReal : ℝ) : EReal) = g q :=
    EReal.coe_toReal
      (mem_effective_domain.mp hq).ne
      (hproblem.toIsProperExtendedRealFunction.ne_bot q)
  have hgy :
      (((g y).toReal : ℝ) : EReal) = g y :=
    EReal.coe_toReal
      (mem_effective_domain.mp hy).ne
      (hproblem.toIsProperExtendedRealFunction.ne_bot y)
  have hleft :
      generalized_conditional_gradient_subproblem f g y q =
        (((inner ℝ (∇ f y) q + (g q).toReal : ℝ)) : EReal) := by
    rw [generalized_conditional_gradient_subproblem_apply, ← hgq, real_inner_comm]
    simpa using (EReal.coe_add (inner ℝ (∇ f y) q) (g q).toReal).symm
  have hright :
      generalized_conditional_gradient_subproblem f g y y =
        (((inner ℝ (∇ f y) y + (g y).toReal : ℝ)) : EReal) := by
    rw [generalized_conditional_gradient_subproblem_apply, ← hgy, real_inner_comm]
    simpa using (EReal.coe_add (inner ℝ (∇ f y) y) (g y).toReal).symm
  rw [hleft, hright] at hmin
  exact_mod_cast hmin

/-- Helper for Theorem 13.14: the generalized conditional-gradient norm is nonnegative at every
feasible argmin point. -/
private lemma generalized_conditional_gradient_norm_toReal_nonneg_of_mem_argmin
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g)
    (hqmin : q ∈ generalized_conditional_gradient_argmin f g y) :
    0 ≤ (S[f, g](y)).toReal := by
  -- Compare the minimizing subproblem value with the base point, then rewrite the resulting real
  -- inequality as the explicit finite gap formula for `S[f, g](y)`.
  have hq :
      q ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hy hqmin
  have hsub :
      inner ℝ (∇ f y) q + (g q).toReal ≤ inner ℝ (∇ f y) y + (g y).toReal :=
    generalized_conditional_gradient_subproblem_toReal_le_of_mem_argmin hproblem hy hqmin
  have hgap_nonneg :
      0 ≤ inner ℝ (∇ f y) (y - q) + (g y).toReal - (g q).toReal := by
    rw [inner_sub_right]
    linarith
  rw [generalized_conditional_gradient_norm_toReal_eq_gap_real_of_mem_argmin hproblem hy hq hqmin]
  exact hgap_nonneg

/-- Helper for Theorem 13.14: Lemma 13.7 becomes a real-valued inequality once all objective and
gap terms are normalized at feasible points. -/
private lemma generalized_conditional_gradient_fundamental_inequality_toReal
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    {y q : E} (hy : y ∈ effective_domain g)
    (hqmin : q ∈ generalized_conditional_gradient_argmin f g y)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (F (y + α • (q - y))).toReal ≤
      (F y).toReal - α * (S[f, g](y)).toReal +
        (((α ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖q - y‖ ^ (2 : ℕ)) := by
  -- Route correction: normalize the EReal-valued one-step inequality from Lemma 13.7 before
  -- splitting the textbook stepsize branches, so the recurrence proof only manipulates plain real
  -- inequalities.
  have hq_dom :
      q ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hy hqmin
  have htrial_dom :
      y + α • (q - y) ∈ effective_domain g :=
    conditional_gradient_trial_mem_effective_domain_of_mem_Icc hproblem hy hq_dom hα
  have hfund :
      F (y + α • (q - y)) ≤
        F y - (α : EReal) * S[f, g](y) +
          ((((α ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖q - y‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (generalized_conditional_gradient_fundamental_inequality
        hproblem.toIsProperExtendedRealFunction.ne_bot
        hproblem.g_convex
        (generalized_conditional_gradient_smooth_on_effective_domain_g hproblem)
        hy hqmin hα)
  rw [composite_model_objective_eq_coe_toReal_of_mem_effective_domain
      hproblem htrial_dom,
    composite_model_objective_eq_coe_toReal_of_mem_effective_domain
      hproblem hy,
    generalized_conditional_gradient_norm_eq_coe_toReal_of_mem_argmin
      hproblem hy hq_dom hqmin,
    ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add] at hfund
  exact_mod_cast hfund

include hproblem htraj hsteps hΩ
/-- Helper for Theorem 13.14: all three textbook stepsize rules satisfy the common one-step
model recurrence from the source proof before the diameter bound is inserted. -/
lemma generalized_conditional_gradient_standard_stepsize_model_recurrence
    (k : ℕ) :
    (F (x (k + 1))).toReal ≤
      (F (x k)).toReal -
        conditional_gradient_predefined_diminishing_stepsize k * (S[f, g](x k)).toReal +
          (((conditional_gradient_predefined_diminishing_stepsize k) ^ (2 : ℕ) *
              (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ) := by
  let αk : ℝ := conditional_gradient_predefined_diminishing_stepsize k
  have hαk : αk ∈ Set.Icc (0 : ℝ) 1 :=
    conditional_gradient_predefined_diminishing_stepsize_mem_Icc k
  have hxk :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj k
  have hpk :
      p k ∈ generalized_conditional_gradient_argmin f g (x k) :=
    htraj.argmin_mem k
  have hpk_dom :
      p k ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hxk hpk
  have htrial :
      (F (x k + αk • (p k - x k))).toReal ≤
        (F (x k)).toReal - αk * (S[f, g](x k)).toReal +
          (((αk ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) := by
    simpa [αk] using
      generalized_conditional_gradient_fundamental_inequality_toReal
        hproblem hxk hpk hαk
  rcases hsteps with hpredef | hrest
  · -- The predefined branch is exactly equation (13.26) with `t_k = α_k`.
    have htk_eq : (t k : ℝ) = αk := by
      simpa [αk] using hpredef k
    have hstep_eq :
        x (k + 1) = x k + αk • (p k - x k) := by
      calc
        x (k + 1) = x k + (t k : ℝ) • (p k - x k) := htraj.step_eq k
        _ = x k + αk • (p k - x k) := by rw [htk_eq]
    simpa [hstep_eq, αk] using htrial
  · rcases hrest with hadapt | hexact
    · -- The adaptive branch first uses Lemma 13.7 at the adaptive step and then the scalar
      -- model comparison from equation (13.28).
      have hS_nonneg :
          0 ≤ (S[f, g](x k)).toReal :=
        generalized_conditional_gradient_norm_toReal_nonneg_of_mem_argmin hproblem hxk hpk
      rcases hadapt k with ⟨_, _, htk_eq⟩
      have hstep_adapt :
          (F (x (k + 1))).toReal ≤
            (F (x k)).toReal - (t k : ℝ) * (S[f, g](x k)).toReal +
              (((((t k : ℝ) ^ (2 : ℕ)) * (Lf : ℝ)) / 2) *
                ‖p k - x k‖ ^ (2 : ℕ)) := by
        simpa [htraj.step_eq k] using
          generalized_conditional_gradient_fundamental_inequality_toReal
            hproblem hxk hpk (t k).2
      have hmodel_compare :
          -(t k : ℝ) * (S[f, g](x k)).toReal +
              (((((t k : ℝ) ^ (2 : ℕ)) * (Lf : ℝ)) / 2) *
                ‖p k - x k‖ ^ (2 : ℕ)) ≤
            -αk * (S[f, g](x k)).toReal +
              (((αk ^ (2 : ℕ) * (Lf : ℝ)) / 2) *
                ‖p k - x k‖ ^ (2 : ℕ)) := by
        rw [htk_eq]
        simpa [αk] using
          adaptive_stepsize_upper_model_value_le_of_mem_Icc
            hS_nonneg hαk (x k) (p k)
      linarith
    · -- The exact-line-search branch compares the minimizing step with the common trial scalar
      -- `α_k`, then inserts the predefined-step model inequality.
      have htrial_dom :
          x k + αk • (p k - x k) ∈ effective_domain g :=
        conditional_gradient_trial_mem_effective_domain_of_mem_Icc hproblem hxk hpk_dom hαk
      have hxnext :
          x (k + 1) ∈ effective_domain g :=
        generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj (k + 1)
      have hcompare :
          F (x (k + 1)) ≤ F (x k + αk • (p k - x k)) := by
        have hexactk := hexact k
        rw [mem_conditional_gradient_exact_line_search_stepsizes_iff, isMinOn_iff] at hexactk
        rcases hexactk with ⟨_, hmin⟩
        simpa [htraj.step_eq k, αk] using hmin αk hαk
      have hcompare_real :
          (F (x (k + 1))).toReal ≤ (F (x k + αk • (p k - x k))).toReal :=
        EReal.toReal_le_toReal hcompare
          (by
            rw [composite_model_objective_eq_coe_real_of_mem_effective_domain
              hproblem hxnext]
            exact EReal.coe_ne_bot _)
          (by
            rw [composite_model_objective_eq_coe_real_of_mem_effective_domain
              hproblem htrial_dom]
            exact EReal.coe_ne_top _)
      exact le_trans hcompare_real htrial
omit hproblem htraj hsteps hΩ

include hproblem htraj hsteps hΩ
/-- Helper for Theorem 13.14: the diameter bound `Ω` converts the model recurrence into the
scalar value recurrence from equation (13.u67). -/
lemma generalized_conditional_gradient_standard_stepsize_value_recurrence
    (k : ℕ) :
    (F (x (k + 1))).toReal ≤
      (F (x k)).toReal -
        conditional_gradient_predefined_diminishing_stepsize k * (S[f, g](x k)).toReal +
          (((Lf : ℝ) * Ω ^ (2 : ℕ)) / 2) *
            (conditional_gradient_predefined_diminishing_stepsize k) ^ (2 : ℕ) := by
  let αk : ℝ := conditional_gradient_predefined_diminishing_stepsize k
  have hxk :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj k
  have hpk :
      p k ∈ generalized_conditional_gradient_argmin f g (x k) :=
    htraj.argmin_mem k
  have hpk_dom :
      p k ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hxk hpk
  have hnorm_le :
      ‖p k - x k‖ ≤ Ω := by
    simpa [norm_sub_rev] using hΩ (x k) hxk (p k) hpk_dom
  have hquad_le :
      (((αk ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ)) ≤
        (((Lf : ℝ) * Ω ^ (2 : ℕ)) / 2) * αk ^ (2 : ℕ) := by
    have hsq_le :
        ‖p k - x k‖ ^ (2 : ℕ) ≤ Ω ^ (2 : ℕ) := by
      nlinarith [hnorm_le, norm_nonneg (p k - x k)]
    have hcoeff_nonneg : 0 ≤ ((αk ^ (2 : ℕ) * (Lf : ℝ)) / 2) := by
      positivity
    calc
      (((αk ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p k - x k‖ ^ (2 : ℕ))
          ≤ ((αk ^ (2 : ℕ) * (Lf : ℝ)) / 2) * Ω ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hsq_le hcoeff_nonneg
      _ = (((Lf : ℝ) * Ω ^ (2 : ℕ)) / 2) * αk ^ (2 : ℕ) := by
        ring
  have hmodel :=
    generalized_conditional_gradient_standard_stepsize_model_recurrence
      hproblem htraj hsteps hΩ k
  dsimp [αk] at hquad_le hmodel ⊢
  linarith
omit hproblem htraj hsteps hΩ

include hproblem htraj hsteps hΩ
/-- Helper for Theorem 13.14: the source-proof recurrence to feed Lemma 13.13 is the
real-valued gap recursion obtained by comparing every admissible textbook stepsize rule against
the common scalar `α_k = 2 / (k + 2)`. -/
lemma generalized_conditional_gradient_standard_stepsize_recurrence
    (k : ℕ) :
    (F (x (k + 1)) - F_opt).toReal ≤
      (F (x k) - F_opt).toReal -
        conditional_gradient_predefined_diminishing_stepsize k * (S[f, g](x k)).toReal +
          (((Lf : ℝ) * Ω ^ (2 : ℕ)) / 2) *
            (conditional_gradient_predefined_diminishing_stepsize k) ^ (2 : ℕ) := by
  -- Route correction: keep the already-closed value recurrence, and only subtract the constant
  -- `(F_opt).toReal` after rewriting both objective gaps as ordinary real differences.
  have hvalue :=
    generalized_conditional_gradient_standard_stepsize_value_recurrence
      hproblem htraj hsteps hΩ k
  rw [generalized_conditional_gradient_objective_gap_toReal_eq_sub_optimal_value
      hproblem htraj (k + 1),
    generalized_conditional_gradient_objective_gap_toReal_eq_sub_optimal_value
      hproblem htraj k]
  linarith
omit hproblem htraj hsteps hΩ

/-- Helper for Theorem 13.14: convexity of `f` and Lemma 13.12 imply that the real objective gap
is dominated by the real generalized conditional-gradient gap at every iterate. -/
lemma generalized_conditional_gradient_objective_gap_toReal_le_norm_toReal
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (k : ℕ) :
    (F (x k) - F_opt).toReal ≤ (S[f, g](x k)).toReal := by
  -- Specialize Lemma 13.12 to the feasible iterate `x^k`, then rewrite both sides through the
  -- finite-value normalizations already established in this file.
  have hxk :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj k
  have hxk_f :
      x k ∈ effective_domain f.toEReal :=
    hproblem.g_effective_domain_subset_f_effective_domain hxk
  have hdiff :
      DifferentiableAt ℝ (fun y ↦ ((f.toEReal) y).toReal) (x k) :=
    (hproblem.is_differentiable_at ⟨x k, hxk_f⟩).2
  have hgap_ereal :
      F (x k) - F_opt ≤ S[f, g](x k) := by
    simpa [ge_iff_le] using
      (generalized_conditional_gradient_gap_ge_objective_gap
        (fun y ↦ EReal.coe_ne_bot (f y))
        (Function.toEReal_isConvexFunction hf_convex)
        hxk_f hdiff hxk)
  have hleft_bot :
      F (x k) - F_opt ≠ ⊥ := by
    rw [generalized_conditional_gradient_objective_gap_eq_coe_sub_optimal_value hproblem htraj k]
    exact EReal.coe_ne_bot _
  have hright_top :
      S[f, g](x k) ≠ ⊤ := by
    rw [generalized_conditional_gradient_norm_eq_coe_toReal hproblem htraj k]
    exact EReal.coe_ne_top _
  exact EReal.toReal_le_toReal hgap_ereal hleft_bot hright_top

/-- Helper for Theorem 13.14: the real objective gap is nonnegative at every iterate because
`F_opt` is the infimum of attained objective values. -/
lemma generalized_conditional_gradient_objective_gap_toReal_nonneg
    (hproblem : IsGeneralizedConditionalGradientProblem f.toEReal g Lf)
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (k : ℕ) :
    0 ≤ (F (x k) - F_opt).toReal := by
  -- Compare the optimal value with the attained iterate value, convert that finite `EReal`
  -- inequality to `ℝ`, and then rewrite the gap as an ordinary difference.
  obtain ⟨xStar, hxStar⟩ := generalized_conditional_gradient_optimal_set_nonempty hproblem
  have hopt_le :
      F_opt ≤ F (x k) := by
    rw [generalized_conditional_gradient_optimal_value_eq_sInf]
    exact sInf_le ⟨x k, rfl⟩
  have hopt_eq :
      F_opt = F xStar :=
    generalized_conditional_gradient_optimal_value_eq_of_mem_optimal_set hxStar
  have hopt_ne_bot :
      F_opt ≠ ⊥ := by
    rw [hopt_eq, composite_model_objective_apply]
    simpa [Function.toEReal] using
      show (((f xStar : ℝ) : EReal) + g xStar) ≠ ⊥ by
        intro hbot
        rw [EReal.add_eq_bot_iff] at hbot
        rcases hbot with hleft | hright
        · exact EReal.coe_ne_bot _ hleft
        · exact hproblem.toIsProperExtendedRealFunction.ne_bot xStar hright
  have hxk :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain hproblem htraj k
  have hFxk_ne_top :
      F (x k) ≠ ⊤ := by
    rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hproblem hxk]
    exact EReal.coe_ne_top _
  have hreal_le :
      (F_opt).toReal ≤ (F (x k)).toReal :=
    EReal.toReal_le_toReal hopt_le hopt_ne_bot hFxk_ne_top
  rw [generalized_conditional_gradient_objective_gap_toReal_eq_sub_optimal_value hproblem htraj k]
  exact sub_nonneg.mpr hreal_le

-- Proof sketch: specialize the one-step estimate from the generalized conditional-gradient
-- analysis to the three admissible stepsize rules, giving the recurrence
-- `a_{k+1} ≤ a_k - α_k b_k + (L_f Ω^2 / 2) α_k^2` with
-- `a_k = F(xᵏ) - F_opt`, `b_k = S(xᵏ)`, and `α_k = 2 / (k + 2)`. Use convexity of `f` together
-- with Lemma 13.12 to obtain `a_k ≤ b_k`, then apply Lemma 13.13 (1) with `p = 1`.
include hproblem hf_convex htraj hsteps hΩ
/-- Theorem 13.14 (1): under Assumption 13.1, if `f` is convex and
`(xᵏ, pᵏ, tₖ)` is a generalized conditional-gradient trajectory using either the predefined
stepsize `tₖ = 2 / (k + 2)`, the adaptive stepsize, or exact line search, and if `Ω` bounds the
diameter of `dom(g)`, then the objective gap satisfies
`F(xᵏ) - F_opt ≤ 2 L_f Ω^2 / k` for every `k ≥ 1`. -/
theorem generalized_conditional_gradient_objective_gap_le_sublinear_rate
    {k : ℕ} (hk : 1 ≤ k) :
    F (x k) - F_opt ≤
      (((2 : ℝ) * (Lf : ℝ) * Ω ^ (2 : ℕ) / (k : ℝ) : ℝ) : EReal) := by
  -- Package the source recurrence into Lemma 13.13 with `p = 1`, then cast the resulting real
  -- estimate back to the chapter's `EReal` objective gap.
  let a : ℕ → ℝ := fun n ↦ (F (x n) - F_opt).toReal
  let b : ℕ → ℝ := fun n ↦ (S[f, g](x n)).toReal
  let A : ℝ := (Lf : ℝ) * Ω ^ (2 : ℕ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  have hbound :=
    scalar_recurrence_le_sublinear_bound_of_conditional_gradient_stepsize
      a b A 1 (by norm_num)
      (fun n ↦ generalized_conditional_gradient_objective_gap_toReal_nonneg hproblem htraj n)
      (fun n ↦ by
        simpa [a, b, A] using
          generalized_conditional_gradient_standard_stepsize_recurrence
            hproblem htraj hsteps hΩ n)
      (fun n ↦ generalized_conditional_gradient_objective_gap_toReal_le_norm_toReal
        hproblem hf_convex htraj n)
      hk
  have hbound' :
      a k ≤ (2 * A) / (k : ℝ) := by
    simpa [a, A, hA_nonneg, max_eq_left hA_nonneg, mul_assoc, mul_left_comm, mul_comm] using
      hbound
  have hfinal_real :
      (F (x k)).toReal - (F_opt).toReal ≤
        (2 : ℝ) * (Lf : ℝ) * Ω ^ (2 : ℕ) / (k : ℝ) := by
    rw [← generalized_conditional_gradient_objective_gap_toReal_eq_sub_optimal_value
      hproblem htraj k]
    simpa [a, A, mul_assoc, mul_left_comm, mul_comm] using hbound'
  rw [generalized_conditional_gradient_objective_gap_eq_coe_sub_optimal_value hproblem htraj k]
  exact_mod_cast hfinal_real
omit hproblem hf_convex htraj hsteps hΩ

-- Proof sketch: keep the same recurrence
-- `a_{k+1} ≤ a_k - α_k b_k + (L_f Ω^2 / 2) α_k^2` and domination `a_k ≤ b_k` as in part `(1)`,
-- then apply Lemma 13.13 (2) with `p = 1` to the half-tail interval
-- `{⌊k / 2⌋ + 2, …, k}`. The resulting existential bound is equivalent to the textbook minimum
-- estimate on `S(xⁿ)` over that finite interval.
include hproblem hf_convex htraj hsteps hΩ
/-- Theorem 13.14 (2): under the same hypotheses, for every `k ≥ 3` there exists an index
`n ∈ {⌊k / 2⌋ + 2, …, k}` such that
`S(xⁿ) ≤ 8 L_f Ω^2 / (k - 2)`. Since the chapter owner `S[f, g](x)` is `EReal`-valued, the
bound is stated directly in `EReal`; equivalently, the minimum of `S(xⁿ)` on that half-tail
interval obeys the same bound. -/
theorem exists_half_tail_generalized_conditional_gradient_gap_le_sublinear_rate
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ n ∈ Set.Icc (k / 2 + 2) k,
      S[f, g](x n) ≤
        (((8 * (Lf : ℝ) * Ω ^ (2 : ℕ)) / ((k - 2 : ℕ) : ℝ) : ℝ) : EReal) := by
  -- Reuse the same scalar recurrence package as in part `(1)`, then cast the selected real gap
  -- bound back to the chapter's `EReal`-valued norm.
  let a : ℕ → ℝ := fun n ↦ (F (x n) - F_opt).toReal
  let b : ℕ → ℝ := fun n ↦ (S[f, g](x n)).toReal
  let A : ℝ := (Lf : ℝ) * Ω ^ (2 : ℕ)
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    positivity
  obtain ⟨n, hn, hbn⟩ :=
    exists_half_tail_index_le_sublinear_bound_of_conditional_gradient_stepsize
      a b A 1 (by norm_num)
      (fun m ↦ generalized_conditional_gradient_objective_gap_toReal_nonneg hproblem htraj m)
      (fun m ↦ by
        simpa [a, b, A] using
          generalized_conditional_gradient_standard_stepsize_recurrence
            hproblem htraj hsteps hΩ m)
      (fun m ↦ generalized_conditional_gradient_objective_gap_toReal_le_norm_toReal
        hproblem hf_convex htraj m)
      hk
  have hbn' :
      b n ≤ (8 * A) / (((k - 2 : ℕ) : ℝ)) := by
    simpa [a, A, hA_nonneg, max_eq_left hA_nonneg, mul_assoc, mul_left_comm, mul_comm] using
      hbn
  have hfinal_real :
      (S[f, g](x n)).toReal ≤
        (8 : ℝ) * (Lf : ℝ) * Ω ^ (2 : ℕ) / (((k - 2 : ℕ) : ℝ)) := by
    simpa [b, A, mul_assoc, mul_left_comm, mul_comm] using hbn'
  refine ⟨n, hn, ?_⟩
  rw [generalized_conditional_gradient_norm_eq_coe_toReal hproblem htraj n]
  exact_mod_cast hfinal_real
omit hproblem hf_convex htraj hsteps hΩ

end
