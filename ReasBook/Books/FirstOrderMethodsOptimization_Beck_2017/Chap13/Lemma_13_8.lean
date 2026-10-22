/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_6
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Lemma_13_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {f : E → ℝ} {g : E → EReal}

local notation "F" => composite_model_objective f.toEReal g

/-- Helper for Lemma 13.8: the composite objective is finite at every point of `effective_domain g`
because the smooth term is real-valued and `g` does not take the value `⊥`. -/
lemma composite_model_objective_eq_coe_real_of_mem_effective_domain
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x : E} (hx : x ∈ effective_domain g) :
    F x = (((f x) + (g x).toReal : ℝ) : EReal) := by
  -- Rewrite the `g`-value through `toReal` so the composite value becomes an ordinary real cast.
  have hgx :
      (((g x).toReal : ℝ) : EReal) = g x :=
    EReal.coe_toReal (mem_effective_domain.mp hx).ne (hg_ne_bot x)
  -- The remaining algebra is just the pointwise expansion of the composite objective.
  rw [composite_model_objective_apply, ← hgx]
  simpa using (EReal.coe_add (f x) (g x).toReal).symm

/-- Helper for Lemma 13.8: every feasible composite objective value is the coercion of its real
`toReal` value. -/
lemma composite_model_objective_eq_coe_toReal_of_mem_effective_domain
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x : E} (hx : x ∈ effective_domain g) :
    F x = (((F x).toReal : ℝ) : EReal) := by
  -- First rewrite the finite objective value through the explicit real formula from the previous
  -- helper, then fold that formula back as the coercion of `toReal`.
  rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hg_ne_bot hx]
  exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm

/-- Helper for Lemma 13.8: every iterate of a generalized conditional-gradient trajectory stays in
`effective_domain g`. -/
lemma generalized_conditional_gradient_trajectory_mem_effective_domain
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    (hg_convex : is_convex_function g)
    {x p : ℕ → E} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t) :
    ∀ k : ℕ, x k ∈ effective_domain g := by
  intro k
  induction' k with k hk
  · -- The base point is feasible by the trajectory owner.
    exact htraj.zero_mem_effective_domain
  · -- The update is a convex combination of two feasible points.
    rcases is_generalized_conditional_gradient_trajectory_step htraj k with ⟨hp, hstep⟩
    have hpdom :
        p k ∈ effective_domain g :=
      generalized_conditional_gradient_argmin_mem_effective_domain hk hp
    have hcombo :
        (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k ∈ effective_domain g :=
      combo_mem_effective_domain_of_is_convex_function hg_convex hpdom hk (t k).2
    have hrewrite :
        x (k + 1) = (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k := by
      have hxscale :
          x k - (t k : ℝ) • x k = (1 - (t k : ℝ)) • x k := by
        simpa using (sub_smul (1 : ℝ) (t k : ℝ) (x k)).symm
      calc
        x (k + 1) = x k + (t k : ℝ) • (p k - x k) := hstep
        _ = x k + ((t k : ℝ) • p k - (t k : ℝ) • x k) := by rw [smul_sub]
        _ = (t k : ℝ) • p k + (x k - (t k : ℝ) • x k) := by
          abel
        _ = (t k : ℝ) • p k + (1 - (t k : ℝ)) • x k := by rw [hxscale]
    rw [hrewrite]
    exact hcombo

/-- Helper for Lemma 13.8: every feasible conditional-gradient trial point on the segment from
`x` to `p` remains in `effective_domain g`. -/
lemma conditional_gradient_trial_mem_effective_domain_of_mem_Icc
    (hg_convex : is_convex_function g)
    {x p : E} (hx : x ∈ effective_domain g) (hpdom : p ∈ effective_domain g)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    x + α • (p - x) ∈ effective_domain g := by
  -- Rewrite the affine trial point as the convex combination from Lemma 13.7, then use the
  -- convexity of `effective_domain g`.
  have hcombo :
      α • p + (1 - α) • x ∈ effective_domain g :=
    combo_mem_effective_domain_of_is_convex_function hg_convex hpdom hx hα
  simpa [conditional_gradient_segment_eq_convex_combo, add_comm, add_left_comm, add_assoc] using
    hcombo

/-- Helper for Lemma 13.8: the adaptive conditional-gradient stepsize always lies in `[0, 1]`
once the current gap value is nonnegative. -/
lemma conditional_gradient_adaptive_stepsize_mem_Icc
    {Sx : ℝ} (hSx : 0 ≤ Sx) (Lf : NNReal) (x p : E) :
    conditional_gradient_adaptive_stepsize Sx Lf x p ∈ Set.Icc (0 : ℝ) 1 := by
  -- Split the explicit fallback branch from the clipped-ratio branch in Definition 13.6.
  by_cases hdeg : ‖p - x‖ = 0 ∨ Lf = 0
  · simpa [Set.mem_Icc, conditional_gradient_adaptive_stepsize, if_pos hdeg] using
      (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by constructor <;> norm_num)
  · have hLf_nonneg : 0 ≤ (Lf : ℝ) := by
      exact_mod_cast Lf.2
    have hdiv_nonneg :
        0 ≤ Sx / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)) := by
      exact div_nonneg hSx (mul_nonneg hLf_nonneg (sq_nonneg ‖p - x‖))
    rw [Set.mem_Icc, conditional_gradient_adaptive_stepsize, if_neg hdeg]
    constructor
    · exact le_min zero_le_one hdiv_nonneg
    · exact min_le_left _ _

/-- Helper for Lemma 13.8: at a feasible search minimizer, the generalized conditional-gradient
norm is represented by the explicit real gap formula. -/
lemma generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x p : E} (hx : x ∈ effective_domain g) (hpdom : p ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    S[f, g](x) =
      (((inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal : ℝ)) : EReal) := by
  -- First rewrite the norm by the maximizing gap value at the chosen minimizer.
  rw [generalized_conditional_gradient_norm_eq_of_mem_argmin hp,
    generalized_conditional_gradient_gap_objective_apply]
  have hgx :
      (((g x).toReal : ℝ) : EReal) = g x :=
    EReal.coe_toReal (mem_effective_domain.mp hx).ne (hg_ne_bot x)
  have hgp :
      (((g p).toReal : ℝ) : EReal) = g p :=
    EReal.coe_toReal (mem_effective_domain.mp hpdom).ne (hg_ne_bot p)
  -- The gap value is then a cast of the displayed real expression.
  have hgap :
      (((inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal : ℝ)) : EReal) =
        ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) + g x - g p := by
    rw [EReal.coe_sub, EReal.coe_add, hgx, hgp]
  exact hgap.symm

/-- Helper for Lemma 13.8: the real-valued generalized conditional-gradient gap formula is the
`toReal` image of the canonical norm at a feasible minimizer. -/
lemma generalized_conditional_gradient_norm_toReal_eq_gap_real_of_mem_argmin
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x p : E} (hx : x ∈ effective_domain g) (hpdom : p ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    (S[f, g](x)).toReal =
      inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal := by
  -- Apply `toReal` to the finite `EReal` representation from the previous helper.
  rw [generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin
    hg_ne_bot hx hpdom hp]
  simpa using
    EReal.toReal_coe (inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal)

/-- Helper for Lemma 13.8: at a feasible argmin point, the generalized conditional-gradient norm
is the coercion of its real `toReal` value. -/
lemma generalized_conditional_gradient_norm_eq_coe_toReal_of_mem_argmin
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x p : E} (hx : x ∈ effective_domain g) (hpdom : p ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    S[f, g](x) = (((S[f, g](x)).toReal : ℝ) : EReal) := by
  -- Rewrite the norm by the explicit finite real gap formula, then read that formula back as a
  -- coercion of its `toReal`.
  rw [generalized_conditional_gradient_norm_eq_coe_gap_real_of_mem_argmin
    hg_ne_bot hx hpdom hp]
  exact (EReal.coe_toReal (EReal.coe_ne_top _) (EReal.coe_ne_bot _)).symm

/-- Helper for Lemma 13.8: argmin membership implies the real-valued linearized subproblem at `p`
is no larger than the comparison value at the base point `x`. -/
lemma generalized_conditional_gradient_subproblem_toReal_le_of_mem_argmin
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x p : E} (hx : x ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    inner ℝ (∇ f x) p + (g p).toReal ≤ inner ℝ (∇ f x) x + (g x).toReal := by
  -- Compare the minimizing value at `p` with the feasible comparison point `x`, then rewrite
  -- both finite `EReal` values as real coercions.
  have hpdom :
      p ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hx hp
  have hmin :
      generalized_conditional_gradient_subproblem f g x p ≤
        generalized_conditional_gradient_subproblem f g x x := by
    exact (isMinOn_univ_iff.mp (mem_generalized_conditional_gradient_argmin_iff.mp hp)) x
  have hgp :
      (((g p).toReal : ℝ) : EReal) = g p :=
    EReal.coe_toReal (mem_effective_domain.mp hpdom).ne (hg_ne_bot p)
  have hgx :
      (((g x).toReal : ℝ) : EReal) = g x :=
    EReal.coe_toReal (mem_effective_domain.mp hx).ne (hg_ne_bot x)
  have hleft :
      generalized_conditional_gradient_subproblem f g x p =
        (((inner ℝ (∇ f x) p + (g p).toReal : ℝ)) : EReal) := by
    rw [generalized_conditional_gradient_subproblem_apply, ← hgp, real_inner_comm]
    simpa using (EReal.coe_add (inner ℝ (∇ f x) p) (g p).toReal).symm
  have hright :
      generalized_conditional_gradient_subproblem f g x x =
        (((inner ℝ (∇ f x) x + (g x).toReal : ℝ)) : EReal) := by
    rw [generalized_conditional_gradient_subproblem_apply, ← hgx, real_inner_comm]
    simpa using (EReal.coe_add (inner ℝ (∇ f x) x) (g x).toReal).symm
  rw [hleft, hright] at hmin
  exact_mod_cast hmin

/-- Helper for Lemma 13.8: the generalized conditional-gradient norm is nonnegative at every
feasible argmin point. -/
lemma generalized_conditional_gradient_norm_toReal_nonneg_of_mem_argmin
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    {x p : E} (hx : x ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    0 ≤ (S[f, g](x)).toReal := by
  -- Compare the minimizing subproblem value with the base point, then rewrite the resulting real
  -- inequality as the explicit finite gap formula for `S[f, g](x)`.
  have hpdom :
      p ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hx hp
  have hsub :
      inner ℝ (∇ f x) p + (g p).toReal ≤ inner ℝ (∇ f x) x + (g x).toReal :=
    generalized_conditional_gradient_subproblem_toReal_le_of_mem_argmin
      hg_ne_bot hx hp
  have hgap_nonneg :
      0 ≤ inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal := by
    rw [inner_sub_right]
    linarith
  rw [generalized_conditional_gradient_norm_toReal_eq_gap_real_of_mem_argmin
    hg_ne_bot hx hpdom hp]
  exact hgap_nonneg

/-- Helper for Lemma 13.8: Lemma 13.7 becomes a real-valued inequality once all objective and
gap terms are normalized at feasible points. -/
lemma generalized_conditional_gradient_fundamental_inequality_toReal
    {Lf : NNReal}
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    (hg_convex : is_convex_function g)
    (hf_smooth_on_effective_domain_g : is_l_smooth_on f (effective_domain g) Lf)
    {x p : E} (hx : x ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (F (x + α • (p - x))).toReal ≤
      (F x).toReal - α * (S[f, g](x)).toReal +
        (((α ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ)) := by
  -- Route correction: normalize the `EReal` one-step estimate from Lemma 13.7 before the scalar
  -- case split, so the adaptive proof only manipulates real inequalities.
  have hpdom :
      p ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hx hp
  have htrial_dom :
      x + α • (p - x) ∈ effective_domain g :=
    conditional_gradient_trial_mem_effective_domain_of_mem_Icc
      hg_convex hx hpdom hα
  have hfund :
      F (x + α • (p - x)) ≤
        F x - (α : EReal) * S[f, g](x) +
          ((((α ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using
      (generalized_conditional_gradient_fundamental_inequality
        hg_ne_bot hg_convex hf_smooth_on_effective_domain_g hx hp hα)
  rw [composite_model_objective_eq_coe_toReal_of_mem_effective_domain
      hg_ne_bot htrial_dom,
    composite_model_objective_eq_coe_toReal_of_mem_effective_domain
      hg_ne_bot hx,
    generalized_conditional_gradient_norm_eq_coe_toReal_of_mem_argmin
      hg_ne_bot hx hpdom hp,
    ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add] at hfund
  exact_mod_cast hfund

/-- Helper for Lemma 13.8: the adaptive trial point
`x + s (p - x)` with
`s = conditional_gradient_adaptive_stepsize (S[f, g](x)).toReal Lf x p`
satisfies the textbook sufficient-decrease bound. -/
theorem generalized_conditional_gradient_adaptive_trial_sufficient_decrease
    {Lf : NNReal}
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    (hg_convex : is_convex_function g)
    (hf_smooth_on_effective_domain_g : is_l_smooth_on f (effective_domain g) Lf)
    {Ω : ℝ}
    (hΩ : ∀ u ∈ effective_domain g, ∀ v ∈ effective_domain g, ‖u - v‖ ≤ Ω)
    {x p : E} (hx : x ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    let s := conditional_gradient_adaptive_stepsize (S[f, g](x)).toReal Lf x p
    F x - F (x + s • (p - x)) ≥
      ((1 / 2 : ℝ) *
          min ((S[f, g](x)).toReal)
            ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) : EReal) := by
  -- Route correction: follow the textbook proof literally. Evaluate Lemma 13.7 at the adaptive
  -- trial scalar, split on the adaptive definition, and then insert the diameter bound.
  dsimp
  have hpdom :
      p ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hx hp
  have hS_nonneg :
      0 ≤ (S[f, g](x)).toReal :=
    generalized_conditional_gradient_norm_toReal_nonneg_of_mem_argmin
      hg_ne_bot hx hp
  set s : ℝ := conditional_gradient_adaptive_stepsize (S[f, g](x)).toReal Lf x p with hs
  have hs_mem :
      s ∈ Set.Icc (0 : ℝ) 1 := by
    -- The adaptive scalar is an admissible comparison point on `[0, 1]`.
    rw [hs]
    exact conditional_gradient_adaptive_stepsize_mem_Icc
      hS_nonneg Lf x p
  have htrial_dom :
      x + s • (p - x) ∈ effective_domain g :=
    conditional_gradient_trial_mem_effective_domain_of_mem_Icc
      hg_convex hx hpdom hs_mem
  have hfund :
      (F (x + s • (p - x))).toReal ≤
        (F x).toReal - s * (S[f, g](x)).toReal +
          (((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ)) := by
    -- This is equation (13.8) after normalizing all finite `EReal` values to reals.
    simpa [hs] using
      generalized_conditional_gradient_fundamental_inequality_toReal
        hg_ne_bot hg_convex hf_smooth_on_effective_domain_g hx hp hs_mem
  have hmodel :
      s * (S[f, g](x)).toReal -
          (((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ)) ≤
        (F x).toReal - (F (x + s • (p - x))).toReal := by
    -- Rearranging the real one-step inequality isolates the decrease term on the right.
    linarith
  have htarget_real :
      (1 / 2 : ℝ) *
          min ((S[f, g](x)).toReal)
            ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) ≤
        (F x).toReal - (F (x + s • (p - x))).toReal := by
    by_cases hdeg : ‖p - x‖ = 0 ∨ Lf = 0
    · rcases hdeg with hnorm | hLf
      · -- If `p = x`, the trial point is `x` itself and the generalized gap vanishes.
        have hpx : p = x := by
          exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
        have hs_eq : s = 1 := by
          rw [hs]
          simp [conditional_gradient_adaptive_stepsize, hnorm]
        have hgap_zero :
            (S[f, g](x)).toReal = 0 := by
          rw [generalized_conditional_gradient_norm_toReal_eq_gap_real_of_mem_argmin
            hg_ne_bot hx hpdom hp, hpx]
          simp
        have htrial_eq :
            x + s • (p - x) = x := by
          rw [hs_eq, hpx]
          simp
        simp [hgap_zero, htrial_eq]
      · -- If `L_f = 0`, the second term in the textbook minimum is zero, so nonnegativity
        -- of the decrease is enough.
        have hs_eq : s = 1 := by
          rw [hs]
          simp [conditional_gradient_adaptive_stepsize, hLf]
        have htarget_zero :
            (1 / 2 : ℝ) *
                min ((S[f, g](x)).toReal)
                  ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) = 0 := by
          simp [hLf, hS_nonneg]
        rw [htarget_zero]
        have hdecrease_nonneg :
            0 ≤ (F x).toReal - (F (x + s • (p - x))).toReal := by
          have htrial_le_gap :
              (F (x + s • (p - x))).toReal ≤ (F x).toReal - (S[f, g](x)).toReal := by
            simpa [hs_eq, hLf] using hfund
          have htrial_le :
              (F (x + s • (p - x))).toReal ≤ (F x).toReal := by
            linarith [htrial_le_gap, hS_nonneg]
          linarith
        exact hdecrease_nonneg
    · have hp_ne : p ≠ x := by
        intro hpx
        exact hdeg (Or.inl (by simpa [hpx]))
      have hLf_ne : Lf ≠ 0 := by
        intro hLf
        exact hdeg (Or.inr hLf)
      have hLf_pos : 0 < (Lf : ℝ) := by
        exact_mod_cast (show (0 : NNReal) < Lf from pos_iff_ne_zero.mpr hLf_ne)
      have hnorm_ne : ‖p - x‖ ≠ 0 := by
        intro hnorm
        exact hdeg (Or.inl hnorm)
      have hnorm_pos : 0 < ‖p - x‖ := by
        exact lt_of_le_of_ne (norm_nonneg (p - x)) hnorm_ne.symm
      have hden_pos :
          0 < (Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ) := by
        exact mul_pos hLf_pos (pow_pos hnorm_pos _)
      have hs_eq :
          s = min (1 : ℝ)
            ((S[f, g](x)).toReal / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) := by
        rw [hs]
        exact conditional_gradient_adaptive_stepsize_of_ne
          (S[f, g](x)).toReal hp_ne hLf_ne
      by_cases hratio :
          (S[f, g](x)).toReal / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)) ≤ 1
      · -- On the clipped-ratio branch, the textbook estimate is the quadratic one.
        have hs_ratio :
            s = (S[f, g](x)).toReal / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)) := by
          rw [hs_eq, min_eq_right hratio]
        have hcase_norm :
            (1 / 2 : ℝ) *
                ((S[f, g](x)).toReal ^ (2 : ℕ) /
                  ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) ≤
              (F x).toReal - (F (x + s • (p - x))).toReal := by
          have hcore :
              (1 / 2 : ℝ) *
                  ((S[f, g](x)).toReal ^ (2 : ℕ) /
                    ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ))) =
                s * (S[f, g](x)).toReal -
                  (((s ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ)) := by
            rw [hs_ratio]
            field_simp [hden_pos.ne']
            ring
          rw [hcore]
          exact hmodel
        have hΩ_nonneg : 0 ≤ Ω := by
          simpa using hΩ x hx x hx
        have hnorm_le : ‖p - x‖ ≤ Ω := by
          simpa [norm_sub_rev] using hΩ x hx p hpdom
        have hsq_le :
            ‖p - x‖ ^ (2 : ℕ) ≤ Ω ^ (2 : ℕ) := by
          nlinarith [hnorm_le, norm_nonneg (p - x), hΩ_nonneg]
        have hden_le :
            (Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ) ≤ (Lf : ℝ) * Ω ^ (2 : ℕ) := by
          exact mul_le_mul_of_nonneg_left hsq_le hLf_pos.le
        have hquad_compare :
            (S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ)) ≤
              (S[f, g](x)).toReal ^ (2 : ℕ) /
                ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)) := by
          exact div_le_div_of_nonneg_left
            (sq_nonneg ((S[f, g](x)).toReal)) hden_pos hden_le
        have htarget_le_quad :
            (1 / 2 : ℝ) *
                min ((S[f, g](x)).toReal)
                  ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) ≤
              (1 / 2 : ℝ) *
                ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) := by
          exact mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
        have hquad_bound :
            (1 / 2 : ℝ) *
                ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) ≤
              (F x).toReal - (F (x + s • (p - x))).toReal := by
          exact le_trans
            (mul_le_mul_of_nonneg_left hquad_compare (by norm_num))
            hcase_norm
        exact le_trans htarget_le_quad hquad_bound
      · -- On the branch `ratio ≥ 1`, the textbook estimate is the linear one.
        have hratio_ge :
            1 ≤ (S[f, g](x)).toReal / ((Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ)) := by
          linarith
        have hs_one : s = 1 := by
          rw [hs_eq, min_eq_left hratio_ge]
        have hden_le_gap :
            (Lf : ℝ) * ‖p - x‖ ^ (2 : ℕ) ≤ (S[f, g](x)).toReal := by
          exact (one_le_div₀ hden_pos).mp hratio_ge
        have hlinear_bound :
            (1 / 2 : ℝ) * (S[f, g](x)).toReal ≤
              (F x).toReal - (F (x + s • (p - x))).toReal := by
          have hstep_bound :
              (S[f, g](x)).toReal -
                  (((1 ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ)) ≤
                (F x).toReal - (F (x + s • (p - x))).toReal := by
            simpa [hs_one] using hmodel
          have hhalf_le :
              (1 / 2 : ℝ) * (S[f, g](x)).toReal ≤
                (S[f, g](x)).toReal -
                  (((1 ^ (2 : ℕ) * (Lf : ℝ)) / 2) * ‖p - x‖ ^ (2 : ℕ)) := by
            nlinarith
          exact le_trans hhalf_le hstep_bound
        have htarget_le_linear :
            (1 / 2 : ℝ) *
                min ((S[f, g](x)).toReal)
                  ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) ≤
              (1 / 2 : ℝ) * (S[f, g](x)).toReal := by
          exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
        exact le_trans htarget_le_linear hlinear_bound
  -- Convert the real sufficient-decrease estimate back to the `EReal` statement.
  have hdecrease_ereal :
      (((F x).toReal - (F (x + s • (p - x))).toReal : ℝ) : EReal) ≥
        ((1 / 2 : ℝ) *
            min ((S[f, g](x)).toReal)
              ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) : EReal) := by
    exact_mod_cast htarget_real
  let Fx : ℝ := (F x).toReal
  let Ftrial : ℝ := (F (x + s • (p - x))).toReal
  have hFx :
      F x = ((Fx : ℝ) : EReal) := by
    dsimp [Fx]
    exact composite_model_objective_eq_coe_toReal_of_mem_effective_domain hg_ne_bot hx
  have hFtrial :
      F (x + s • (p - x)) = ((Ftrial : ℝ) : EReal) := by
    dsimp [Ftrial]
    exact composite_model_objective_eq_coe_toReal_of_mem_effective_domain hg_ne_bot htrial_dom
  calc
    F x - F (x + s • (p - x)) =
        (((Fx : ℝ) : EReal) - ((Ftrial : ℝ) : EReal)) := by
          rw [hFx, hFtrial]
    _ = (((Fx - Ftrial : ℝ)) : EReal) := by
          simpa using (EReal.coe_sub Fx Ftrial).symm
    _ ≥
        ((1 / 2 : ℝ) *
            min ((S[f, g](x)).toReal)
              ((S[f, g](x)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) : EReal) :=
        by simpa [Fx, Ftrial] using hdecrease_ereal

/- This lemma is `source-facing`: it gives the one-step decrease bound for the generalized
conditional-gradient method under the two textbook stepsize choices. Domain sampling in the
surrounding Chapter 13 files shows that the relevant owners already exist upstream:

- `is_generalized_conditional_gradient_trajectory` from Algorithm 13.2 for the iterate/search
  point update data;
- `uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule` from Definition 13.6
  for the admissible stepsize choice;
- `generalized_conditional_gradient_norm`, written `S[f, g](x)`, from Text 13.2 for the chapter
  gap quantity;
- `generalized_conditional_gradient_fundamental_inequality` from Lemma 13.7 for the canonical
  one-step descent bridge.

The theorem therefore keeps only the primitive source data not already owned upstream: the
convexity/no-`⊥` hypotheses on `g`, the smoothness of `f` on `effective_domain g`, and the
explicit diameter bound `Ω` on `effective_domain g`. The descent estimate itself is then expressed
through the canonical Chapter 13 owners above, with
`F = composite_model_objective f.toEReal g` as the ambient objective surface. -/

-- Proof sketch: let `Sₖ = (generalized_conditional_gradient_gap_objective f g (x k) (p k)).toReal`
-- and apply the Chapter 13 one-step fundamental inequality to the segment
-- `x k + u • (p k - x k)`, where the chosen point `p k` is recovered from the trajectory owner.
-- In the adaptive branch, unfold the Definition 13.6 owner to substitute
-- `tₖ = min {1, Sₖ / (L_f ‖p k - x k‖²)}` and split into the two textbook cases. Use the
-- diameter bound on `effective_domain g` to replace `‖p k - x k‖²` by `Ω²`. In the exact
-- line-search branch, compare the minimizing step `tₖ` with the same adaptive candidate to obtain
-- the identical lower bound. Finally rewrite the chosen-point gap as the canonical quantity
-- `S[f, g](x k)` using `generalized_conditional_gradient_norm_eq_of_mem_argmin`.
/-- Lemma 13.8: if `g : E → (-∞, ∞]` is convex, `f` is `L_f`-smooth on `dom(g)`, `x⁰ ∈ dom(g)`,
each `pᵏ ∈ arg min_p {⟪p, ∇ f(xᵏ)⟫ + g(p)}`, and
`xᵏ⁺¹ = xᵏ + tₖ (pᵏ - xᵏ)` with stepsizes chosen either by the adaptive rule or by exact line
search, then every one-step objective decrease is at least
`(1 / 2) * min {S(xᵏ), S(xᵏ)^2 / (L_f Ω^2)}`, where `S(xᵏ) = (S[f, g](x k)).toReal` and `Ω`
bounds the diameter of `dom(g)`. Here `F = composite_model_objective f.toEReal g`. The textbook
codomain restriction is represented explicitly by `hg_ne_bot : ∀ y, g y ≠ ⊥`. -/
theorem generalized_conditional_gradient_sufficient_decrease_of_adaptive_or_exact_line_search
    {Lf : NNReal}
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    (hg_convex : is_convex_function g)
    (hf_smooth_on_effective_domain_g : is_l_smooth_on f (effective_domain g) Lf)
    {x p : ℕ → E} {t : ℕ → Set.Icc (0 : ℝ) 1}
    (htraj : is_generalized_conditional_gradient_trajectory f g x p t)
    (hrule : uses_generalized_conditional_gradient_adaptive_or_exact_stepsize_rule f g Lf x p t)
    {Ω : ℝ}
    (hΩ : ∀ u ∈ effective_domain g, ∀ v ∈ effective_domain g, ‖u - v‖ ≤ Ω)
    (k : ℕ) :
    F (x k) - F (x (k + 1)) ≥
      ((1 / 2 : ℝ) *
          min ((S[f, g](x k)).toReal)
            ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) : EReal) := by
  -- First keep the iterate and the chosen search point inside the feasible domain.
  have hxk :
      x k ∈ effective_domain g :=
    generalized_conditional_gradient_trajectory_mem_effective_domain
      hg_ne_bot hg_convex htraj k
  have hpk :
      p k ∈ generalized_conditional_gradient_argmin f g (x k) :=
    htraj.argmin_mem k
  have hpk_dom :
      p k ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hxk hpk
  have hS_nonneg : 0 ≤ (S[f, g](x k)).toReal := by
    -- The chosen gap is nonnegative because the search point minimizes the linearized subproblem.
    exact generalized_conditional_gradient_norm_toReal_nonneg_of_mem_argmin
      hg_ne_bot hxk hpk
  let s : ℝ := conditional_gradient_adaptive_stepsize (S[f, g](x k)).toReal Lf (x k) (p k)
  let xTilde : E := x k + s • (p k - x k)
  have hs_mem :
      s ∈ Set.Icc (0 : ℝ) 1 := by
    -- The adaptive comparison scalar is a feasible exact-line-search comparison point.
    dsimp [s]
    exact conditional_gradient_adaptive_stepsize_mem_Icc hS_nonneg Lf (x k) (p k)
  have htrial :
      F (x k) - F xTilde ≥
        ((1 / 2 : ℝ) *
            min ((S[f, g](x k)).toReal)
              ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) : EReal) := by
    -- This is the source proof's core trial-point estimate (13.10).
    simpa [s, xTilde] using
      generalized_conditional_gradient_adaptive_trial_sufficient_decrease
        hg_ne_bot hg_convex hf_smooth_on_effective_domain_g hΩ hxk hpk
  rcases hrule with hadapt | hexact
  · -- Under the adaptive rule, the trial point is exactly the next iterate.
    rcases hadapt k with ⟨_, _, htk_eq⟩
    have hstep_eq :
        x (k + 1) = xTilde := by
      dsimp [xTilde, s]
      rw [htraj.step_eq k, htk_eq]
      rfl
    rw [hstep_eq]
    exact htrial
  · -- Under exact line search, the next iterate does at least as well as the adaptive trial point.
    have hexactk := hexact k
    rw [mem_conditional_gradient_exact_line_search_stepsizes_iff, isMinOn_iff] at hexactk
    rcases hexactk with ⟨_, hmin⟩
    have hstep_compare :
        F (x (k + 1)) ≤ F xTilde := by
      have hcompare :
          F (x k + (t k : ℝ) • (p k - x k)) ≤ F xTilde :=
        hmin s hs_mem
      simpa [xTilde, htraj.step_eq k] using hcompare
    have hxTilde :
        xTilde ∈ effective_domain g := by
      dsimp [xTilde]
      exact conditional_gradient_trial_mem_effective_domain_of_mem_Icc
        hg_convex hxk hpk_dom hs_mem
    have hxnext :
        x (k + 1) ∈ effective_domain g :=
      generalized_conditional_gradient_trajectory_mem_effective_domain
        hg_ne_bot hg_convex htraj (k + 1)
    have hcompare_real :
        (F (x (k + 1))).toReal ≤ (F xTilde).toReal :=
      EReal.toReal_le_toReal hstep_compare
        (by
          rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hg_ne_bot hxnext]
          exact EReal.coe_ne_bot _)
        (by
          rw [composite_model_objective_eq_coe_real_of_mem_effective_domain hg_ne_bot hxTilde]
          exact EReal.coe_ne_top _)
    have htrial_real :
        (1 / 2 : ℝ) *
            min ((S[f, g](x k)).toReal)
              ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) ≤
          (F (x k)).toReal - (F xTilde).toReal := by
      let Fxk : ℝ := (F (x k)).toReal
      let FxTilde : ℝ := (F xTilde).toReal
      have hFxk :
          F (x k) = ((Fxk : ℝ) : EReal) := by
        dsimp [Fxk]
        exact composite_model_objective_eq_coe_toReal_of_mem_effective_domain hg_ne_bot hxk
      have hFxTilde :
          F xTilde = ((FxTilde : ℝ) : EReal) := by
        dsimp [FxTilde]
        exact composite_model_objective_eq_coe_toReal_of_mem_effective_domain hg_ne_bot hxTilde
      have htrial_coe :
          (((Fxk - FxTilde : ℝ)) : EReal) ≥
            ((1 / 2 : ℝ) *
                min ((S[f, g](x k)).toReal)
                  ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) :
              EReal) := by
        calc
          (((Fxk - FxTilde : ℝ)) : EReal) =
              F (x k) - F xTilde := by
                rw [hFxk, hFxTilde, ← EReal.coe_sub]
          _ ≥
              ((1 / 2 : ℝ) *
                  min ((S[f, g](x k)).toReal)
                    ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) :
                EReal) :=
              htrial
      exact_mod_cast htrial_coe
    have hgoal_real :
        (1 / 2 : ℝ) *
            min ((S[f, g](x k)).toReal)
              ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) ≤
          (F (x k)).toReal - (F (x (k + 1))).toReal := by
      linarith
    let Fxk : ℝ := (F (x k)).toReal
    let Fxnext : ℝ := (F (x (k + 1))).toReal
    have hFxk :
        F (x k) = ((Fxk : ℝ) : EReal) := by
      dsimp [Fxk]
      exact composite_model_objective_eq_coe_toReal_of_mem_effective_domain hg_ne_bot hxk
    have hFxnext :
        F (x (k + 1)) = ((Fxnext : ℝ) : EReal) := by
      dsimp [Fxnext]
      exact composite_model_objective_eq_coe_toReal_of_mem_effective_domain hg_ne_bot hxnext
    have hgoal_ereal :
        (((Fxk - Fxnext : ℝ)) : EReal) ≥
          ((1 / 2 : ℝ) *
              min ((S[f, g](x k)).toReal)
                ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) :
            EReal) := by
      simpa [Fxk, Fxnext] using (show
        (((F (x k)).toReal - (F (x (k + 1))).toReal : ℝ) : EReal) ≥
          ((1 / 2 : ℝ) *
              min ((S[f, g](x k)).toReal)
                ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) :
            EReal) by
          exact_mod_cast hgoal_real)
    calc
      F (x k) - F (x (k + 1)) =
          (((Fxk : ℝ) : EReal) - ((Fxnext : ℝ) : EReal)) := by
            rw [hFxk, hFxnext]
      _ = (((Fxk - Fxnext : ℝ)) : EReal) := by
            simpa using (EReal.coe_sub Fxk Fxnext).symm
      _ ≥
          ((1 / 2 : ℝ) *
              min ((S[f, g](x k)).toReal)
                ((S[f, g](x k)).toReal ^ (2 : ℕ) / ((Lf : ℝ) * Ω ^ (2 : ℕ))) :
            EReal) :=
          hgoal_ereal

end
