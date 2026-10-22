/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Remark 10.13 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `is_backtracking_procedure_B1_index` from Algorithm 10.2 is the owner for the output of
  backtracking procedure B1;
- `proximal_gradient_backtracking_trial_stepsize` is the canonical trial curvature `s η^i`;
- `proximal_gradient_backtracking_accepts` is the exact sufficient-decrease test from the source;
- the inclusion `effective_domain g ⊆ interior (effective_domain f)` is the canonical bridge from
  the source-facing iterate condition `x ∈ effective_domain g` to the interior-domain operator
  API;
- `prox_grad_sufficient_decrease` from Lemma 10.4 is the descent estimate behind the finiteness
  threshold.

The source has two independent conclusions, so the item is split into two atomic theorem
skeletons. The textbook assumptions that `f` is convex or lower semicontinuous are omitted because
the descent estimate used here already has the semantically minimal hypotheses recorded in
Lemma 10.4. -/

variable (f g : E → EReal) (Lf : NNReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
variable [Fact (is_convex_function g)]
variable (hg_effective_domain_subset_interior_f_effective_domain :
  effective_domain g ⊆ interior (effective_domain f))
variable (s : PosReal) (γ : ProximalGradientBacktrackingDecreaseFraction)
variable (η : ProximalGradientBacktrackingGrowthFactor) (x : effective_domain g)

/-- Helper for Remark 10.13: the prox-gradient update lies in the effective domain of `g`. -/
lemma prox_grad_update_mem_effective_domain_g
    (L : PosReal)
    (y : interior (effective_domain f)) :
    T[L, f, g] y ∈ effective_domain g := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  have hprox :
      prox[((((1 / L : PosReal) : EReal) • g))]
        ((y : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (y : E)) =
          {T[L, f, g] y} := by
    -- Expand the prox-gradient update back to the singleton proximal step.
    simpa [proximal_gradient_step] using prox_grad_operator_eq_singleton f g L y
  rcases prox_singleton_implies_effective_domain_and_inner_support
      ((((1 / L : PosReal) : EReal) • g))
      hg_scaled.1
      hg_scaled.2.2
      ((y : E) - (1 / L : ℝ) • ∇ (fun z ↦ (f z).toReal) (y : E))
      (T[L, f, g] y)
      hprox with
    ⟨hyPlus_eff_scaled, _⟩
  -- Finiteness for `(1 / L) • g` is equivalent to finiteness for `g`.
  exact
    (mem_effective_domain_scaled_function_iff g (1 / L) inferInstance (T[L, f, g] y)).mp
      hyPlus_eff_scaled

/-- Helper for Remark 10.13: the singleton proximal support inequality controls the smooth
linear term in real-valued form. -/
lemma prox_grad_support_controls_linear_term
    (L : PosReal)
    (y : interior (effective_domain f))
    (hyg : (y : E) ∈ effective_domain g) :
    inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (T[L, f, g] y - (y : E)) ≤
      -(L : ℝ) * ‖T[L, f, g] y - (y : E)‖ ^ (2 : ℕ) +
        (g (y : E)).toReal - (g (T[L, f, g] y)).toReal := by
  let yPlus : E := T[L, f, g] y
  let z : E := (y : E) - (1 / L : ℝ) • ∇ (fun w ↦ (f w).toReal) (y : E)
  let hg_convex : is_convex_function g := Fact.out
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hprox : prox[((((1 / L : PosReal) : EReal) • g))] z = {yPlus} := by
    -- The prox-gradient update is the singleton proximal point of the scaled penalty.
    simpa [yPlus, z, proximal_gradient_step] using prox_grad_operator_eq_singleton f g L y
  rcases scaled_prox_singleton_support_of_proper_convex
      g (1 / L) inferInstance hg_convex z yPlus hprox with
    ⟨hyPlus_eff, hsupport⟩
  have hy_val :
      g (y : E) = (((g (y : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hyg).ne (hg_proper.ne_bot _)).symm
  have hyPlus_val :
      g yPlus = (((g yPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hyPlus_eff).ne (hg_proper.ne_bot _)).symm
  have hsupport_real :
      inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - yPlus)) ((y : E) - yPlus) ≤
        (g (y : E)).toReal - (g yPlus).toReal := by
    have hsupportE := hsupport (y : E) hyg
    rw [hy_val, hyPlus_val] at hsupportE
    have hsupportE' :
        (((inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - yPlus)) ((y : E) - yPlus) : ℝ)) :
            EReal) ≤
          ((((g (y : E)).toReal - (g yPlus).toReal : ℝ)) : EReal) := by
      simpa [EReal.coe_sub] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hLinv : (1 / (1 / L : PosReal) : ℝ) = (L : ℝ) := by
    simp [PosReal.coe_inv]
  have hleft :
      inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - yPlus)) ((y : E) - yPlus) =
        (L : ℝ) * ‖(y : E) - yPlus‖ ^ (2 : ℕ) -
          inner ℝ (∇ (fun w ↦ (f w).toReal) (y : E)) ((y : E) - yPlus) := by
    -- Expanding the forward point isolates the residual square and the linear gradient term.
    have hz_sub :
        z - yPlus = ((y : E) - yPlus) - (1 / L : ℝ) • ∇ (fun w ↦ (f w).toReal) (y : E) := by
      dsimp [z]
      abel
    rw [hLinv, hz_sub, smul_sub, inner_sub_left]
    have hnorm :
        inner ℝ ((L : ℝ) • ((y : E) - yPlus)) ((y : E) - yPlus) =
          (L : ℝ) * ‖(y : E) - yPlus‖ ^ (2 : ℕ) := by
      calc
        inner ℝ ((L : ℝ) • ((y : E) - yPlus)) ((y : E) - yPlus) =
            (starRingEnd ℝ) (L : ℝ) * inner ℝ ((y : E) - yPlus) ((y : E) - yPlus) := by
          rw [inner_smul_left]
        _ = (L : ℝ) * ‖(y : E) - yPlus‖ ^ (2 : ℕ) := by
          simp [real_inner_self_eq_norm_sq]
    have hL0 : (L : ℝ) ≠ 0 := (PosReal.coe_pos L).ne'
    have hcancel : (L : ℝ) * (1 / L : ℝ) = 1 := by
      field_simp [hL0]
    have hgrad :
        inner ℝ ((L : ℝ) • ((1 / L : ℝ) • ∇ (fun w ↦ (f w).toReal) (y : E))) ((y : E) - yPlus) =
          inner ℝ (∇ (fun w ↦ (f w).toReal) (y : E)) ((y : E) - yPlus) := by
      rw [smul_smul, hcancel, one_smul]
    rw [hnorm, hgrad]
  have haux :
      -inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) ((y : E) - yPlus) ≤
        -(L : ℝ) * ‖(y : E) - yPlus‖ ^ (2 : ℕ) +
          (g (y : E)).toReal - (g yPlus).toReal := by
    rw [hleft] at hsupport_real
    linarith
  have hdir :
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (yPlus - (y : E)) =
        -inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) ((y : E) - yPlus) := by
    have hsub : yPlus - (y : E) = -((y : E) - yPlus) := by
      abel
    rw [hsub, inner_neg_right]
  -- Rewrite the displacement as the negative residual direction.
  simpa [yPlus, hdir, norm_sub_rev] using haux

/-- Helper for Remark 10.13: the gradient-mapping norm is the residual norm multiplied by
`L^2`. -/
lemma gradient_mapping_norm_sq_eq_scaled_step_norm_sq
    (L : PosReal)
    (y : interior (effective_domain f)) :
    ‖G[L, f, g] y‖ ^ (2 : ℕ) =
      (L : ℝ) ^ (2 : ℕ) * ‖((y : E) - T[L, f, g] y)‖ ^ (2 : ℕ) := by
  -- Expand `G_L(y) = L • (y - T_L(y))` and square the norm.
  rw [gradient_mapping_apply, norm_smul, Real.norm_eq_abs, abs_of_pos L.2, pow_two, pow_two]
  ring

/-- Helper for Remark 10.13: the one-step prox-gradient decrease estimate holds at any
`x ∈ effective_domain g`, viewed through the induced point of `interior (effective_domain f)`. -/
lemma prox_grad_effective_domain_sufficient_decrease
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (L : PosReal) :
    let xInterior : interior (effective_domain f) :=
      ⟨(x : E), hg_effective_domain_subset_interior_f_effective_domain x.property⟩
    ((((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) *
        ‖G[L, f, g] xInterior‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
      composite_model_objective f g (x : E) -
        composite_model_objective f g (T[L, f, g] xInterior) := by
  -- Route correction: replace the broken imported Lemma 10.4 dependency with the same
  -- Chapter 5 + Chapter 6 descent argument localized to the current effective-domain point.
  let xInterior : interior (effective_domain f) :=
    ⟨(x : E), hg_effective_domain_subset_interior_f_effective_domain x.property⟩
  let xPlus : E := T[L, f, g] xInterior
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hx_eff_f : (xInterior : E) ∈ effective_domain f := interior_subset xInterior.property
  have hxPlus_eff_g : xPlus ∈ effective_domain g := by
    -- The prox-gradient update stays finite for `g`, so both objective terms are real-valued.
    simpa [xPlus] using prox_grad_update_mem_effective_domain_g f g L xInterior
  have hxPlus_int_f : xPlus ∈ interior (effective_domain f) := by
    exact hg_effective_domain_subset_interior_f_effective_domain hxPlus_eff_g
  have hxPlus_eff_f : xPlus ∈ effective_domain f := interior_subset hxPlus_int_f
  have hfx_val :
      f (x : E) = (((f (x : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hx_eff_f).ne (hf_ne_bot _)).symm
  have hfxPlus_val :
      f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_f).ne (hf_ne_bot _)).symm
  have hgx_val :
      g (x : E) = (((g (x : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp x.property).ne (hg_proper.ne_bot _)).symm
  have hgxPlus_val :
      g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_g).ne (hg_proper.ne_bot _)).symm
  have hdescent :
      (f xPlus).toReal ≤
        (f (x : E)).toReal +
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) +
          ((Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
    -- Apply the smooth descent lemma to the current point and its realized prox-gradient update.
    simpa [xInterior, xPlus, norm_sub_rev] using
      (is_l_smooth_on_descent_lemma
        hf_effective_domain_convex.interior
        hf_toReal_smooth_on_interior_effective_domain
        xInterior.property
        hxPlus_int_f)
  have hlinear :
      inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) ≤
        -(L : ℝ) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) +
          (g (x : E)).toReal - (g xPlus).toReal := by
    -- The Chapter 6 prox-support inequality controls the linear model error.
    simpa [xInterior, xPlus] using
      prox_grad_support_controls_linear_term f g L xInterior x.property
  have hgap_real :
      ((L : ℝ) - (Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) ≤
        (f (x : E)).toReal + (g (x : E)).toReal -
          ((f xPlus).toReal + (g xPlus).toReal) := by
    -- Adding the smoothness and prox-support estimates yields the one-step objective gap.
    linarith
  have hcoeff_real :
      (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) * ‖G[L, f, g] xInterior‖ ^ (2 : ℕ)) =
        ((L : ℝ) - (Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
    rw [gradient_mapping_norm_sq_eq_scaled_step_norm_sq f g L xInterior]
    have hL0 : (L : ℝ) ≠ 0 := (PosReal.coe_pos L).ne'
    rw [pow_two]
    have hnorm :
        ‖(xInterior : E) - T[L, f, g] xInterior‖ ^ (2 : ℕ) =
          ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
      simpa [xInterior, xPlus, norm_sub_rev]
    rw [hnorm]
    field_simp [hL0]
  have hFx :
      composite_model_objective f g (x : E) =
        ((((f (x : E)).toReal + (g (x : E)).toReal : ℝ)) : EReal) := by
    -- At the base point, both objective terms are finite real values.
    rw [composite_model_objective_apply]
    conv_lhs =>
      rw [hfx_val, hgx_val]
    rw [EReal.coe_add]
  have hFxPlus :
      composite_model_objective f g xPlus =
        ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
    -- The same finite-value expansion holds at the realized update.
    rw [composite_model_objective_apply]
    conv_lhs =>
      rw [hfxPlus_val, hgxPlus_val]
    rw [EReal.coe_add]
  have hFgap :
      composite_model_objective f g (x : E) - composite_model_objective f g xPlus =
        ((((f (x : E)).toReal + (g (x : E)).toReal) -
            ((f xPlus).toReal + (g xPlus).toReal) : ℝ) : EReal) := by
    rw [hFx, hFxPlus, EReal.coe_sub]
  have hgoal :
      ((((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) *
          ‖G[L, f, g] xInterior‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        composite_model_objective f g (x : E) -
          composite_model_objective f g xPlus := by
    -- After rewriting both sides to the same real-valued gap, the result is exactly `hgap_real`.
    rw [hFgap, hcoeff_real]
    exact EReal.coe_le_coe_iff.mpr hgap_real
  -- Rewrite the objective gap and the residual coefficient into the same real-valued expression.
  simpa [xInterior, xPlus] using hgoal

/-- Helper for Remark 10.13: any trial curvature above the smoothness threshold
`L_f / (2 * (1 - γ))` satisfies the B1 sufficient-decrease test. -/
lemma backtracking_accepts_of_stepsize_ge_smoothness_threshold
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    (L : PosReal)
    (hthreshold : (Lf : ℝ) / (2 * (1 - (γ : ℝ))) ≤ (L : ℝ)) :
    proximal_gradient_backtracking_accepts
      f g γ L
      hg_effective_domain_subset_interior_f_effective_domain x := by
  let xInterior : interior (effective_domain f) :=
    ⟨(x : E), hg_effective_domain_subset_interior_f_effective_domain x.property⟩
  -- Lemma 10.4 gives the descent estimate at the interior-domain point induced by `x`.
  have hdecrease :
      ((((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) *
          ‖G[L, f, g] xInterior‖ ^ (2 : ℕ) : ℝ) : EReal) ≤
        composite_model_objective f g (x : E) -
          composite_model_objective f g (T[L, f, g] xInterior) := by
    simpa [xInterior] using
      prox_grad_effective_domain_sufficient_decrease
        f g Lf
        hg_effective_domain_subset_interior_f_effective_domain
        x
        hf_ne_bot
        hf_effective_domain_convex
        hf_toReal_smooth_on_interior_effective_domain
        L
  let residual : ℝ := ‖G[L, f, g] xInterior‖ ^ (2 : ℕ)
  have hresidual_nonneg : 0 ≤ residual := by
    -- The squared norm factor is nonnegative, so coefficient comparison lifts through it.
    dsimp [residual]
    positivity
  have hL_pos : 0 < (L : ℝ) := L.2
  have hL_sq_nonneg : 0 ≤ (L : ℝ) ^ (2 : ℕ) := by
    positivity
  have hγ_lt_one : (γ : ℝ) < 1 := γ.2
  have hdenom_pos : 0 < 2 * (1 - (γ : ℝ)) := by
    nlinarith
  have hthreshold_mul : (Lf : ℝ) ≤ (L : ℝ) * (2 * (1 - (γ : ℝ))) := by
    exact (div_le_iff₀ hdenom_pos).1 hthreshold
  have hlinear :
      (γ : ℝ) * (L : ℝ) ≤ (L : ℝ) - (Lf : ℝ) / 2 := by
    -- This is the textbook threshold inequality rewritten in linear form.
    nlinarith
  have hscaled :
      ((γ : ℝ) * (L : ℝ) * residual) ≤
        (((L : ℝ) - (Lf : ℝ) / 2) * residual) := by
    exact mul_le_mul_of_nonneg_right hlinear hresidual_nonneg
  have hdiv :
      (((γ : ℝ) * (L : ℝ) * residual) / (L : ℝ) ^ (2 : ℕ)) ≤
        ((((L : ℝ) - (Lf : ℝ) / 2) * residual) / (L : ℝ) ^ (2 : ℕ)) := by
    exact div_le_div_of_nonneg_right hscaled hL_sq_nonneg
  have hL_ne : (L : ℝ) ≠ 0 := ne_of_gt hL_pos
  have hcoeff_real :
      ((γ : ℝ) / (L : ℝ)) * residual ≤
        (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ)) * residual := by
    -- Rewriting both sides with the common denominator `L^2` exposes the monotone division step.
    have hleft :
        (((γ : ℝ) * (L : ℝ) * residual) / (L : ℝ) ^ (2 : ℕ)) =
          ((γ : ℝ) / (L : ℝ)) * residual := by
      field_simp [pow_two, hL_ne]
    have hright :
        ((((L : ℝ) - (Lf : ℝ) / 2) * residual) / (L : ℝ) ^ (2 : ℕ)) =
          (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ)) * residual := by
      rw [div_eq_mul_inv]
      ring
    rw [hleft, hright] at hdiv
    exact hdiv
  have hcoeff :
      ((((γ : ℝ) / (L : ℝ)) * residual : ℝ) : EReal) ≤
        ((((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) * residual : ℝ) : EReal) := by
    exact EReal.coe_le_coe_iff.2 hcoeff_real
  -- Combining the coefficient comparison with Lemma 10.4 gives the B1 acceptance test.
  simpa [proximal_gradient_backtracking_accepts, xInterior, residual] using
    le_trans hcoeff hdecrease

/-- Helper for Remark 10.13: some geometric B1 trial eventually crosses the smoothness threshold
and is therefore accepted. -/
lemma exists_accepted_backtracking_trial
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf) :
    ∃ i : ℕ,
      proximal_gradient_backtracking_accepts
        f g γ (proximal_gradient_backtracking_trial_stepsize s η i)
        hg_effective_domain_subset_interior_f_effective_domain x := by
  have hs_pos : 0 < (s : ℝ) := s.2
  have hη_gt_one : 1 < (η : ℝ) := η.2
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt
    (((Lf : ℝ) / (2 * (1 - (γ : ℝ)))) / (s : ℝ))
    hη_gt_one
  refine ⟨i, ?_⟩
  have hthreshold_lt :
      (Lf : ℝ) / (2 * (1 - (γ : ℝ))) <
        (proximal_gradient_backtracking_trial_stepsize s η i : ℝ) := by
    -- Geometric growth of `η^i` eventually pushes the trial stepsize above the threshold.
    rw [proximal_gradient_backtracking_trial_stepsize_coe]
    have hi' : (Lf : ℝ) / (2 * (1 - (γ : ℝ))) < (η : ℝ) ^ i * (s : ℝ) := by
      exact (div_lt_iff₀ hs_pos).1 hi
    simpa [mul_comm, mul_left_comm, mul_assoc] using hi'
  exact backtracking_accepts_of_stepsize_ge_smoothness_threshold
    f g Lf
    hg_effective_domain_subset_interior_f_effective_domain
    γ x
    hf_ne_bot hf_effective_domain_convex
    hf_toReal_smooth_on_interior_effective_domain
    (proximal_gradient_backtracking_trial_stepsize s η i)
    hthreshold_lt.le

/-- Helper for Remark 10.13: any rejected geometric B1 trial lies strictly below the smoothness
threshold `L_f / (2 * (1 - γ))`. -/
lemma backtracking_trial_lt_smoothness_threshold_of_rejected
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {j : ℕ}
    (hreject :
      ¬ proximal_gradient_backtracking_accepts
        f g γ (proximal_gradient_backtracking_trial_stepsize s η j)
        hg_effective_domain_subset_interior_f_effective_domain x) :
    (proximal_gradient_backtracking_trial_stepsize s η j : ℝ) <
      (Lf : ℝ) / (2 * (1 - (γ : ℝ))) := by
  -- The threshold-acceptance lemma yields the contrapositive source-proof bridge.
  refine lt_of_not_ge fun hge ↦ ?_
  exact hreject <|
    backtracking_accepts_of_stepsize_ge_smoothness_threshold
      f g Lf
      hg_effective_domain_subset_interior_f_effective_domain
      γ x
      hf_ne_bot hf_effective_domain_convex
      hf_toReal_smooth_on_interior_effective_domain
      (proximal_gradient_backtracking_trial_stepsize s η j)
      hge

/-- Helper for Remark 10.13: consecutive B1 trial stepsizes differ by a multiplicative factor
`η`. -/
lemma proximal_gradient_backtracking_trial_stepsize_succ_coe
    (n : ℕ) :
    (proximal_gradient_backtracking_trial_stepsize s η (n + 1) : ℝ) =
      (η : ℝ) * (proximal_gradient_backtracking_trial_stepsize s η n : ℝ) := by
  -- Unfold the geometric trial family and rewrite `η^(n+1)` as `η * η^n`.
  simp [proximal_gradient_backtracking_trial_stepsize_coe, pow_succ, mul_assoc, mul_left_comm,
    mul_comm]

-- Proof sketch: by Lemma 10.4, every trial curvature `L` with
-- `L ≥ L_f / (2 (1 - γ))` satisfies the B1 sufficient-decrease test. Since the trial family
-- `s η^i` grows geometrically with `η > 1`, some trial is accepted; then choose the least
-- accepted index to obtain a valid B1 output.
/-- Remark 10.13 (1): for a proper closed convex `g` and a smooth term `f` that never takes the
value `-∞`, whose domain contains `effective_domain g` in its interior, backtracking procedure B1
terminates at every point `x^k ∈ dom(g)`. Equivalently, there exists a valid backtracking index
whose accepted trial curvature satisfies the sufficient-decrease inequality. -/
theorem exists_backtracking_procedure_B1_index
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf) :
    ∃ i : ℕ,
      is_backtracking_procedure_B1_index
        f g s γ η
        hg_effective_domain_subset_interior_f_effective_domain x
        i := by
  classical
  have hex :
      ∃ i : ℕ,
        proximal_gradient_backtracking_accepts
          f g γ (proximal_gradient_backtracking_trial_stepsize s η i)
          hg_effective_domain_subset_interior_f_effective_domain x :=
    exists_accepted_backtracking_trial
      f g Lf hg_effective_domain_subset_interior_f_effective_domain
      s γ η x
      hf_ne_bot hf_effective_domain_convex
      hf_toReal_smooth_on_interior_effective_domain
  refine ⟨Nat.find hex, ?_⟩
  refine ⟨Nat.find_spec hex, ?_⟩
  intro j hj
  -- The chosen output is the least accepted trial index, exactly as in Algorithm 10.2.
  intro hj_accepts
  exact Nat.not_lt_of_ge (Nat.find_min' hex hj_accepts) hj

-- Proof sketch: if the accepted index is `i = 0`, then the accepted stepsize is `s`. Otherwise
-- the preceding trial `s η^(i-1)` is rejected by minimality. Any rejected trial must lie below
-- the threshold `L_f / (2 (1 - γ))` coming from Lemma 10.4, so multiplying by `η` yields the
-- bound `L_k < η L_f / (2 (1 - γ))`. Combining the two cases gives the stated maximum bound.
/-- Remark 10.13 (2): if `i_k` is the valid output of backtracking procedure B1 at a point
`x^k ∈ dom(g)`, then its accepted stepsize `L_k = s η^{i_k}` satisfies the uniform upper bound
`L_k ≤ max {s, η L_f / (2 (1 - γ))}`. -/
theorem backtracking_procedure_B1_stepsize_le_max_initial_or_smoothness_threshold
    (hf_ne_bot : ∀ y, f y ≠ ⊥)
    (hf_effective_domain_convex : Convex ℝ (effective_domain f))
    (hf_toReal_smooth_on_interior_effective_domain :
      is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)
    {i : ℕ}
    (hi : is_backtracking_procedure_B1_index
      f g s γ η
      hg_effective_domain_subset_interior_f_effective_domain x
      i) :
    (proximal_gradient_backtracking_trial_stepsize s η i : ℝ) ≤
      max (s : ℝ)
        (((η : ℝ) * (Lf : ℝ)) /
          (2 * (1 - (γ : ℝ)))) := by
  cases i with
  | zero =>
      -- At the initial trial, the accepted stepsize is exactly `s`.
      simpa [proximal_gradient_backtracking_trial_stepsize_coe] using
        (le_max_left (s : ℝ)
          (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))
  | succ n =>
      have hreject :
          ¬ proximal_gradient_backtracking_accepts
            f g γ (proximal_gradient_backtracking_trial_stepsize s η n)
            hg_effective_domain_subset_interior_f_effective_domain x :=
        is_backtracking_procedure_B1_index_minimal hi (Nat.lt_succ_self n)
      have htrial_lt_threshold :
          (proximal_gradient_backtracking_trial_stepsize s η n : ℝ) <
            (Lf : ℝ) / (2 * (1 - (γ : ℝ))) :=
        backtracking_trial_lt_smoothness_threshold_of_rejected
          f g Lf hg_effective_domain_subset_interior_f_effective_domain
          s γ η x
          hf_ne_bot hf_effective_domain_convex
          hf_toReal_smooth_on_interior_effective_domain
          hreject
      have hη_pos : 0 < (η : ℝ) := lt_trans zero_lt_one η.2
      have hmul_lt :
          (η : ℝ) * (proximal_gradient_backtracking_trial_stepsize s η n : ℝ) <
            (η : ℝ) * ((Lf : ℝ) / (2 * (1 - (γ : ℝ)))) := by
        exact mul_lt_mul_of_pos_left htrial_lt_threshold hη_pos
      have hbound :
          (proximal_gradient_backtracking_trial_stepsize s η (n + 1) : ℝ) <
            (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))) := by
        -- The current accepted trial is `η` times its rejected predecessor.
        rw [proximal_gradient_backtracking_trial_stepsize_succ_coe]
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hmul_lt
      exact le_trans (le_of_lt hbound) (le_max_right (s : ℝ)
        (((η : ℝ) * (Lf : ℝ)) / (2 * (1 - (γ : ℝ)))))

end
