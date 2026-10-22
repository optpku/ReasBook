/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable (f g : E → EReal) (Lf : NNReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
variable [Fact (is_convex_function g)] (hf_ne_bot : ∀ y, f y ≠ ⊥)
variable (hf_effective_domain_convex : Convex ℝ (effective_domain f))
variable (hg_effective_domain_subset_interior_f_effective_domain :
  effective_domain g ⊆ interior (effective_domain f))
variable (hf_toReal_smooth_on_interior_effective_domain :
  is_l_smooth_on (fun y ↦ (f y).toReal) (interior (effective_domain f)) Lf)

local notation "F" => composite_model_objective f g

/- Lemma 10.4 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `IsCompositeSmoothMinimizationProblem` from Definition 10.3 is the chapter owner separating
  primitive assumptions from derived facts for composite smooth minimization, with `f_ne_bot` as
  the primitive source-facing non-`⊥` assumption on the smooth term;
- `composite_model_objective` from Definition 10.2 is the chapter owner for the value `F = f + g`;
- `prox_grad_operator` from Definition 10.9 is the canonical prox-gradient update `T_L`;
- `gradient_mapping` from Definition 10.5 is the owner of the residual `G_L = L • (id - T_L)`.

This lemma stays `source-facing`, so it keeps only the primitive one-step descent hypotheses it
actually uses. In particular, the smooth term must still exclude the value `⊥`, but the
nonemptiness part of `IsProperExtendedRealFunction f` is derived data in Chapter 10 rather than
primitive source content, so the hypothesis is kept at the exact `f_ne_bot` level. The scaled
residual is likewise derived API and should be stated through `gradient_mapping` rather than as a
separate raw formula in the conclusion. -/

-- Proof sketch: let `x⁺ = T[L, f, g] x`. Apply the Chapter 5 descent lemma to
-- `(fun y ↦ (f y).toReal)` at `x` and `x⁺`, use the prox optimality inequality for the scaled
-- function `(1 / L) • g` to control the linear term by `g x - g x⁺ - L ‖x - x⁺‖²`, and then
-- rewrite the result in terms of `composite_model_objective` and the residual
-- `L • (x - x⁺) = G_L^{f,g}(x)`.
/-- Helper for Lemma 10.4: the prox-gradient update lies in the effective domain of `g`. -/
lemma prox_grad_operator_mem_effective_domain_g
    (L : PosReal)
    (x : interior (effective_domain f)) :
    T[L, f, g] x ∈ effective_domain g := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  have hprox :
      prox[((((1 / L : PosReal) : EReal) • g))]
        ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)) =
          {T[L, f, g] x} := by
    -- Expand the Chapter 10 prox-grad operator back to the singleton proximal step.
    simpa [proximal_gradient_step] using prox_grad_operator_eq_singleton f g L x
  rcases prox_singleton_implies_effective_domain_and_inner_support
      ((((1 / L : PosReal) : EReal) • g))
      hg_scaled.1
      hg_scaled.2.2
      ((x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))
      (T[L, f, g] x)
      hprox with
    ⟨hxPlus_eff_scaled, _⟩
  -- Finiteness for the scaled penalty is equivalent to finiteness for `g` itself.
  exact
    (mem_effective_domain_scaled_function_iff g (1 / L) inferInstance (T[L, f, g] x)).mp
      hxPlus_eff_scaled

include hf_ne_bot hf_effective_domain_convex
  hg_effective_domain_subset_interior_f_effective_domain
  hf_toReal_smooth_on_interior_effective_domain

/-- Helper for Lemma 10.4: the prox-gradient update stays in the interior of `dom(f)`. -/
lemma prox_grad_operator_mem_interior_effective_domain_f
    (L : PosReal)
    (x : interior (effective_domain f)) :
    T[L, f, g] x ∈ interior (effective_domain f) := by
  -- The standing domain inclusion upgrades the previous `dom(g)` finiteness to `int(dom(f))`.
  exact
    hg_effective_domain_subset_interior_f_effective_domain
      (prox_grad_operator_mem_effective_domain_g f g L x)

/-- Helper for Lemma 10.4: the proximal support inequality controls the smooth linear term in
real-valued form. -/
lemma prox_grad_linear_term_le_toReal
    (L : PosReal)
    (x : interior (effective_domain f))
    (hxg : (x : E) ∈ effective_domain g) :
    inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (T[L, f, g] x - (x : E)) ≤
      -(L : ℝ) * ‖T[L, f, g] x - (x : E)‖ ^ (2 : ℕ) +
        (g (x : E)).toReal - (g (T[L, f, g] x)).toReal := by
  let xPlus : E := T[L, f, g] x
  let z : E := (x : E) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E)
  let hg_convex : is_convex_function g := Fact.out
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hprox : prox[((((1 / L : PosReal) : EReal) • g))] z = {xPlus} := by
    -- The Chapter 10 prox-gradient step is exactly the singleton proximal point of `(1 / L) g`.
    simpa [xPlus, z, proximal_gradient_step] using prox_grad_operator_eq_singleton f g L x
  rcases scaled_prox_singleton_support_of_proper_convex
      g (1 / L) inferInstance hg_convex z xPlus hprox with
    ⟨hxPlus_eff, hsupport⟩
  have hx_val :
      g (x : E) = (((g (x : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne (hg_proper.ne_bot _)).symm
  have hxPlus_val :
      g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff).ne (hg_proper.ne_bot _)).symm
  have hsupport_real :
      inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) ((x : E) - xPlus) ≤
        (g (x : E)).toReal - (g xPlus).toReal := by
    have hsupportE := hsupport (x : E) hxg
    rw [hx_val, hxPlus_val] at hsupportE
    have hsupportE' :
        (((inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) ((x : E) - xPlus) : ℝ)) :
            EReal) ≤
          ((((g (x : E)).toReal - (g xPlus).toReal : ℝ)) : EReal) := by
      simpa [EReal.coe_sub] using hsupportE
    exact EReal.coe_le_coe_iff.mp hsupportE'
  have hLinv : (1 / (1 / L : PosReal) : ℝ) = (L : ℝ) := by
    simp [PosReal.coe_inv]
  have hleft :
      inner ℝ ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) ((x : E) - xPlus) =
        (L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) -
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) := by
    -- Expanding the forward point `z` isolates the residual square and the linear gradient term.
    have hz_sub :
        z - xPlus = ((x : E) - xPlus) - (1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E) := by
      dsimp [z]
      abel
    rw [hLinv, hz_sub, smul_sub, inner_sub_left]
    have hnorm :
        inner ℝ ((L : ℝ) • ((x : E) - xPlus)) ((x : E) - xPlus) =
          (L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) := by
      calc
        inner ℝ ((L : ℝ) • ((x : E) - xPlus)) ((x : E) - xPlus) =
            (starRingEnd ℝ) (L : ℝ) * inner ℝ ((x : E) - xPlus) ((x : E) - xPlus) := by
          rw [inner_smul_left]
        _ = (L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) := by
          simp [real_inner_self_eq_norm_sq]
    have hgrad :
        inner ℝ ((L : ℝ) • ((1 / L : ℝ) • ∇ (fun y ↦ (f y).toReal) (x : E))) ((x : E) - xPlus) =
          inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) := by
      rw [smul_smul]
      have hcancel : ((L : ℝ) * (1 / L : ℝ)) = 1 := by
        field_simp [show (L : ℝ) ≠ 0 by exact (PosReal.coe_pos L).ne']
      rw [hcancel, one_smul]
    rw [hnorm, hgrad]
  have haux :
      -inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) ≤
        -(L : ℝ) * ‖(x : E) - xPlus‖ ^ (2 : ℕ) +
          (g (x : E)).toReal - (g xPlus).toReal := by
    rw [hleft] at hsupport_real
    linarith
  have hdir :
      inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) =
        -inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) ((x : E) - xPlus) := by
    have hsub : xPlus - (x : E) = -((x : E) - xPlus) := by
      abel
    rw [hsub, inner_neg_right]
  -- Replace `xPlus - x` by the negative residual and use symmetry of the norm.
  simpa [xPlus, hdir, norm_sub_rev] using haux

/-- Helper for Lemma 10.4: the squared norm of the gradient mapping is the squared residual norm
scaled by `L^2`. -/
lemma gradient_mapping_norm_sq_eq_residual_sq
    (L : PosReal)
    (x : interior (effective_domain f)) :
    ‖G[L, f, g] x‖ ^ (2 : ℕ) =
      (L : ℝ) ^ (2 : ℕ) * ‖((x : E) - T[L, f, g] x)‖ ^ (2 : ℕ) := by
  -- Expand `G_L(x) = L • (x - T_L(x))` and square the norm.
  rw [gradient_mapping_apply, norm_smul, Real.norm_eq_abs, abs_of_pos L.2, pow_two, pow_two]
  ring

/-- Lemma 10.4: if `g` is proper, closed, and convex; `effective_domain f` is convex;
`effective_domain g ⊆ interior (effective_domain f)`; and `(fun y ↦ (f y).toReal)` is
`L_f`-smooth on `interior (effective_domain f)`, then for every positive stepsize `L` the
composite objective `F = f + g` decreases along one prox-grad step by at least
`((L - L_f / 2) / L^2) ‖G_L^{f,g}(x)‖²`. -/
theorem prox_grad_sufficient_decrease
    (L : PosReal)
    (x : interior (effective_domain f)) :
    F (x : E) - F (T[L, f, g] x) ≥
      ((((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) *
          ‖G[L, f, g] x‖ ^ (2 : ℕ) : ℝ) : EReal) := by
  let xPlus : E := T[L, f, g] x
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hx_eff_f : (x : E) ∈ effective_domain f := interior_subset x.property
  have hxPlus_int_f :
      xPlus ∈ interior (effective_domain f) :=
    prox_grad_operator_mem_interior_effective_domain_f
      f g Lf hf_ne_bot hf_effective_domain_convex
      hg_effective_domain_subset_interior_f_effective_domain
      hf_toReal_smooth_on_interior_effective_domain L x
  have hxPlus_eff_f : xPlus ∈ effective_domain f := interior_subset hxPlus_int_f
  have hxPlus_eff_g : xPlus ∈ effective_domain g :=
    prox_grad_operator_mem_effective_domain_g f g L x
  by_cases hxg : (x : E) ∈ effective_domain g
  · have hfx_val :
        f (x : E) = (((f (x : E)).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hx_eff_f).ne (hf_ne_bot _)).symm
    have hfxPlus_val :
        f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_f).ne (hf_ne_bot _)).symm
    have hgx_val :
        g (x : E) = (((g (x : E)).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne (hg_proper.ne_bot _)).symm
    have hgxPlus_val :
        g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_g).ne (hg_proper.ne_bot _)).symm
    have hdescent :
        (f xPlus).toReal ≤
          (f (x : E)).toReal +
            inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) +
            ((Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
      -- Apply the Chapter 5 descent lemma at `x` and the realized successor `xPlus`.
      simpa [xPlus, norm_sub_rev] using
        (is_l_smooth_on_descent_lemma
          hf_effective_domain_convex.interior
          hf_toReal_smooth_on_interior_effective_domain
          x.property
          hxPlus_int_f)
    have hlinear :
        inner ℝ (∇ (fun y ↦ (f y).toReal) (x : E)) (xPlus - (x : E)) ≤
          -(L : ℝ) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) +
            (g (x : E)).toReal - (g xPlus).toReal := by
      -- The Chapter 6 singleton support inequality controls the linear model error.
      simpa [xPlus] using
        (prox_grad_linear_term_le_toReal
          f g Lf hf_ne_bot hf_effective_domain_convex
          hg_effective_domain_subset_interior_f_effective_domain
          hf_toReal_smooth_on_interior_effective_domain L x hxg)
    have hgap_real :
        ((L : ℝ) - (Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) ≤
          (f (x : E)).toReal + (g (x : E)).toReal -
            ((f xPlus).toReal + (g xPlus).toReal) := by
      -- Adding the two real inequalities yields the exact one-step objective gap.
      linarith
    have hcoeff_real :
        (((L : ℝ) - (Lf : ℝ) / 2) / (L : ℝ) ^ (2 : ℕ) * ‖G[L, f, g] x‖ ^ (2 : ℕ)) =
          ((L : ℝ) - (Lf : ℝ) / 2) * ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
      rw [gradient_mapping_norm_sq_eq_residual_sq
        f g Lf hf_ne_bot hf_effective_domain_convex
        hg_effective_domain_subset_interior_f_effective_domain
        hf_toReal_smooth_on_interior_effective_domain L x]
      have hL0 : (L : ℝ) ≠ 0 := (PosReal.coe_pos L).ne'
      rw [pow_two]
      have hnorm :
          ‖(x : E) - T[L, f, g] x‖ ^ (2 : ℕ) = ‖xPlus - (x : E)‖ ^ (2 : ℕ) := by
        simp [xPlus, norm_sub_rev]
      rw [hnorm]
      field_simp [hL0]
    have hFx :
        F (x : E) = ((((f (x : E)).toReal + (g (x : E)).toReal : ℝ)) : EReal) := by
      -- On the finite branch, the composite objective is the sum of two finite real values.
      rw [composite_model_objective_apply, hfx_val, hgx_val]
      exact (EReal.coe_add (f (x : E)).toReal (g (x : E)).toReal).symm
    have hFxPlus :
        F xPlus = ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
      rw [composite_model_objective_apply, hfxPlus_val, hgxPlus_val]
      exact (EReal.coe_add (f xPlus).toReal (g xPlus).toReal).symm
    have hFgap :
        F (x : E) - F xPlus =
          ((((f (x : E)).toReal + (g (x : E)).toReal) -
              ((f xPlus).toReal + (g xPlus).toReal) : ℝ) : EReal) := by
      rw [hFx, hFxPlus, EReal.coe_sub]
    rw [hFgap, hcoeff_real]
    exact EReal.coe_le_coe_iff.mpr hgap_real
  · have hgx_top : g (x : E) = ⊤ := by
      rw [mem_effective_domain] at hxg
      exact le_antisymm le_top (not_lt.mp hxg)
    have hfxPlus_val :
        f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_f).ne (hf_ne_bot _)).symm
    have hgxPlus_val :
        g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff_g).ne (hg_proper.ne_bot _)).symm
    have hFx_top : F (x : E) = ⊤ := by
      -- Outside `dom(g)`, the composite value is `⊤` because `f` never takes the value `⊥`.
      rw [composite_model_objective_apply, hgx_top]
      exact EReal.add_top_of_ne_bot (hf_ne_bot (x : E))
    have hFxPlus :
        F xPlus = ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
      rw [composite_model_objective_apply, hfxPlus_val, hgxPlus_val]
      exact (EReal.coe_add (f xPlus).toReal (g xPlus).toReal).symm
    rw [hFx_top, hFxPlus, EReal.top_sub_coe]
    exact le_top

end
