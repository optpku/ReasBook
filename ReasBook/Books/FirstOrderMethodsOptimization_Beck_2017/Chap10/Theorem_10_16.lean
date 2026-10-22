/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_10
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Algorithm_10_3
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_9
import FirstOrderMethodsOptimization_Beck_2017.Chap10.ProxGradientLinearizationDefect

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
variable {f g : E → EReal} [IsProperExtendedRealFunction g]
  [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)]

local notation "F" => composite_model_objective f g

/- Theorem 10.16 is `source-facing` in the Chapter 10 proximal-gradient API.

Domain sampling:
- `proximal_gradient_backtracking_B2_accepts` from Algorithm 10.3 is the existing owner for the
  local upper-model inequality at the prox-gradient point `T_L(y)`;
- `composite_model_objective` from Definition 10.2 is the chapter owner for the composite value
  `F = f + g`;
- `prox_grad_operator` from Definition 10.9 is the canonical one-step prox-gradient point
  `T_L(y)`;
- `prox_gradient_linearization_defect` from Remark 10.17 is the existing chapter owner for the
  textbook first-order residual `ℓ_f(x, y)`, together with its exported notation `ℓ[f, x, y]`.

This file therefore reuses the existing Chapter 10 owner declarations, rather than keeping a
second local name for the same linearization term. -/

/-- Helper for Theorem 10.16: the prox-grad point lies in the effective domain of the nonsmooth
term `g`. -/
lemma prox_grad_step_mem_effective_domain_g
    (y : interior (effective_domain f)) (L : PosReal) :
    let xPlus := T[L, f, g] y
    xPlus ∈ effective_domain g := by
  let xPlus : E := T[L, f, g] y
  let z : E := (y : E) - (1 / L : ℝ) • ∇ (fun x ↦ (f x).toReal) (y : E)
  have hprox :
      prox[((((1 / L : PosReal) : EReal) • g))] z = {xPlus} := by
    simpa [xPlus, z, proximal_gradient_step] using prox_grad_operator_eq_singleton f g L y
  let hg_convex : is_convex_function g := Fact.out
  rcases @scaled_prox_singleton_support_of_proper_convex
      E _ _ _ g (1 / L) inferInstance hg_convex z xPlus hprox with
    ⟨hxPlus_eff, _⟩
  simpa [xPlus] using hxPlus_eff

/-- Helper for Theorem 10.16: the prox-grad optimality condition gives the affine support
inequality for `g` at `xPlus = T_L(y)`. -/
lemma prox_grad_support_inequality
    (x : E) (y : interior (effective_domain f)) (L : PosReal) :
    let xPlus := T[L, f, g] y
    ((inner ℝ
        ((((L : ℝ) • ((y : E) - xPlus)) - ∇ (fun z ↦ (f z).toReal) (y : E)))
        (x - xPlus) : ℝ) : EReal) ≤
      g x - g xPlus := by
  let xPlus : E := T[L, f, g] y
  dsimp [xPlus]
  let z : E := (y : E) - (1 / L : ℝ) • ∇ (fun w ↦ (f w).toReal) (y : E)
  let hg_convex : is_convex_function g := Fact.out
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hprox : prox[((((1 / L : PosReal) : EReal) • g))] z = {xPlus} := by
    simpa [xPlus, z, proximal_gradient_step] using prox_grad_operator_eq_singleton f g L y
  rcases @scaled_prox_singleton_support_of_proper_convex
      E _ _ _ g (1 / L) inferInstance hg_convex z xPlus hprox with
    ⟨hxPlus_eff, hsupport⟩
  have hvector :
      ((1 / (1 / L : PosReal) : ℝ) • (z - xPlus)) =
        (((L : ℝ) • ((y : E) - xPlus)) - ∇ (fun w ↦ (f w).toReal) (y : E)) := by
    have hLinv : (1 / (1 / L : PosReal) : ℝ) = (L : ℝ) := by
      simp
    have hz_sub :
        z - xPlus = ((y : E) - xPlus) - (1 / L : ℝ) • ∇ (fun w ↦ (f w).toReal) (y : E) := by
      dsimp [z]
      abel
    have hcancel : (L : ℝ) * (1 / L : ℝ) = 1 := by
      field_simp [show (L : ℝ) ≠ 0 by exact (PosReal.coe_pos L).ne']
    rw [hLinv, hz_sub, smul_sub, smul_smul, hcancel, one_smul]
  by_cases hxg : x ∈ effective_domain g
  · have hsupport' := hsupport x hxg
    rwa [hvector] at hsupport'
  · have hgx_top : g x = ⊤ := by
      rw [mem_effective_domain] at hxg
      exact le_antisymm le_top (not_lt.mp hxg)
    have hxPlus_val :
        g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
      exact (EReal.coe_toReal (mem_effective_domain.mp hxPlus_eff).ne (hg_proper.ne_bot _)).symm
    rw [hgx_top, hxPlus_val, EReal.top_sub_coe]
    exact le_top

/-- Helper for Theorem 10.16: the base-step inner product equals the standard half-difference of
squared norms. -/
lemma inner_base_step_eq_half_norm_balance
    (x : E) (y : interior (effective_domain f)) (L : PosReal) :
    let xPlus := T[L, f, g] y
    inner ℝ ((y : E) - xPlus) (x - xPlus) =
      (‖xPlus - (y : E)‖ ^ (2 : ℕ) + ‖x - xPlus‖ ^ (2 : ℕ) -
        ‖x - (y : E)‖ ^ (2 : ℕ)) / 2 := by
  let xPlus : E := T[L, f, g] y
  have hsq :
      ‖x - (y : E)‖ ^ (2 : ℕ) =
        ‖x - xPlus‖ ^ (2 : ℕ) -
          2 * inner ℝ (x - xPlus) ((y : E) - xPlus) +
            ‖(y : E) - xPlus‖ ^ (2 : ℕ) := by
    simpa [xPlus, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
      (norm_sub_sq_real (x - xPlus) ((y : E) - xPlus))
  have hcomm :
      inner ℝ ((y : E) - xPlus) (x - xPlus) =
        inner ℝ (x - xPlus) ((y : E) - xPlus) := by
    rw [real_inner_comm]
  have hnorm :
      ‖(y : E) - xPlus‖ ^ (2 : ℕ) = ‖xPlus - (y : E)‖ ^ (2 : ℕ) := by
    simp [norm_sub_rev]
  nlinarith [hsq, hcomm, hnorm]

/-- Helper for Theorem 10.16: the affine support inequality for `g` rewrites into the exact
quadratic prox-gap expression used in the final estimate. -/
lemma prox_grad_g_gap_lower_bound
    (x : E) (y : interior (effective_domain f)) (L : PosReal) :
    let xPlus := T[L, f, g] y
    ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
        ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) +
        (((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) -
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - xPlus) : ℝ)) : EReal) +
      g xPlus ≤ g x := by
  let xPlus : E := T[L, f, g] y
  dsimp [xPlus]
  let grad : E := ∇ (fun z ↦ (f z).toReal) (y : E)
  let gapR : ℝ :=
    ((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
      ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) +
      (((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) -
        inner ℝ grad (x - xPlus))
  have hsupport := @prox_grad_support_inequality E _ _ _ f g _ _ _ x y L
  have hsupport' :
      (((gapR : ℝ)) : EReal) ≤ g x - g xPlus := by
    have hsupportx :
        ((inner ℝ (((L : ℝ) • ((y : E) - xPlus)) - grad) (x - xPlus) : ℝ) : EReal) ≤
          g x - g xPlus := by
      simpa [xPlus, grad] using hsupport
    have hleft_eq :
        inner ℝ (((L : ℝ) • ((y : E) - xPlus)) - grad) (x - xPlus) = gapR := by
      have hsmul :
          inner ℝ ((L : ℝ) • ((y : E) - xPlus)) (x - xPlus) =
            (L : ℝ) * inner ℝ ((y : E) - xPlus) (x - xPlus) := by
        rw [inner_smul_left]
        simp
      calc
        inner ℝ (((L : ℝ) • ((y : E) - xPlus)) - grad) (x - xPlus) =
            inner ℝ ((L : ℝ) • ((y : E) - xPlus)) (x - xPlus) -
              inner ℝ grad (x - xPlus) := by
              rw [inner_sub_left]
        _ = (L : ℝ) * inner ℝ ((y : E) - xPlus) (x - xPlus) -
              inner ℝ grad (x - xPlus) := by
              rw [hsmul]
        _ = (L : ℝ) *
              ((‖xPlus - (y : E)‖ ^ (2 : ℕ) + ‖x - xPlus‖ ^ (2 : ℕ) -
                  ‖x - (y : E)‖ ^ (2 : ℕ)) / 2) -
              inner ℝ grad (x - xPlus) := by
              rw [inner_base_step_eq_half_norm_balance x y L]
        _ = gapR := by
              dsimp [gapR]
              ring
    have hleft_eqE :
        (((gapR : ℝ)) : EReal) =
          ((inner ℝ (((L : ℝ) • ((y : E) - xPlus)) - grad) (x - xPlus) : ℝ) : EReal) := by
      exact congrArg (fun t : ℝ ↦ ((t : ℝ) : EReal)) hleft_eq.symm
    rw [hleft_eqE]
    exact hsupportx
  exact EReal.add_le_of_le_sub hsupport'

/-- Helper for Theorem 10.16: if the accepted upper model is based at a point where `f(y) = ⊥`,
then the accepted prox-gradient step also has `f(T_L(y)) = ⊥`. -/
lemma accepted_model_forces_step_bot_of_base_bot
    (y : interior (effective_domain f)) (L : PosReal)
    (hmodel : proximal_gradient_backtracking_B2_accepts f g L y)
    (hfy_bot : f (y : E) = ⊥) :
    let xPlus := T[L, f, g] y
    f xPlus = ⊥ := by
  let xPlus : E := T[L, f, g] y
  dsimp [xPlus]
  have hmodel' :
      f xPlus ≤
        f (y : E) +
          ((inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
            ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [xPlus] using
      (proximal_gradient_backtracking_B2_accepts_iff f g L y).1 hmodel
  have hle_bot : f xPlus ≤ ⊥ := by
    simpa [hfy_bot] using hmodel'
  exact le_antisymm hle_bot bot_le

/-- Helper for Theorem 10.16: if the accepted upper model is based at a point where `f(y)` is
finite, then the accepted prox-gradient step cannot satisfy `f(T_L(y)) = ⊤`. -/
lemma accepted_model_forces_step_ne_top_of_base_finite
    (y : interior (effective_domain f)) (L : PosReal)
    (hmodel : proximal_gradient_backtracking_B2_accepts f g L y)
    (hfy_bot : f (y : E) ≠ ⊥) :
    let xPlus := T[L, f, g] y
    f xPlus ≠ ⊤ := by
  let xPlus : E := T[L, f, g] y
  dsimp [xPlus]
  have hfy_top : f (y : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset y.2)).ne
  have hmodel' :
      f xPlus ≤
        f (y : E) +
          ((inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
            ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
    simpa [xPlus] using
      (proximal_gradient_backtracking_B2_accepts_iff f g L y).1 hmodel
  have hfy_val :
      f (y : E) = (((f (y : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hfy_top hfy_bot).symm
  have hfinite_rhs :
      f (y : E) +
        ((inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
          ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) =
        (((f (y : E)).toReal +
            (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
              ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    rw [hfy_val]
    exact
      (EReal.coe_add
        (f (y : E)).toReal
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
          ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ))).symm
  -- The accepted upper-model right-hand side is finite, so `f(xPlus) = ⊤` is impossible.
  intro hfxPlus_top
  rw [hfxPlus_top, hfinite_rhs] at hmodel'
  have htopgt :
      (⊤ : EReal) >
        (((f (y : E)).toReal +
            (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
              ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ)) : ℝ) : EReal) := by
    simpa using
      (lt_top_iff_ne_top.mpr
        (EReal.coe_ne_top
          ((f (y : E)).toReal +
            (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
              ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ)))))
  have hnot :
      ¬ (⊤ : EReal) ≤
        (((f (y : E)).toReal +
            (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (xPlus - (y : E)) +
              ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ)) : ℝ) : EReal) :=
    not_le_of_gt htopgt
  exact hnot hmodel'

omit [Fact (LowerSemicontinuous g)] [Fact (is_convex_function g)] in
/-- Helper for Theorem 10.16: on the finite branch, the model right-hand side
`g(x) + f(y) + ⟪∇f(y), x - y⟫` is exactly `F(x) - ℓ_f(x, y)`. -/
lemma objective_minus_linearization_eq_model_rhs_of_finite_values
    (x : E) (y : interior (effective_domain f))
    (hxg : x ∈ effective_domain g)
    (hfx_bot : f x ≠ ⊥) (hfx_top : f x ≠ ⊤)
    (hfy_bot : f (y : E) ≠ ⊥) :
    g x + f (y : E) +
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : EReal) =
      F x - ℓ[f, x, y] := by
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  have hfy_top : f (y : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset y.2)).ne
  have hgx_val :
      g x = (((g x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne (hg_proper.ne_bot _)).symm
  have hfx_val :
      f x = (((f x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hfx_top hfx_bot).symm
  have hfy_val :
      f (y : E) = (((f (y : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hfy_top hfy_bot).symm
  have hFx :
      F x = ((((f x).toReal + (g x).toReal : ℝ)) : EReal) := by
    -- The composite objective at `x` is the sum of two finite real values.
    rw [composite_model_objective_apply, hfx_val, hgx_val]
    exact (EReal.coe_add (f x).toReal (g x).toReal).symm
  have hℓ :
      ℓ[f, x, y] =
        (((f x).toReal - (f (y : E)).toReal -
            inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : ℝ) : EReal) := by
    -- Unfold the linearization defect and rewrite the surviving `EReal` terms as coercions.
    rw [prox_gradient_linearization_defect_eq, hfx_val, hfy_val, EReal.coe_sub]
    exact
      (EReal.coe_sub
        ((f x).toReal - (f (y : E)).toReal)
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))).symm
  have hleft :
      g x + f (y : E) +
          (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : EReal) =
        (((g x).toReal + (f (y : E)).toReal +
            inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)) : ℝ) : EReal) := by
    -- The source-model right-hand side is also a finite real value on this branch.
    rw [hgx_val, hfy_val, ← EReal.coe_add]
    exact
      (EReal.coe_add
        ((g x).toReal + (f (y : E)).toReal)
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))).symm
  rw [hleft, hFx, hℓ, EReal.coe_sub]
  congr 1
  ring

/-- Helper for Theorem 10.16: on the surviving finite branch, the prox-support inequality and
the accepted model inequality combine into one pure real objective-gap estimate. -/
lemma prox_grad_finite_branch_real_gap
    (x : E) (y : interior (effective_domain f)) (L : PosReal)
    (hmodel : proximal_gradient_backtracking_B2_accepts f g L y)
    (hfx_bot : f x ≠ ⊥) (hfy_bot : f (y : E) ≠ ⊥)
    (hxPlus_bot : let xPlus := T[L, f, g] y; f xPlus ≠ ⊥)
    (hFx_top : F x ≠ ⊤) :
    let xPlus := T[L, f, g] y
    ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
        ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)) +
        ((f x).toReal - (f (y : E)).toReal -
          inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))) ≤
      ((f x).toReal + (g x).toReal) - ((f xPlus).toReal + (g xPlus).toReal) := by
  let xPlus : E := T[L, f, g] y
  dsimp [xPlus] at hxPlus_bot ⊢
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  let grad : E := ∇ (fun z ↦ (f z).toReal) (y : E)
  let quadR : ℝ :=
    ((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
      ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)
  let tailR : ℝ :=
    ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) -
      inner ℝ grad (x - xPlus)
  have hfy_top : f (y : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset y.2)).ne
  -- The finite-branch hypothesis `F x ≠ ⊤` forces `x ∈ dom(g)`.
  have hxg : x ∈ effective_domain g := by
    by_contra hxg
    have hgx_top : g x = ⊤ := by
      rw [mem_effective_domain] at hxg
      exact le_antisymm le_top (not_lt.mp hxg)
    have hFx_eq_top : F x = ⊤ := by
      rw [composite_model_objective_apply, hgx_top]
      exact EReal.add_top_of_ne_bot hfx_bot
    exact hFx_top hFx_eq_top
  have hgx_bot : g x ≠ ⊥ := hg_proper.ne_bot _
  -- The same branch exclusion then rules out `f x = ⊤`.
  have hfx_top : f x ≠ ⊤ := by
    intro hfx_top
    have hFx_eq_top : F x = ⊤ := by
      rw [composite_model_objective_apply, hfx_top, add_comm]
      exact EReal.add_top_of_ne_bot hgx_bot
    exact hFx_top hFx_eq_top
  have hxPlusg :
      xPlus ∈ effective_domain g :=
    prox_grad_step_mem_effective_domain_g y L
  have hxPlus_top :
      f xPlus ≠ ⊤ :=
    accepted_model_forces_step_ne_top_of_base_finite y L hmodel hfy_bot
  have hgx_val :
      g x = (((g x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne hgx_bot).symm
  have hgxPlus_val :
      g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPlusg).ne (hg_proper.ne_bot _)).symm
  have hfxPlus_val :
      f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hxPlus_top hxPlus_bot).symm
  have hfy_val :
      f (y : E) = (((f (y : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hfy_top hfy_bot).symm
  have hgap_real :
      quadR + tailR ≤ (g x).toReal - (g xPlus).toReal := by
    have hgapE :
        (((quadR + tailR : ℝ)) : EReal) + g xPlus ≤ g x := by
      simpa [xPlus, grad, quadR, tailR] using
        prox_grad_g_gap_lower_bound x y L
    have hgapE' :
        (((quadR + tailR : ℝ)) : EReal) ≤ g x - g xPlus := by
      have hgapIff :
          (((quadR + tailR : ℝ)) : EReal) ≤ g x - g xPlus ↔
            (((quadR + tailR : ℝ)) : EReal) + g xPlus ≤ g x :=
        EReal.le_sub_iff_add_le
          (Or.inr hgx_bot)
          (Or.inl (mem_effective_domain.mp hxPlusg).ne)
      exact hgapIff.2 hgapE
    rw [hgx_val, hgxPlus_val] at hgapE'
    have hgapE'' :
        (((quadR + tailR : ℝ)) : EReal) ≤
          ((((g x).toReal - (g xPlus).toReal : ℝ)) : EReal) := by
      simpa [EReal.coe_sub] using hgapE'
    exact EReal.coe_le_coe_iff.mp hgapE''
  have hmodel_real :
      (f xPlus).toReal ≤
        (f (y : E)).toReal +
          (inner ℝ grad (xPlus - (y : E)) +
            ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ)) := by
    have hmodelE :
        f xPlus ≤
          f (y : E) +
            ((inner ℝ grad (xPlus - (y : E)) +
              ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) := by
      simpa [xPlus, grad] using
        (proximal_gradient_backtracking_B2_accepts_iff f g L y).1 hmodel
    rw [hfxPlus_val, hfy_val] at hmodelE
    have hmodelE' :
        (((f xPlus).toReal : ℝ) : EReal) ≤
          ((((f (y : E)).toReal +
              (inner ℝ grad (xPlus - (y : E)) +
                ((L : ℝ) / 2) * ‖xPlus - (y : E)‖ ^ (2 : ℕ)) : ℝ)) : EReal) := by
      simpa [EReal.coe_add, add_assoc, add_left_comm, add_comm] using hmodelE
    exact EReal.coe_le_coe_iff.mp hmodelE'
  -- Splitting `⟪∇f(y), x - y⟫` along `x - y = (x - xPlus) + (xPlus - y)` matches the source proof.
  have hinner_split :
      inner ℝ grad (x - (y : E)) =
        inner ℝ grad (x - xPlus) + inner ℝ grad (xPlus - (y : E)) := by
    have hdecomp : x - (y : E) = (x - xPlus) + (xPlus - (y : E)) := by
      abel
    calc
      inner ℝ grad (x - (y : E)) = inner ℝ grad ((x - xPlus) + (xPlus - (y : E))) := by
        rw [hdecomp]
      _ = inner ℝ grad (x - xPlus) + inner ℝ grad (xPlus - (y : E)) := by
        rw [inner_add_right]
  -- The two real inequalities are exactly the textbook `φ(x) - F(xPlus)` comparison.
  dsimp [quadR, tailR] at hgap_real ⊢
  linarith

/-- Helper for Theorem 10.16: on the surviving finite branch, rewrite the final `EReal` goal into
the exact pure real objective-gap inequality. -/
lemma fundamental_prox_grad_goal_normal_form
    (x : E) (y : interior (effective_domain f)) (L : PosReal)
    (hxg : x ∈ effective_domain g)
    (hxPlusg : let xPlus := T[L, f, g] y; xPlus ∈ effective_domain g)
    (hfx_bot : f x ≠ ⊥) (hfx_top : f x ≠ ⊤)
    (hfy_bot : f (y : E) ≠ ⊥)
    (hxPlus_bot : let xPlus := T[L, f, g] y; f xPlus ≠ ⊥)
    (hxPlus_top : let xPlus := T[L, f, g] y; f xPlus ≠ ⊤) :
    let xPlus := T[L, f, g] y
    (F x - F xPlus ≥
      ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ℓ[f, x, y]) ↔
      ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)) +
          ((f x).toReal - (f (y : E)).toReal -
            inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))) ≤
        ((f x).toReal + (g x).toReal) - ((f xPlus).toReal + (g xPlus).toReal) := by
  let xPlus : E := T[L, f, g] y
  have hxPlusg' : xPlus ∈ effective_domain g := by
    simpa [xPlus] using hxPlusg
  have hxPlus_bot' : f xPlus ≠ ⊥ := by
    simpa [xPlus] using hxPlus_bot
  have hxPlus_top' : f xPlus ≠ ⊤ := by
    simpa [xPlus] using hxPlus_top
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  let quadR : ℝ :=
    ((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
      ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)
  let ellR : ℝ :=
    (f x).toReal - (f (y : E)).toReal -
      inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E))
  have hfy_top : f (y : E) ≠ ⊤ := (mem_effective_domain.mp (interior_subset y.2)).ne
  have hgx_val :
      g x = (((g x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxg).ne (hg_proper.ne_bot _)).symm
  have hgxPlus_val :
      g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hxPlusg').ne (hg_proper.ne_bot _)).symm
  have hfx_val :
      f x = (((f x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hfx_top hfx_bot).symm
  have hfxPlus_val :
      f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hxPlus_top' hxPlus_bot').symm
  have hFy_val :
      f (y : E) = (((f (y : E)).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal hfy_top hfy_bot).symm
  have hFx :
      F x = ((((f x).toReal + (g x).toReal : ℝ)) : EReal) := by
    -- Both objective terms at `x` are finite on the surviving branch.
    rw [composite_model_objective_apply, hfx_val, hgx_val]
    exact (EReal.coe_add (f x).toReal (g x).toReal).symm
  have hFxPlus :
      F xPlus = ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
    -- The realized prox-gradient step is also finite for both summands.
    rw [composite_model_objective_apply, hfxPlus_val, hgxPlus_val]
    exact (EReal.coe_add (f xPlus).toReal (g xPlus).toReal).symm
  have hFgap :
      F x - F xPlus =
        ((((f x).toReal + (g x).toReal) -
            ((f xPlus).toReal + (g xPlus).toReal) : ℝ) : EReal) := by
    rw [hFx, hFxPlus, EReal.coe_sub]
  have hℓ :
      ℓ[f, x, y] = ((ellR : ℝ) : EReal) := by
    -- Unfold the linearization defect once, then rewrite it as a single real coercion.
    rw [prox_gradient_linearization_defect_eq, hfx_val, hFy_val, EReal.coe_sub]
    exact
      (EReal.coe_sub
        ((f x).toReal - (f (y : E)).toReal)
        (inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))).symm
  simpa [xPlus] using
    (show
      (F x - F xPlus ≥
        ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ℓ[f, x, y]) ↔
        ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)) +
            ((f x).toReal - (f (y : E)).toReal -
              inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))) ≤
          ((f x).toReal + (g x).toReal) - ((f xPlus).toReal + (g xPlus).toReal) from by
      constructor
      · intro hgoal
        rw [hFgap, hℓ] at hgoal
        have hgoal' :
            (((quadR + ellR : ℝ)) : EReal) ≤
              ((((f x).toReal + (g x).toReal) -
                  ((f xPlus).toReal + (g xPlus).toReal) : ℝ) : EReal) := by
          simpa [quadR, ellR, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hgoal
        exact EReal.coe_le_coe_iff.mp hgoal'
      · intro hgoal
        have hgoal' :
            (((quadR + ellR : ℝ)) : EReal) ≤
              ((((f x).toReal + (g x).toReal) -
                  ((f xPlus).toReal + (g xPlus).toReal) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.mpr hgoal
        rw [hFgap, hℓ]
        simpa [quadR, ellR, EReal.coe_add, add_assoc, add_left_comm, add_comm] using hgoal')

/-- Helper for Theorem 10.16: once the `⊥`/`⊤` branches are excluded, the proved prox-support
gap and the accepted upper-model inequality combine to give the final textbook estimate. -/
lemma fundamental_prox_grad_inequality_finite_branch
    (x : E) (y : interior (effective_domain f)) (L : PosReal)
    (hmodel : proximal_gradient_backtracking_B2_accepts f g L y)
    (hfx_bot : f x ≠ ⊥) (hfy_bot : f (y : E) ≠ ⊥)
    (hxPlus_bot : let xPlus := T[L, f, g] y; f xPlus ≠ ⊥)
    (hFx_top : F x ≠ ⊤) :
    let xPlus := T[L, f, g] y
    F x - F xPlus ≥
      ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ℓ[f, x, y] := by
  let xPlus : E := T[L, f, g] y
  have hxPlus_bot' : f xPlus ≠ ⊥ := by
    simpa [xPlus] using hxPlus_bot
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  -- The finite-objective branch implies `x ∈ dom(g)`, hence both summands at `x` are finite.
  have hxg : x ∈ effective_domain g := by
    by_contra hxg
    have hgx_top : g x = ⊤ := by
      rw [mem_effective_domain] at hxg
      exact le_antisymm le_top (not_lt.mp hxg)
    have hFx_eq_top : F x = ⊤ := by
      rw [composite_model_objective_apply, hgx_top]
      exact EReal.add_top_of_ne_bot hfx_bot
    exact hFx_top hFx_eq_top
  have hfx_top : f x ≠ ⊤ := by
    intro hfx_top
    have hFx_eq_top : F x = ⊤ := by
      rw [composite_model_objective_apply, hfx_top, add_comm]
      exact EReal.add_top_of_ne_bot (hg_proper.ne_bot _)
    exact hFx_top hFx_eq_top
  have hxPlusg :
      xPlus ∈ effective_domain g :=
    prox_grad_step_mem_effective_domain_g y L
  have hxPlus_top :
      f xPlus ≠ ⊤ :=
    accepted_model_forces_step_ne_top_of_base_finite y L hmodel hfy_bot
  -- Route correction: normalize the goal once, then close it with the pure real gap lemma.
  have hnorm :
      (F x - F xPlus ≥
        ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ℓ[f, x, y]) ↔
        ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)) +
            ((f x).toReal - (f (y : E)).toReal -
              inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))) ≤
          ((f x).toReal + (g x).toReal) - ((f xPlus).toReal + (g xPlus).toReal) := by
    simpa [xPlus] using
      (fundamental_prox_grad_goal_normal_form
        x y L
        hxg
        (by simpa [xPlus] using hxPlusg)
        hfx_bot hfx_top hfy_bot
        (by simpa [xPlus] using hxPlus_bot')
        (by simpa [xPlus] using hxPlus_top))
  have hreal :
      ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ)) +
          ((f x).toReal - (f (y : E)).toReal -
            inner ℝ (∇ (fun z ↦ (f z).toReal) (y : E)) (x - (y : E)))) ≤
        ((f x).toReal + (g x).toReal) - ((f xPlus).toReal + (g xPlus).toReal) := by
    simpa [xPlus] using
      (prox_grad_finite_branch_real_gap
        x y L hmodel hfx_bot hfy_bot
        (by simpa [xPlus] using hxPlus_bot') hFx_top)
  have hgoal :
      F x - F xPlus ≥
        ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
            ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
          ℓ[f, x, y] :=
    hnorm.mpr hreal
  simpa [xPlus] using hgoal

/-- Theorem 10.16: if the local B2 upper-model inequality holds at `y`, equivalently
`f(T_L(y)) ≤ f(y) + ⟪∇ f(y), T_L(y) - y⟫ + (L / 2) ‖T_L(y) - y‖²`, then the composite
objective satisfies the fundamental prox-grad inequality
`F(x) - F(xPlus) ≥ (L / 2) ‖x - xPlus‖² - (L / 2) ‖x - y‖² + ℓ_f(x, y)`. -/
theorem fundamental_prox_grad_inequality
    (x : E) (y : interior (effective_domain f)) (L : PosReal)
    (hmodel : proximal_gradient_backtracking_B2_accepts f g L y) :
    let xPlus := T[L, f, g] y
    F x - F xPlus ≥
      ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
          ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
        ℓ[f, x, y] := by
  let xPlus : E := T[L, f, g] y
  let hg_proper : IsProperExtendedRealFunction g := inferInstance
  by_cases hfx_bot_eq : f x = ⊥
  · -- If `f x = ⊥`, then the linearization defect is already `⊥`, so the claim is immediate.
    have hgoal :
        F x - F xPlus ≥
          ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
              ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
            ℓ[f, x, y] := by
      have hℓ_bot : ℓ[f, x, y] = ⊥ := by
        rw [prox_gradient_linearization_defect_eq, hfx_bot_eq]
        simp only [EReal.bot_sub]
      rw [hℓ_bot]
      simp only [EReal.add_bot, bot_le]
    simpa [xPlus] using hgoal
  · have hfx_bot : f x ≠ ⊥ := hfx_bot_eq
    have hFx_ne_bot : F x ≠ ⊥ := by
      rw [composite_model_objective_apply]
      exact (EReal.add_ne_bot_iff.mpr ⟨hfx_bot, hg_proper.ne_bot _⟩)
    by_cases hfy_bot_eq : f (y : E) = ⊥
    · -- If `f y = ⊥`, acceptance forces the prox-gradient step to have `f xPlus = ⊥`.
      have hxPlus_bot_eq :
          f xPlus = ⊥ :=
        by simpa [xPlus] using
          (accepted_model_forces_step_bot_of_base_bot y L hmodel hfy_bot_eq)
      have hgoal :
          F x - F xPlus ≥
            ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
                ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
              ℓ[f, x, y] := by
        have hFxPlus_bot : F xPlus = ⊥ := by
          rw [composite_model_objective_apply, hxPlus_bot_eq]
          simp only [EReal.bot_add]
        rw [hFxPlus_bot, EReal.sub_bot hFx_ne_bot]
        exact le_top
      simpa [xPlus] using hgoal
    · have hfy_bot : f (y : E) ≠ ⊥ := hfy_bot_eq
      by_cases hxPlus_bot_eq : f xPlus = ⊥
      · -- If the step value is `⊥`, the left-hand side is again `⊤`.
        have hgoal :
            F x - F xPlus ≥
              ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
                  ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
                ℓ[f, x, y] := by
          have hFxPlus_bot : F xPlus = ⊥ := by
            rw [composite_model_objective_apply, hxPlus_bot_eq]
            simp only [EReal.bot_add]
          rw [hFxPlus_bot, EReal.sub_bot hFx_ne_bot]
          exact le_top
        simpa [xPlus] using hgoal
      · have hxPlus_bot : f xPlus ≠ ⊥ := hxPlus_bot_eq
        by_cases hFx_top_eq : F x = ⊤
        · -- If `F x = ⊤`, rewrite the finite step value as a real coercion and finish.
          have hxPlusg :
              xPlus ∈ effective_domain g :=
            prox_grad_step_mem_effective_domain_g y L
          have hxPlus_top :
              f xPlus ≠ ⊤ :=
            accepted_model_forces_step_ne_top_of_base_finite y L hmodel hfy_bot
          have hfxPlus_val :
              f xPlus = (((f xPlus).toReal : ℝ) : EReal) := by
            exact (EReal.coe_toReal hxPlus_top hxPlus_bot).symm
          have hgxPlus_val :
              g xPlus = (((g xPlus).toReal : ℝ) : EReal) := by
            exact
              (EReal.coe_toReal (mem_effective_domain.mp hxPlusg).ne (hg_proper.ne_bot _)).symm
          have hFxPlus :
              F xPlus = ((((f xPlus).toReal + (g xPlus).toReal : ℝ)) : EReal) := by
            rw [composite_model_objective_apply, hfxPlus_val, hgxPlus_val]
            exact (EReal.coe_add (f xPlus).toReal (g xPlus).toReal).symm
          have hgoal :
              F x - F xPlus ≥
                ((((L : ℝ) / 2) * ‖x - xPlus‖ ^ (2 : ℕ) -
                    ((L : ℝ) / 2) * ‖x - (y : E)‖ ^ (2 : ℕ) : ℝ) : EReal) +
                  ℓ[f, x, y] := by
            rw [hFx_top_eq, hFxPlus, EReal.top_sub_coe]
            exact le_top
          simpa [xPlus] using hgoal
        · -- The remaining branch is exactly the finite-branch helper proved above.
          simpa [xPlus] using
            (fundamental_prox_grad_inequality_finite_branch
              x y L hmodel hfx_bot hfy_bot
              (by simpa [xPlus] using hxPlus_bot) hFx_top_eq)

end
