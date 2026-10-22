/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Lemma_5_7
import FirstOrderMethodsOptimization_Beck_2017.Chap09.Definition_9_2
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 5 and Chapter 13 owner APIs.

This item is `source-facing`: it records the one-step descent inequality along the generalized
conditional-gradient segment. Its gap term is nevertheless already canonically owned in Text 13.2
by `generalized_conditional_gradient_norm`, written `S[f, g](x)`. The relevant declarations are:

- `composite_model_objective` for the composite value `F = f + g`;
- `generalized_conditional_gradient_argmin` for the linearized search point `p(x)`;
- `generalized_conditional_gradient_norm`, written `S[f, g](x)`, for the chapter gap quantity;
- `generalized_conditional_gradient_norm_eq_of_mem_argmin` for the bridge from a chosen minimizer
  `p` back to that canonical owner;
- `is_l_smooth_on` for the smoothness of the real-valued term `f`;
- `is_convex_function` and `effective_domain` for the convex extended-real term `g`.

The primitive source data is the argmin witness `hp`; the chosen-point gap value is only derived
API. Accordingly, the public theorem is stated on `S[f, g](x)`, while the gap-objective formula is
used only as a bridge step through
`generalized_conditional_gradient_norm_eq_of_mem_argmin hp`. The textbook codomain restriction
`g : E → (-∞, ∞]` is primitive source data here, so it is kept explicitly as the no-`⊥`
hypothesis `hg_ne_bot` rather than being hidden inside a broader package. -/

section

variable {f : E → ℝ} {g : E → EReal} {Lf : NNReal}

local notation "F" => composite_model_objective f.toEReal g

/-- Helper for Lemma 13.7: any minimizer of the generalized conditional-gradient linearized
subproblem is finite for `g`, hence belongs to `effective_domain g`. -/
lemma generalized_conditional_gradient_argmin_mem_effective_domain
    {x p : E} (hx : x ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x) :
    p ∈ effective_domain g := by
  -- Rewrite the argmin witness as pointwise minimality of the linearized subproblem.
  rw [mem_generalized_conditional_gradient_argmin_iff, isMinOn_univ_iff] at hp
  have hx_sub_lt_top :
      generalized_conditional_gradient_subproblem f g x x < ⊤ := by
    -- The subproblem value at the comparison point `x` is finite because `g x` is finite.
    rw [generalized_conditional_gradient_subproblem_apply]
    exact EReal.add_lt_top (EReal.coe_ne_top _) (mem_effective_domain.mp hx).ne
  have hp_sub_ne_top :
      generalized_conditional_gradient_subproblem f g x p ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt (hp x) hx_sub_lt_top)
  have hgp_ne_top : g p ≠ ⊤ := by
    intro hgp_top
    have hp_sub_top :
        generalized_conditional_gradient_subproblem f g x p = ⊤ := by
      rw [generalized_conditional_gradient_subproblem_apply, hgp_top]
      simpa [add_comm] using EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)
    exact hp_sub_ne_top hp_sub_top
  -- Membership in the effective domain only asks for `g p < ⊤`.
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hgp_ne_top)

/-- Helper for Lemma 13.7: the conditional-gradient trial point is the convex combination of `x`
and `p` with weights `1 - t` and `t`. -/
lemma conditional_gradient_segment_eq_convex_combo
    (x p : E) (t : ℝ) :
    x + t • (p - x) = (1 - t) • x + t • p := by
  -- Expand the affine step and collect the `x` and `p` terms into a convex-combination form.
  calc
    x + t • (p - x) = x + (t • p - t • x) := by
      rw [smul_sub]
    _ = (1 - t) • x + t • p := by
      simp [sub_eq_add_neg, add_smul, add_comm, add_left_comm, add_assoc]

/-- Helper for Lemma 13.7: the quadratic remainder along the conditional-gradient segment
normalizes to the textbook factor `t^2 ‖p - x‖^2`. -/
lemma conditional_gradient_segment_quadratic_rewrite
    {x p : E} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ((Lf : ℝ) / 2) * ‖x - (x + t • (p - x))‖ ^ (2 : ℕ) =
      (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) := by
  -- Rewrite the displacement as a scaled copy of `p - x`, then collapse `‖t‖` using `t ≥ 0`.
  calc
    ((Lf : ℝ) / 2) * ‖x - (x + t • (p - x))‖ ^ (2 : ℕ) =
      ((Lf : ℝ) / 2) * ‖t • (x - p)‖ ^ (2 : ℕ) := by
        rw [show x - (x + t • (p - x)) = -(t • (p - x)) by
          abel_nf]
        rw [show -(t • (p - x)) = t • (x - p) by
          simp [sub_eq_add_neg, smul_sub, add_comm, add_left_comm, add_assoc]]
    _ = ((Lf : ℝ) / 2) * (‖t‖ * ‖p - x‖) ^ (2 : ℕ) := by
        rw [norm_smul, norm_sub_rev]
    _ = ((Lf : ℝ) / 2) * (t * ‖p - x‖) ^ (2 : ℕ) := by
        rw [Real.norm_of_nonneg ht.1]
    _ = (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) := by
        ring

/-- Helper for Lemma 13.7: convexity of `g` bounds the value at the conditional-gradient trial
point by the convex combination of the endpoint values. -/
lemma generalized_conditional_gradient_segment_convex_bound
    {x p : E} (hg_ne_bot : ∀ y, g y ≠ ⊥) (hg_convex : is_convex_function g)
    (hx : x ∈ effective_domain g) (hp_dom : p ∈ effective_domain g)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    g (x + t • (p - x)) ≤ ((1 - t : ℝ) : EReal) * g x + (t : EReal) * g p := by
  letI : IsProperExtendedRealFunction g :=
    { ne_bot := hg_ne_bot
      effective_domain_nonempty := ⟨x, hx⟩ }
  -- Use the Chapter 2 segment inequality after rewriting the affine step as a convex combination.
  have hsegment :=
    (is_convex_function_iff_segment_ineq.mp hg_convex) p hp_dom x hx ht
  simpa [conditional_gradient_segment_eq_convex_combo, add_comm, add_left_comm, add_assoc] using
    hsegment

-- Proof sketch: apply the Chapter 5 descent lemma to `f` on the convex effective domain of `g`
-- between `x` and `(1 - t) • x + t • p`, using convexity of `g` to keep the segment in
-- `effective_domain g` and to bound `g ((1 - t) • x + t • p)` by
-- `(1 - t) * g x + t * g p`. Rewrite the linear term with the argmin search point `p`, then use
-- `generalized_conditional_gradient_norm_eq_of_mem_argmin hp` to identify the resulting
-- first-order decrement with the canonical chapter quantity `S[f, g](x)`.
/-- Lemma 13.7: if `f` is `L_f`-smooth on `dom(g)`, `g` is convex, `x ∈ dom(g)`, `p` minimizes
the linearized subproblem at `x`, and `t ∈ [0, 1]`, then the composite objective satisfies
`F(x + t (p - x)) ≤ F(x) - t S(x) + (t^2 L_f / 2) ‖p - x‖^2`. Here
`F = composite_model_objective f.toEReal g` and
`S(x) = S[f, g](x)`. The chosen-point formula
`S[f, g](x) = generalized_conditional_gradient_gap_objective f g x p` follows from `hp` by
Text 13.2. The textbook assumption
`g : E → (-∞, ∞]` is represented by `hg_ne_bot : ∀ y, g y ≠ ⊥`. -/
theorem generalized_conditional_gradient_fundamental_inequality
    (hg_ne_bot : ∀ y, g y ≠ ⊥)
    (hg_convex : is_convex_function g)
    (hf_smooth : is_l_smooth_on f (effective_domain g) Lf)
    {x p : E} (hx : x ∈ effective_domain g)
    (hp : p ∈ generalized_conditional_gradient_argmin f g x)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    F (x + t • (p - x)) ≤
      F x - (t : EReal) * S[f, g](x) +
        (((t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ 2 : ℝ) : EReal) := by
  -- Route correction: keep the textbook structure explicit. First control the segment point in
  -- `effective_domain g`, then combine the smooth and convex segment bounds, and finally rewrite
  -- the resulting decrement as the canonical gap `S[f, g](x)`.
  let y := x + t • (p - x)
  have hp_dom : p ∈ effective_domain g :=
    generalized_conditional_gradient_argmin_mem_effective_domain hx hp
  have hy : y ∈ effective_domain g := by
    -- Re-express the affine trial point as a convex combination and use convexity of `dom(g)`.
    rw [show y = x + t • (p - x) by rfl, conditional_gradient_segment_eq_convex_combo, add_comm]
    exact combo_mem_effective_domain_of_is_convex_function hg_convex hp_dom hx ht
  have hgx_val :
      g x = (((g x).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hx).ne (hg_ne_bot x)).symm
  have hgp_val :
      g p = (((g p).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hp_dom).ne (hg_ne_bot p)).symm
  have hgy_val :
      g y = (((g y).toReal : ℝ) : EReal) := by
    exact (EReal.coe_toReal (mem_effective_domain.mp hy).ne (hg_ne_bot y)).symm
  have hFy :
      F y = (((f y + (g y).toReal : ℝ)) : EReal) := by
    -- Once `g y` is finite, the composite value is just the sum of the corresponding real values.
    rw [composite_model_objective_apply, hgy_val]
    simpa using (EReal.coe_add (f y) ((g y).toReal)).symm
  have hFx :
      F x = (((f x + (g x).toReal : ℝ)) : EReal) := by
    -- The same finite-value normalization holds at the base point `x`.
    rw [composite_model_objective_apply, hgx_val]
    simpa using (EReal.coe_add (f x) ((g x).toReal)).symm
  have hS_value :
      S[f, g](x) =
        (((inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal : ℝ)) : EReal) := by
    -- Realize the canonical gap by the chosen argmin point and rewrite the finite `g` values
    -- through `toReal`.
    calc
      S[f, g](x) = generalized_conditional_gradient_gap_objective f g x p :=
        generalized_conditional_gradient_norm_eq_of_mem_argmin hp
      _ = ((inner ℝ (∇ f x) (x - p) : ℝ) : EReal) + g x - g p :=
        generalized_conditional_gradient_gap_objective_apply f g x p
      _ = (((inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal : ℝ)) : EReal) := by
        rw [hgx_val, hgp_val, ← EReal.coe_add, ← EReal.coe_sub]
        simp
  have hdescent :
      f y ≤
        f x + t * inner ℝ (∇ f x) (p - x) +
          (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) := by
    -- Apply Lemma 5.7 on the convex effective domain and then normalize the affine-step syntax.
    have hdescent_raw :=
      is_l_smooth_on_descent_lemma
        (effective_domain_convex_of_is_convex_function hg_convex)
        hf_smooth
        hx
        hy
    calc
      f y ≤
          f x + inner ℝ (∇ f x) (y - x) +
            ((Lf : ℝ) / 2) * ‖x - y‖ ^ (2 : ℕ) := hdescent_raw
      _ = f x + inner ℝ (∇ f x) (t • (p - x)) +
            ((Lf : ℝ) / 2) * ‖x - (x + t • (p - x))‖ ^ (2 : ℕ) := by
            rw [show y - x = t • (p - x) by
              dsimp [y]
              abel_nf,
              show y = x + t • (p - x) by rfl]
      _ = f x + t * inner ℝ (∇ f x) (p - x) +
            ((Lf : ℝ) / 2) * ‖x - (x + t • (p - x))‖ ^ (2 : ℕ) := by
            rw [inner_smul_right]
      _ = f x + t * inner ℝ (∇ f x) (p - x) +
            (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) := by
            rw [conditional_gradient_segment_quadratic_rewrite ht]
  have hconv_rhs_val :
      ((1 - t : ℝ) : EReal) * g x + (t : EReal) * g p =
        ((((1 - t) * (g x).toReal + t * (g p).toReal : ℝ)) : EReal) := by
    -- The convex combination on the right-hand side is finite because both endpoint values are.
    rw [hgx_val, hgp_val, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  have hconv :
      (g y).toReal ≤ (1 - t) * (g x).toReal + t * (g p).toReal := by
    -- Convert the convex EReal inequality to a real inequality once the endpoint values are known
    -- to be finite.
    have hconv_raw :=
      generalized_conditional_gradient_segment_convex_bound hg_ne_bot hg_convex hx hp_dom ht
    have hconv_raw' : g y ≤ ((1 - t : ℝ) : EReal) * g x + (t : EReal) * g p := by
      simpa [y] using hconv_raw
    have hconv_rhs_ne_top :
        ((1 - t : ℝ) : EReal) * g x + (t : EReal) * g p ≠ ⊤ := by
      rw [hconv_rhs_val]
      exact EReal.coe_ne_top _
    have hconv_toReal :
        (g y).toReal ≤ (((1 - t : ℝ) : EReal) * g x + (t : EReal) * g p).toReal :=
      EReal.toReal_le_toReal hconv_raw' (hg_ne_bot y) hconv_rhs_ne_top
    rw [hconv_rhs_val] at hconv_toReal
    simpa using hconv_toReal
  have hinner_flip :
      inner ℝ (∇ f x) (x - p) = -inner ℝ (∇ f x) (p - x) := by
    -- The source gap uses `x - p`, while the descent estimate uses `p - x`.
    rw [← neg_sub p x, inner_neg_right]
  have htotal :
      f y + (g y).toReal ≤
        f x + (g x).toReal -
          t * (inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal) +
            (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) := by
    -- Add the smooth and convex bounds, then rewrite the first-order decrement into the textbook
    -- gap expression.
    calc
      f y + (g y).toReal ≤
          f x + t * inner ℝ (∇ f x) (p - x) +
            (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) +
              ((1 - t) * (g x).toReal + t * (g p).toReal) := by
            linarith [hdescent, hconv]
      _ = f x + (g x).toReal -
            t * (inner ℝ (∇ f x) (x - p) + (g x).toReal - (g p).toReal) +
              (t ^ 2 * (Lf : ℝ) / 2) * ‖p - x‖ ^ (2 : ℕ) := by
            rw [hinner_flip]
            ring
  -- With all finite-value rewrites in place, the target inequality reduces to the corresponding
  -- real inequality.
  rw [show F y = F (x + t • (p - x)) by rfl] at hFy
  rw [hFy, hFx, hS_value, ← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_add]
  exact EReal.coe_le_coe_iff.mpr htotal

end

end
