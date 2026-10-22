/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Algorithm_13_1
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Definition_13_22
import FirstOrderMethodsOptimization_Beck_2017.Chap13.Text_13_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- `prompt_add/` is absent in this workspace, so the statement design is sampled directly from the
nearby Chapter 13 owners and the Chapter 13 strong-convexity owner file.

This item is `source-facing`: it is a lower bound for the constrained Frank-Wolfe gap in the
strongly convex feasible-set regime. The owner abstractions already present in the project are:

- `Set.StrongConvex` from Definition 13.22 for the primitive strong-convex geometry of `C`,
  together with the source-facing positivity clause `0 < σ`;
- `generalized_conditional_gradient_argmin`, specialized to `g = extendedIndicator C`, for the
  chosen feasible linear minimizer;
- `generalized_conditional_gradient_norm`, written `S`, for the chapter gap quantity.
- `generalized_conditional_gradient_gap_ge_objective_gap` from Lemma 13.12 as the nearby gradient
  style check: once a statement speaks about `∇ (fun y ↦ (f y).toReal) x`, it should carry an
  explicit differentiability hypothesis at `x`.

Primitive data versus derived API:

- primitive data: `hσ : 0 < σ`, `hC : Set.StrongConvex C σ`, the base point `x : C`, the
  differentiability hypothesis at `x`, the norm lower bound `δ ≤ ‖∇ f₀ x‖`, and the chosen argmin
  witness `px`;
- derived API: feasibility nonemptiness is already supplied by `x : C`, so the stronger wrapper
  `Set.StronglyConvexWith C σ` is unnecessary here, while the constrained gap value itself remains
  the canonical owner `S[f₀, extendedIndicator C](x)`.

Accordingly, the main statement is written directly on the primitive strong-convex owner
`Set.StrongConvex C σ`, the explicit differentiability and gradient lower-bound data at `x`, and a
single pointwise argmin witness, without importing the full Assumption 13.25 package or
introducing any new wrapper around the constrained conditional-gradient data. -/

section

variable
  {f : E → EReal} {C : Set E} {σ δ : ℝ}

local notation "f₀" => fun y ↦ EReal.toReal (f y)

/- The proof follows the textbook midpoint-perturbation route. The helper lemmas below keep the
`EReal`/indicator rewrite, the feasible-minimizer inequality, the strong-convexity midpoint
inclusion, and the final inner-product normalization separate so the main proof stays close to the
source calculation. -/

/-- Helper for Lemma 13.26: at a constrained argmin point, the canonical Chapter 13 gap rewrites
to the real inner product `⟪∇f(x), x - px⟫`. -/
lemma generalized_conditional_gradient_norm_toReal_eq_inner_sub_of_mem_argmin
    (x : C)
    {px : E}
    (hp : px ∈ generalized_conditional_gradient_argmin f₀ (extendedIndicator C) x) :
    (S[f₀, extendedIndicator C](x)).toReal =
      inner ℝ (∇ f₀ x) ((x : E) - px) := by
  -- Recover feasibility of the chosen minimizer so the indicator terms vanish in the gap formula.
  rcases
      (mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
        ⟨(x : E), x.2⟩).mp hp with
    ⟨hpxC, _⟩
  -- The canonical norm is realized by the chosen argmin point, and the constrained indicator is
  -- zero at both feasible endpoints.
  rw [generalized_conditional_gradient_norm_eq_of_mem_argmin hp,
    generalized_conditional_gradient_gap_objective_apply]
  simp [extendedIndicator, x.2, hpxC]

/-- Helper for Lemma 13.26: feasibility of `z` upgrades the constrained argmin condition to the
linear inequality `⟪∇f(x), px⟫ ≤ ⟪∇f(x), z⟫`. -/
lemma argmin_inner_le_of_feasible
    (x : C)
    {px z : E}
    (hp : px ∈ generalized_conditional_gradient_argmin f₀ (extendedIndicator C) x)
    (hz : z ∈ C) :
    inner ℝ (∇ f₀ x) px ≤ inner ℝ (∇ f₀ x) z := by
  -- Translate the constrained argmin witness into the minimizer property for the linear form on
  -- `C`, then commute the inner product to match the source proof's orientation.
  rcases
      (mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
        ⟨(x : E), x.2⟩).mp hp with
    ⟨_, hpmin⟩
  rw [isMinOn_iff] at hpmin
  have hlin : inner ℝ px (∇ f₀ x) ≤ inner ℝ z (∇ f₀ x) :=
    hpmin z hz
  simpa [real_inner_comm] using hlin

/-- Helper for Lemma 13.26: the gradient perturbation has norm at most the strong-convexity
radius `(σ / 8) d²`. -/
lemma gradient_perturbation_norm_le_quadratic_radius
    (hσ : 0 < σ)
    (g : E)
    {d2 : ℝ}
    (hd2 : 0 ≤ d2) :
    ‖(((σ / 8) * (d2 / ‖g‖)) • g)‖ ≤ (σ / 8) * d2 := by
  by_cases hg : ‖g‖ = 0
  · -- When the gradient vanishes, the robust perturbation collapses to `0`.
    have hrad : 0 ≤ (σ / 8) * d2 := by
      positivity
    simp [hg, hrad]
  · -- Otherwise the scaling by `‖g‖⁻¹` cancels the final norm exactly.
    have hcoeff_nonneg : 0 ≤ (σ / 8) * (d2 / ‖g‖) := by
      have hdiv_nonneg : 0 ≤ d2 / ‖g‖ := by
        exact div_nonneg hd2 (norm_nonneg g)
      positivity
    rw [norm_smul, Real.norm_of_nonneg hcoeff_nonneg]
    calc
      ((σ / 8) * (d2 / ‖g‖)) * ‖g‖ = (σ / 8) * ((d2 / ‖g‖) * ‖g‖) := by
        ring
      _ = (σ / 8) * d2 := by
        rw [div_mul_cancel₀ _ hg]
      _ ≤ (σ / 8) * d2 := le_rfl

/-- Helper for Lemma 13.26: strong convexity of `C` keeps the midpoint shifted in the negative
gradient direction inside `C`. -/
lemma strong_convex_midpoint_gradient_perturbation_mem
    (hσ : 0 < σ)
    (hC : Set.StrongConvex C σ)
    (x : C)
    {px : E}
    (hpxC : px ∈ C) :
    ((1 / 2 : ℝ) • (x : E) + (1 - (1 / 2 : ℝ)) • px) -
        (((σ / 8) * (‖((x : E) - px)‖ ^ (2 : ℕ) / ‖∇ f₀ x‖)) • ∇ f₀ x) ∈ C := by
  let center : E := ((1 / 2 : ℝ) • (x : E) + (1 - (1 / 2 : ℝ)) • px)
  let z : E := center -
    (((σ / 8) * (‖((x : E) - px)‖ ^ (2 : ℕ) / ‖∇ f₀ x‖)) • ∇ f₀ x)
  have ht : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    norm_num
  have hd2 : 0 ≤ ‖((x : E) - px)‖ ^ (2 : ℕ) := by
    positivity
  have hz_ball :
      z ∈ Metric.closedBall center
        (((σ / 2) * (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * ‖((x : E) - px)‖ ^ (2 : ℕ)) : ℝ) := by
    -- The perturbation length is bounded by the radius guaranteed by strong convexity at `t = 1/2`.
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hz_sub :
        z - center =
          -((((σ / 8) * (‖((x : E) - px)‖ ^ (2 : ℕ) / ‖∇ f₀ x‖)) : ℝ) • ∇ f₀ x) := by
      simp [z, center, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    rw [hz_sub, norm_neg]
    calc
      ‖((((σ / 8) * (‖((x : E) - px)‖ ^ (2 : ℕ) / ‖∇ f₀ x‖)) : ℝ) • ∇ f₀ x)‖ ≤
          (σ / 8) * ‖((x : E) - px)‖ ^ (2 : ℕ) :=
        gradient_perturbation_norm_le_quadratic_radius
          hσ (∇ f₀ x) hd2
      _ = ((σ / 2) * (1 / 2 : ℝ) * (1 - (1 / 2 : ℝ)) * ‖((x : E) - px)‖ ^ (2 : ℕ)) := by
        ring
  -- Feed the closed-ball membership into the defining strong-convexity inclusion.
  have hsubset := hC x.2 hpxC ht
  have hzC : z ∈ C := hsubset hz_ball
  simpa [z, center] using hzC

/-- Helper for Lemma 13.26: the inner product of the gradient with the perturbation vector is the
quadratic term `(σ / 4) ‖g‖ d²`. -/
lemma gradient_perturbation_inner_eq_quadratic
    (σ : ℝ)
    (g : E)
    {d2 : ℝ} :
    2 * inner ℝ g ((((σ / 8) * (d2 / ‖g‖)) : ℝ) • g) =
      (σ / 4) * ‖g‖ * d2 := by
  by_cases hg : ‖g‖ = 0
  · -- In the zero-gradient case both sides vanish.
    have hg_zero : g = 0 := norm_eq_zero.mp hg
    simp [hg_zero]
  · -- Otherwise expand `⟪g, g⟫` as `‖g‖²` and cancel the single denominator.
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq]
    calc
      2 * (((σ / 8) * (d2 / ‖g‖)) * ‖g‖ ^ (2 : ℕ)) =
          2 * ((σ / 8) * ((d2 / ‖g‖) * ‖g‖) * ‖g‖) := by
            ring
      _ = 2 * ((σ / 8) * d2 * ‖g‖) := by
            rw [div_mul_cancel₀ _ hg]
      _ = (σ / 4) * ‖g‖ * d2 := by
            ring

/-- Helper for Lemma 13.26: subtracting an endpoint from its midpoint with `x` gives half of the
difference `x - y`. -/
lemma midpoint_sub_eq_half_sub
    (x y : E) :
    ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) - y =
      (1 / 2 : ℝ) • (x - y) := by
  -- Normalize the midpoint coefficient and then collect the two `y` terms into `(-1/2) • y`.
  calc
    ((1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y) - y
        = (1 / 2 : ℝ) • x + ((1 / 2 : ℝ) • y - y) := by
          rw [show (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) by norm_num]
          abel
    _ = (1 / 2 : ℝ) • x + (((1 / 2 : ℝ) - 1) • y) := by
          simpa using
            congrArg (fun t : E ↦ (1 / 2 : ℝ) • x + t)
              ((sub_smul (1 / 2 : ℝ) 1 y).symm)
    _ = (1 / 2 : ℝ) • x + ((- (1 / 2 : ℝ)) • y) := by
          norm_num
    _ = (1 / 2 : ℝ) • (x - y) := by
          simp [sub_eq_add_neg, smul_add, smul_neg]

-- Proof sketch: define the perturbed midpoint
-- `z = (x + px) / 2 - (σ / 8) * (‖x - px‖² / ‖∇f(x)‖) • ∇f(x)` in the direction of the
-- negative gradient. The primitive strong-convex inclusion `hC` together with `hσ : 0 < σ` puts
-- `z` back in `C`, while the linear-minimizer property of `px` implies `⟪∇f(x), z - px⟫ ≥ 0`.
-- Rewriting the canonical Chapter 13 owner
-- `S[f₀, extendedIndicator C](x)` by the argmin formula at `px`, then expanding
-- `x - px = 2 ((x + px) / 2 - px)`, substituting the definition of `z`, and using the
-- pointwise gradient lower bound `δ ≤ ‖∇f(x)‖` yields the displayed quadratic lower bound.
/-- Lemma 13.26: if `C` is `σ`-strongly convex in the primitive sense `Set.StrongConvex C σ`,
`σ > 0`, `fun y ↦ (f y).toReal` is differentiable at the feasible point `x ∈ C`,
`δ ≤ ‖∇f(x)‖`, and `px` is a feasible linear minimizer at `x`, then the canonical constrained
Frank-Wolfe gap `S(x)` dominates `(σ δ / 4) ‖x - px‖²`. -/
theorem generalized_conditional_gradient_norm_ge_strong_convexity_quadratic_bound
    (hσ : 0 < σ)
    (hC : Set.StrongConvex C σ)
    (x : C)
    (hx_diff : DifferentiableAt ℝ f₀ x)
    (hδ : δ ≤ ‖∇ f₀ x‖)
    (px : E)
    (hp : px ∈ generalized_conditional_gradient_argmin f₀ (extendedIndicator C) x) :
    (S[f₀, extendedIndicator C](x)).toReal ≥
      (σ * δ / 4) * ‖x - px‖ ^ (2 : ℕ) := by
  let g : E := ∇ f₀ x
  let d2 : ℝ := ‖((x : E) - px)‖ ^ (2 : ℕ)
  let z : E :=
    ((1 / 2 : ℝ) • (x : E) + (1 - (1 / 2 : ℝ)) • px) -
      (((σ / 8) * (d2 / ‖g‖)) • g)
  -- First rewrite the Chapter 13 gap into the real inner product used in the source proof.
  rw [generalized_conditional_gradient_norm_toReal_eq_inner_sub_of_mem_argmin
    x hp]
  rcases
      (mem_generalized_conditional_gradient_argmin_extendedIndicator_iff
        ⟨(x : E), x.2⟩).mp hp with
    ⟨hpxC, _⟩
  have hd2 : 0 ≤ d2 := by
    positivity
  have hzC : z ∈ C := by
    -- This is the geometric midpoint-plus-gradient perturbation step from the textbook.
    simpa [z, d2, g] using
      strong_convex_midpoint_gradient_perturbation_mem
        hσ hC x hpxC
  have hargmin : inner ℝ g px ≤ inner ℝ g z := by
    -- Feasibility of `z` lets the constrained argmin witness compare `px` directly with `z`.
    simpa [g] using argmin_inner_le_of_feasible x hp hzC
  have hz_nonneg : 0 ≤ inner ℝ g (z - px) := by
    -- Rewrite the difference of objective values as the inner product with `z - px`.
    rw [inner_sub_right]
    linarith
  have hmidpoint_sub :
      ((1 / 2 : ℝ) • (x : E) + (1 - (1 / 2 : ℝ)) • px) - px =
        (1 / 2 : ℝ) • (((x : E) - px)) := by
    -- This is the scalar midpoint identity used in the textbook decomposition of `x - px`.
    simpa using midpoint_sub_eq_half_sub (x : E) px
  have hmidpoint_from_z :
      ((1 / 2 : ℝ) • (x : E) + (1 - (1 / 2 : ℝ)) • px) - px =
        (z - px) + (((σ / 8) * (d2 / ‖g‖)) • g) := by
    -- Expand the local definition of `z` and rearrange the additive terms explicitly.
    dsimp [z]
    abel
  have hinner_ge :
      inner ℝ g ((x : E) - px) ≥
        2 * inner ℝ g ((((σ / 8) * (d2 / ‖g‖)) : ℝ) • g) := by
    -- Expand `x - px` through the midpoint, substitute `z`, and drop the nonnegative term
    -- `2 ⟪g, z - px⟫`.
    calc
      inner ℝ g ((x : E) - px) =
          2 * inner ℝ g
            (((1 / 2 : ℝ) • (x : E) + (1 - (1 / 2 : ℝ)) • px) - px) := by
              rw [hmidpoint_sub, real_inner_smul_right]
              ring
      _ = 2 * inner ℝ g ((z - px) + (((σ / 8) * (d2 / ‖g‖)) • g)) := by
            rw [hmidpoint_from_z]
      _ = 2 * inner ℝ g (z - px) +
            2 * inner ℝ g ((((σ / 8) * (d2 / ‖g‖)) : ℝ) • g) := by
            rw [inner_add_right]
            ring
      _ ≥ 2 * inner ℝ g ((((σ / 8) * (d2 / ‖g‖)) : ℝ) • g) := by
            nlinarith
  have hquadratic :
      2 * inner ℝ g ((((σ / 8) * (d2 / ‖g‖)) : ℝ) • g) =
        (σ / 4) * ‖g‖ * d2 := by
    -- This is the algebraic normalization of the perturbation term.
    exact gradient_perturbation_inner_eq_quadratic σ g
  have hdelta_scaled :
      (σ * δ / 4) * d2 ≤ (σ / 4) * ‖g‖ * d2 := by
    -- Scale `δ ≤ ‖g‖` first by `σ / 4`, then by `d²`, and normalize the scalar products.
    have hσ_quarter_nonneg : 0 ≤ σ / 4 := by
      positivity
    have hscaled_left :
        (σ / 4) * δ ≤ (σ / 4) * ‖g‖ :=
      mul_le_mul_of_nonneg_left hδ hσ_quarter_nonneg
    have hscaled :
        ((σ / 4) * δ) * d2 ≤ ((σ / 4) * ‖g‖) * d2 :=
      mul_le_mul_of_nonneg_right hscaled_left hd2
    have hnormalized := hscaled
    ring_nf at hnormalized ⊢
    exact hnormalized
  have hfinal :
      inner ℝ g ((x : E) - px) ≥ (σ * δ / 4) * d2 := by
    calc
      inner ℝ g ((x : E) - px) ≥
          2 * inner ℝ g ((((σ / 8) * (d2 / ‖g‖)) : ℝ) • g) := hinner_ge
      _ = (σ / 4) * ‖g‖ * d2 := hquadratic
      _ ≥ (σ * δ / 4) * d2 := hdelta_scaled
  simpa [g, d2] using hfinal

end

end
