/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.GradientCocoercivity
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_42
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

section Lemma1011

variable (f : E → ℝ) (g : E → EReal) (L : PosReal)
variable [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
  [Fact (is_convex_function g)]

/- Lemma 10.11 mixes three layers of the Chapter 10 proximal-gradient API:
- `source-facing`: the cocoercive inner-product inequality for the residual `G[L; f, g]`;
- `core/canonical`: the `LipschitzWith` regularity statement for that same owner;
- `bridge/view`: the pointwise norm estimate, derived below from `LipschitzWith.dist_le_mul`.

The owner abstraction remains Definition 10.5's proximal-gradient mapping `G[L; f, g]`; this file
should not introduce a parallel wrapper for the same residual. -/

/-- Helper for Lemma 10.11: the Chapter 10 prox-gradient operator is the unique proximal point of
the scaled penalty at the forward-gradient input. -/
private lemma prox_gradient_operator_eq_singleton_forward (x : E) :
    prox[((((1 / L : PosReal) : EReal) • g))] (x - (1 / (L : ℝ)) • ∇ f x) =
      {T[L; f, g] x} := by
  -- The source-facing prox-gradient operator is defined by choosing the singleton proximal point
  -- of the forward-gradient step.
  simpa [proximal_gradient_step] using
    (prox_grad_operator_eq_singleton f.toEReal g L
      (interior_effective_domain_point_of_real f x))

/-- Helper for Lemma 10.11: the prox-gradient update equals the identity minus the scaled gradient
mapping residual. -/
lemma prox_gradient_operator_eq_sub_gradient_mapping (x : E) :
    T[L; f, g] x = x - (1 / (L : ℝ)) • G[L; f, g] x := by
  have hG :
      G[L; f, g] x = (L : ℝ) • (x - T[L; f, g] x) := by
    calc
      G[L; f, g] x = G[L, f.toEReal, g] (interior_effective_domain_point_of_real f x) := by
        rfl
      _ =
          (L : ℝ) •
            (((interior_effective_domain_point_of_real f x : interior (effective_domain f.toEReal))
              : E) - T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x)) := by
            exact
              gradient_mapping_apply (f.toEReal) g L
                (interior_effective_domain_point_of_real f x)
      _ = (L : ℝ) • (x - T[L; f, g] x) := by
            rfl
  have hL : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
  -- Solve the defining identity `G_L(x) = L • (x - T_L(x))` for `T_L(x)`.
  calc
    T[L; f, g] x = x - (x - T[L; f, g] x) := by
      exact (sub_sub_cancel x (T[L; f, g] x)).symm
    _ = x - (1 / (L : ℝ)) • G[L; f, g] x := by
      rw [hG, smul_smul, hL, one_smul]

/-- Helper for Lemma 10.11: the difference of the two forward-gradient base points splits into the
prox-gradient step difference plus the residual gap `G_L - ∇f`. -/
lemma prox_gradient_forward_difference_eq_step_add_residual_gap (x y : E) :
    (x - (1 / (L : ℝ)) • ∇ f x) - (y - (1 / (L : ℝ)) • ∇ f y) =
      (T[L; f, g] x - T[L; f, g] y) +
        (1 / (L : ℝ)) •
          ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y)) := by
  -- Rewrite each prox-gradient step as `id - (1 / L) G_L` and then collect the residual gap.
  rw [prox_gradient_operator_eq_sub_gradient_mapping]
  rw [prox_gradient_operator_eq_sub_gradient_mapping]
  simp only [sub_eq_add_neg, add_assoc]
  module

/-- Helper for Lemma 10.11: expanding the cross term from the firm-nonexpansive step gives the
scalar inequality surface used in the textbook proof. -/
lemma prox_gradient_cross_term_expansion (x y : E) :
    inner ℝ
        ((x - y) - (1 / (L : ℝ)) • (G[L; f, g] x - G[L; f, g] y))
        ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y)) =
      inner ℝ (G[L; f, g] x - G[L; f, g] y) (x - y) -
        inner ℝ (∇ f x - ∇ f y) (x - y) -
        (1 / (L : ℝ)) * ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) +
        (1 / (L : ℝ)) *
          inner ℝ (G[L; f, g] x - G[L; f, g] y) (∇ f x - ∇ f y) := by
  -- Expand the bilinear form once so the main theorem can stay on the scalar side.
  let dG := G[L; f, g] x - G[L; f, g] y
  let dGrad := ∇ f x - ∇ f y
  have hdG_pair :
      inner ℝ dG (dG - dGrad) = ‖dG‖ ^ (2 : ℕ) - inner ℝ dG dGrad := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  have hcore :
      inner ℝ ((x - y) - (1 / (L : ℝ)) • dG) (dG - dGrad) =
        inner ℝ (x - y) dG - inner ℝ (x - y) dGrad -
          (1 / (L : ℝ)) * (‖dG‖ ^ (2 : ℕ) - inner ℝ dG dGrad) := by
    rw [inner_sub_left, inner_sub_right, real_inner_smul_left, hdG_pair]
  calc
    inner ℝ
        ((x - y) - (1 / (L : ℝ)) • (G[L; f, g] x - G[L; f, g] y))
        ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y)) =
      inner ℝ ((x - y) - (1 / (L : ℝ)) • dG) (dG - dGrad) := by
        simp [dG, dGrad]
    _ = inner ℝ (x - y) dG - inner ℝ (x - y) dGrad -
          (1 / (L : ℝ)) * (‖dG‖ ^ (2 : ℕ) - inner ℝ dG dGrad) := hcore
    _ = inner ℝ dG (x - y) - inner ℝ dGrad (x - y) -
          (1 / (L : ℝ)) * ‖dG‖ ^ (2 : ℕ) +
          (1 / (L : ℝ)) * inner ℝ dG dGrad := by
        rw [real_inner_comm (x - y) dG, real_inner_comm (x - y) dGrad]
        ring

/-- Helper for Lemma 10.11: the mixed quadratic term from the source proof always dominates
three quarters of the first square. -/
lemma mixed_quadratic_lower_bound_three_quarters (a b : ℝ) :
    (3 / 4 : ℝ) * a ^ (2 : ℕ) ≤ a ^ (2 : ℕ) + b ^ (2 : ℕ) - a * b := by
  -- Complete the square exactly as in the textbook proof.
  nlinarith [sq_nonneg (a / 2 - b)]

/-- Helper for Lemma 10.11: firm nonexpansivity of the proximal map yields the nonnegative
cross-term appearing in the source proof after rewriting `T_L = I - (1 / L) G_L`. -/
lemma prox_gradient_cross_term_nonneg (x y : E) :
    0 ≤
      inner ℝ
        ((x - y) - (1 / (L : ℝ)) • (G[L; f, g] x - G[L; f, g] y))
        ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y)) := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  have hfirm :
      inner ℝ
          ((x - (1 / (L : ℝ)) • ∇ f x) - (y - (1 / (L : ℝ)) • ∇ f y))
          (T[L; f, g] x - T[L; f, g] y) ≥
        ‖T[L; f, g] x - T[L; f, g] y‖ ^ (2 : ℕ) := by
    -- Apply firm nonexpansivity to the singleton proximal points at the two forward inputs.
    exact
      prox_eq_singleton_firmly_nonexpansive
        ((((1 / L : PosReal) : EReal) • g))
        (x - (1 / (L : ℝ)) • ∇ f x)
        (y - (1 / (L : ℝ)) • ∇ f y)
        (T[L; f, g] x)
        (T[L; f, g] y)
        hg_scaled.1
        hg_scaled.2.1
        hg_scaled.2.2
        (prox_gradient_operator_eq_singleton_forward f g L x)
        (prox_gradient_operator_eq_singleton_forward f g L y)
  have hscaled_nonneg :
      0 ≤
        (1 / (L : ℝ)) *
          inner ℝ
            ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y))
            (T[L; f, g] x - T[L; f, g] y) := by
    -- Rewrite the forward-point difference as `step + (1 / L) • residualGap` and cancel
    -- the common `‖step‖²` term.
    have hrewrite :
        inner ℝ
            ((x - (1 / (L : ℝ)) • ∇ f x) - (y - (1 / (L : ℝ)) • ∇ f y))
            (T[L; f, g] x - T[L; f, g] y) =
          ‖T[L; f, g] x - T[L; f, g] y‖ ^ (2 : ℕ) +
            (1 / (L : ℝ)) *
              inner ℝ
                ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y))
                (T[L; f, g] x - T[L; f, g] y) := by
      rw [prox_gradient_forward_difference_eq_step_add_residual_gap f g L]
      rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have hfirm' :
        ‖T[L; f, g] x - T[L; f, g] y‖ ^ (2 : ℕ) +
            (1 / (L : ℝ)) *
              inner ℝ
                ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y))
                (T[L; f, g] x - T[L; f, g] y) ≥
          ‖T[L; f, g] x - T[L; f, g] y‖ ^ (2 : ℕ) := by
      rw [← hrewrite]
      exact hfirm
    linarith
  have hcross_nonneg :
      0 ≤
        inner ℝ
          ((G[L; f, g] x - G[L; f, g] y) - (∇ f x - ∇ f y))
          (T[L; f, g] x - T[L; f, g] y) := by
    -- The scalar factor `1 / L` is positive, so it can be removed.
    have hLinv_pos : 0 < (1 / (L : ℝ)) := by
      exact one_div_pos.mpr L.2
    nlinarith
      [hscaled_nonneg, hLinv_pos]
  have hstep :
      T[L; f, g] x - T[L; f, g] y =
        (x - y) - (1 / (L : ℝ)) • (G[L; f, g] x - G[L; f, g] y) := by
    -- Normalize the prox-gradient step difference into the residual form from the statement.
    rw [prox_gradient_operator_eq_sub_gradient_mapping]
    rw [prox_gradient_operator_eq_sub_gradient_mapping]
    simp only [sub_eq_add_neg, add_assoc]
    module
  -- Replace the step difference by the residual form and swap the real inner-product arguments.
  simpa [hstep, real_inner_comm] using hcross_nonneg

/-- Lemma 10.11 (1): if `f` is convex and globally `L`-smooth and `g` is proper closed convex,
then the specialized Chapter 10 gradient mapping satisfies
`⟪G[L; f, g] x - G[L; f, g] y, x - y⟫ ≥
  (3 / (4L)) ‖G[L; f, g] x - G[L; f, g] y‖²`. -/
theorem prox_gradient_mapping_cocoercive
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    (x y : E) :
    inner ℝ (G[L; f, g] x - G[L; f, g] y) (x - y) ≥
      (3 / (4 * (L : ℝ))) *
        ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) := by
  let dG := G[L; f, g] x - G[L; f, g] y
  let dGrad := ∇ f x - ∇ f y
  have hcross :
      0 ≤
        inner ℝ dG (x - y) - inner ℝ dGrad (x - y) -
          (1 / (L : ℝ)) * ‖dG‖ ^ (2 : ℕ) +
          (1 / (L : ℝ)) * inner ℝ dG dGrad := by
    -- Route correction: expand the firm-nonexpansive cross term only after reaching the abstract
    -- nonnegative residual inequality.
    have hcross0 :=
      prox_gradient_cross_term_nonneg f g L x y
    rw [prox_gradient_cross_term_expansion f g L x y] at hcross0
    simpa [dG, dGrad] using hcross0
  have hgrad :
      (1 / (L : ℝ)) * ‖dGrad‖ ^ (2 : ℕ) ≤ inner ℝ dGrad (x - y) := by
    -- Insert the Chapter 5 cocoercivity estimate for the smooth gradient.
    simpa [dGrad] using
      (gradient_cocoercive_of_convex_l_smooth_posReal
        (E := E) L hf_convex hf_smooth) x y
  have hcs :
      inner ℝ dG dGrad ≤ ‖dG‖ * ‖dGrad‖ := by
    -- Cauchy--Schwarz controls the mixed inner product.
    exact real_inner_le_norm dG dGrad
  have hLinv_nonneg : 0 ≤ (1 / (L : ℝ)) := by
    exact le_of_lt (one_div_pos.mpr L.2)
  have hcs_scaled :
      (1 / (L : ℝ)) * inner ℝ dG dGrad ≤
        (1 / (L : ℝ)) * (‖dG‖ * ‖dGrad‖) := by
    exact mul_le_mul_of_nonneg_left hcs hLinv_nonneg
  have hlower :
      inner ℝ dG (x - y) ≥
        (1 / (L : ℝ)) *
          (‖dG‖ ^ (2 : ℕ) + ‖dGrad‖ ^ (2 : ℕ) - ‖dG‖ * ‖dGrad‖) := by
    -- Collect the nonnegative cross term, gradient cocoercivity, and Cauchy--Schwarz on the
    -- exact scalar surface of the source proof.
    nlinarith
      [hcross, hgrad, hcs_scaled]
  have hmixed :
      (3 / 4 : ℝ) * ‖dG‖ ^ (2 : ℕ) ≤
        ‖dG‖ ^ (2 : ℕ) + ‖dGrad‖ ^ (2 : ℕ) - ‖dG‖ * ‖dGrad‖ := by
    -- The last scalar step is the textbook completed-square inequality.
    exact mixed_quadratic_lower_bound_three_quarters ‖dG‖ ‖dGrad‖
  have hmixed_scaled :
      (1 / (L : ℝ)) * ((3 / 4 : ℝ) * ‖dG‖ ^ (2 : ℕ)) ≤
        (1 / (L : ℝ)) *
          (‖dG‖ ^ (2 : ℕ) + ‖dGrad‖ ^ (2 : ℕ) - ‖dG‖ * ‖dGrad‖) := by
    exact mul_le_mul_of_nonneg_left hmixed hLinv_nonneg
  have hcoeff :
      (1 / (L : ℝ)) * ((3 / 4 : ℝ) * ‖dG‖ ^ (2 : ℕ)) =
        (3 / (4 * (L : ℝ))) * ‖dG‖ ^ (2 : ℕ) := by
    field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
  -- Chain the quadratic lower bound back to the stated `3 / (4L)` inequality.
  calc
    inner ℝ dG (x - y) ≥
        (1 / (L : ℝ)) *
          (‖dG‖ ^ (2 : ℕ) + ‖dGrad‖ ^ (2 : ℕ) - ‖dG‖ * ‖dGrad‖) :=
      hlower
    _ ≥ (1 / (L : ℝ)) * ((3 / 4 : ℝ) * ‖dG‖ ^ (2 : ℕ)) := by
      exact hmixed_scaled
    _ = (3 / (4 * (L : ℝ))) * ‖dG‖ ^ (2 : ℕ) := hcoeff

-- Proof sketch: combine part (1) with Cauchy-Schwarz:
-- `‖G[L; f, g] x - G[L; f, g] y‖² ≤
-- (4L / 3) ⟪G[L; f, g] x - G[L; f, g] y, x - y⟫ ≤
-- (4L / 3) ‖G[L; f, g] x - G[L; f, g] y‖ ‖x - y‖`, then divide by
-- `‖G[L; f, g] x - G[L; f, g] y‖` in the nontrivial case. The public owner-level regularity
-- statement is phrased through `LipschitzWith`, matching the canonical Chapter 10 API from
-- Lemma 10.10.
/-- Lemma 10.11 (2): under the same hypotheses, the proximal-gradient mapping is
`(4L / 3)`-Lipschitz. -/
theorem prox_gradient_mapping_lipschitz
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    :
    LipschitzWith (Real.toNNReal (((4 : ℝ) * (L : ℝ)) / 3))
      (G[L; f, g]) := by
  have hcoeff_nonneg : 0 ≤ (((4 : ℝ) * (L : ℝ)) / 3) := by
    exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt L.2)) (by norm_num)
  rw [lipschitzWith_iff_norm_sub_le]
  intro x y
  by_cases hzero : G[L; f, g] x = G[L; f, g] y
  · -- The degenerate case is immediate.
    have hzero_sub : G[L; f, g] x - G[L; f, g] y = 0 := by
      exact sub_eq_zero.mpr hzero
    simpa [Real.toNNReal_of_nonneg hcoeff_nonneg] using
      (show ‖G[L; f, g] x - G[L; f, g] y‖ ≤
          (Real.toNNReal (((4 : ℝ) * (L : ℝ)) / 3) : ℝ) * ‖x - y‖ from by
        rw [hzero_sub, norm_zero]
        positivity)
  · have hcoco :
        (3 / (4 * (L : ℝ))) *
            ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) ≤
          inner ℝ (G[L; f, g] x - G[L; f, g] y) (x - y) := by
      simpa using
        prox_gradient_mapping_cocoercive
          f g L hf_convex hf_smooth x y
    have hcs :
        inner ℝ (G[L; f, g] x - G[L; f, g] y) (x - y) ≤
          ‖G[L; f, g] x - G[L; f, g] y‖ * ‖x - y‖ := by
      exact real_inner_le_norm _ _
    have hbound :
        ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) ≤
          ‖G[L; f, g] x - G[L; f, g] y‖ *
            ((((4 : ℝ) * (L : ℝ)) / 3) * ‖x - y‖) := by
      have haux :
          (3 / (4 * (L : ℝ))) * ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) ≤
            ‖G[L; f, g] x - G[L; f, g] y‖ * ‖x - y‖ := by
        exact le_trans hcoco hcs
      have hmul :=
        mul_le_mul_of_nonneg_left haux hcoeff_nonneg
      have hfactor :
          (((4 : ℝ) * (L : ℝ)) / 3) * (3 / (4 * (L : ℝ))) = 1 := by
        field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
      calc
        ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) =
            ((((4 : ℝ) * (L : ℝ)) / 3) *
              (3 / (4 * (L : ℝ)))) *
              ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ) := by
                rw [hfactor, one_mul]
        _ = (((4 : ℝ) * (L : ℝ)) / 3) *
              ((3 / (4 * (L : ℝ))) *
                ‖G[L; f, g] x - G[L; f, g] y‖ ^ (2 : ℕ)) := by
                ring
        _ ≤ (((4 : ℝ) * (L : ℝ)) / 3) *
              (‖G[L; f, g] x - G[L; f, g] y‖ * ‖x - y‖) := hmul
        _ = ‖G[L; f, g] x - G[L; f, g] y‖ *
              ((((4 : ℝ) * (L : ℝ)) / 3) * ‖x - y‖) := by
                ring
    have hnorm_pos : 0 < ‖G[L; f, g] x - G[L; f, g] y‖ := by
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hzero)
    rw [pow_two] at hbound
    -- Cancel the nonzero norm factor exactly as in the Chapter 6 nonexpansive template.
    simpa [Real.toNNReal_of_nonneg hcoeff_nonneg, mul_assoc] using
      le_of_mul_le_mul_left hbound hnorm_pos

/-- The pointwise norm inequality form of Lemma 10.11 (2), derived from the canonical
`LipschitzWith` statement above. -/
theorem prox_gradient_mapping_lipschitz_norm_sub_le
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    (x y : E) :
    ‖G[L; f, g] x - G[L; f, g] y‖ ≤ ((4 : ℝ) * (L : ℝ) / 3) * ‖x - y‖ := by
  have hcoeff : 0 ≤ ((4 : ℝ) * (L : ℝ) / 3) := by
    exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt L.2)) (by norm_num)
  simpa [dist_eq_norm, Real.toNNReal_of_nonneg hcoeff] using
    (prox_gradient_mapping_lipschitz f g L hf_convex hf_smooth).dist_le_mul x y

end Lemma1011

end
