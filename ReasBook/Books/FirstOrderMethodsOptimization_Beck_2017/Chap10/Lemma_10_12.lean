/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import Mathlib
import FirstOrderMethodsOptimization_Beck_2017.Chap05.Definition_5_1
import FirstOrderMethodsOptimization_Beck_2017.Chap10.Definition_10_5
import FirstOrderMethodsOptimization_Beck_2017.Chap10.GradientCocoercivity
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_42

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped Gradient

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Lemma 10.12 is a `bridge/view` theorem in the Chapter 10 proximal-gradient API. The owner
`gradient_mapping` from Definition 10.5 is already canonical; this file only specializes that
owner to a real-valued smooth term via the shared bridge/view surface `G[L; f, g]`. -/

/-- Helper for Lemma 10.12: the Chapter 10 prox-gradient point is the unique proximal point of
the scaled penalty at the forward-gradient input. -/
private lemma prox_gradient_operator_eq_singleton_forward
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    prox[((((1 / L : PosReal) : EReal) • g))] (x - (1 / (L : ℝ)) • ∇ f x) =
      {T[L; f, g] x} := by
  -- Unfold the source-facing prox-gradient operator into the singleton proximal step.
  simpa [proximal_gradient_step] using
    (prox_grad_operator_eq_singleton f.toEReal g L
      (interior_effective_domain_point_of_real f x))

/-- Helper for Lemma 10.12: convex global `L`-smoothness controls the gradient difference at the
prox-gradient pair `(x, T_L(x))` by the Chapter 5 cocoercivity inequality. -/
lemma convex_smooth_gradient_difference_sq_le
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) ≤
      (L : ℝ) *
        inner ℝ (∇ f (T[L; f, g] x) - ∇ f x) (T[L; f, g] x - x) := by
  have hcoco :
      (1 / (L : ℝ)) * ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) ≤
        inner ℝ (∇ f (T[L; f, g] x) - ∇ f x) (T[L; f, g] x - x) := by
    -- Specialize the Chapter 5 cocoercivity inequality to `(T_L(x), x)`.
    simpa using
      (gradient_cocoercive_of_convex_l_smooth_posReal
        (E := E) L hf_convex hf_smooth) (T[L; f, g] x) x
  have hmul := mul_le_mul_of_nonneg_left hcoco (le_of_lt L.2)
  have hL : (L : ℝ) * (1 / (L : ℝ)) = 1 := by
    field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
  -- Multiply the cocoercivity estimate by `L` to recover the textbook inequality.
  calc
    ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) =
        ((L : ℝ) * (1 / (L : ℝ))) *
          ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ) := by
            rw [hL, one_mul]
    _ = (L : ℝ) *
          ((1 / (L : ℝ)) * ‖∇ f (T[L; f, g] x) - ∇ f x‖ ^ (2 : ℕ)) := by
            rw [mul_assoc]
    _ ≤ (L : ℝ) *
          inner ℝ (∇ f (T[L; f, g] x) - ∇ f x) (T[L; f, g] x - x) := hmul

/-- Helper for Lemma 10.12: the two forward-gradient points entering the consecutive prox steps
are at most one prox-gradient step apart. -/
lemma prox_gradient_forward_points_dist_le_step
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖(x - (1 / (L : ℝ)) • ∇ f x) -
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))‖ ≤
      ‖x - T[L; f, g] x‖ := by
  let a := ∇ f (T[L; f, g] x) - ∇ f x
  let b := T[L; f, g] x - x
  have hgrad :
      ‖a‖ ^ (2 : ℕ) ≤ (L : ℝ) * inner ℝ a b := by
    -- Rewrite the Chapter 5 inequality in the compact `a,b` notation from the source proof.
    simpa [a, b] using
      convex_smooth_gradient_difference_sq_le
        f g L hf_convex hf_smooth x
  have hsq :
      ‖((1 / (L : ℝ)) • a) - b‖ ^ (2 : ℕ) ≤ ‖b‖ ^ (2 : ℕ) := by
    -- Expand the squared norm and reduce to the scalar inequality coming from `hgrad`.
    rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs,
      abs_of_pos (one_div_pos.mpr L.2), pow_two, inner_smul_left]
    simp only [starRingEnd_apply]
    have hLinv_nonneg : 0 ≤ (1 / (L : ℝ)) := le_of_lt (one_div_pos.mpr L.2)
    have hLinv : (1 / (L : ℝ)) * (L : ℝ) = 1 := by
      field_simp [show (L : ℝ) ≠ 0 from L.2.ne']
    have hdiv :
        (1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ) ≤ inner ℝ a b := by
      have hmul := mul_le_mul_of_nonneg_left hgrad hLinv_nonneg
      calc
        (1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ) ≤
            (1 / (L : ℝ)) * ((L : ℝ) * inner ℝ a b) := hmul
        _ = ((1 / (L : ℝ)) * (L : ℝ)) * inner ℝ a b := by rw [mul_assoc]
        _ = inner ℝ a b := by rw [hLinv, one_mul]
    have hinner_nonneg : 0 ≤ inner ℝ a b := by
      have hleft_nonneg : 0 ≤ (1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ) := by
        exact mul_nonneg hLinv_nonneg (sq_nonneg ‖a‖)
      exact le_trans hleft_nonneg hdiv
    have hdiv' :
        (1 / (L : ℝ)) * ((1 / (L : ℝ)) * ‖a‖ ^ (2 : ℕ)) ≤
          (1 / (L : ℝ)) * inner ℝ a b := by
      exact mul_le_mul_of_nonneg_left hdiv hLinv_nonneg
    have hsq_aux :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) ≤
          (1 / (L : ℝ)) * inner ℝ a b := by
      nlinarith [hdiv', norm_nonneg a]
    have hs_nonneg : 0 ≤ (1 / (L : ℝ)) * inner ℝ a b := by
      exact mul_nonneg hLinv_nonneg hinner_nonneg
    have htwice :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) ≤
          2 * ((1 / (L : ℝ)) * inner ℝ a b) := by
      nlinarith [hsq_aux, hs_nonneg]
    have hcore :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) -
          2 * ((1 / (L : ℝ)) * inner ℝ a b) ≤ 0 := by
      linarith [htwice]
    have hcore' :
        (1 / (L : ℝ)) * ‖a‖ * ((1 / (L : ℝ)) * ‖a‖) -
          2 * (star (1 / (L : ℝ)) * inner ℝ a b) ≤ 0 := by
      simpa using hcore
    linarith [hcore']
  have hnorm :
      ‖((1 / (L : ℝ)) • a) - b‖ ≤ ‖b‖ := by
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq
  have hforward :
      (x - (1 / (L : ℝ)) • ∇ f x) -
          (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x)) =
        ((1 / (L : ℝ)) • a) - b := by
    -- This is the exact forward-point difference from the source proof.
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Convert the compact estimate back to the original forward-gradient points.
  calc
    ‖(x - (1 / (L : ℝ)) • ∇ f x) -
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))‖ =
        ‖((1 / (L : ℝ)) • a) - b‖ := by
          rw [hforward]
    _ ≤ ‖b‖ := hnorm
    _ = ‖x - T[L; f, g] x‖ := by
          simp [b, norm_sub_rev]

/-- Helper for Lemma 10.12: nonexpansivity of the proximal map turns the forward-point estimate
into monotonicity of successive prox-gradient step lengths. -/
lemma prox_gradient_step_distance_monotone
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖T[L; f, g] x - T[L; f, g] (T[L; f, g] x)‖ ≤ ‖x - T[L; f, g] x‖ := by
  let hg_closed : LowerSemicontinuous g := Fact.out
  let hg_convex : is_convex_function g := Fact.out
  let hg_scaled :=
    scaled_function_proper_closed_convex_of_pos g inferInstance hg_closed hg_convex (1 / L)
  have hx :
      prox[((((1 / L : PosReal) : EReal) • g))]
        (x - (1 / (L : ℝ)) • ∇ f x) =
          {T[L; f, g] x} := by
    -- The Chapter 10 prox-gradient point is exactly the unique proximal point at the forward input.
    simpa using prox_gradient_operator_eq_singleton_forward f g L x
  have hy :
      prox[((((1 / L : PosReal) : EReal) • g))]
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x)) =
          {T[L; f, g] (T[L; f, g] x)} := by
    -- Apply the same singleton description one step later.
    simpa using
      prox_gradient_operator_eq_singleton_forward
        f g L (T[L; f, g] x)
  have hnonexp :
      ‖T[L; f, g] x - T[L; f, g] (T[L; f, g] x)‖ ≤
        ‖(x - (1 / (L : ℝ)) • ∇ f x) -
          (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))‖ := by
    -- Proximal nonexpansivity compares the two consecutive prox-gradient updates.
    simpa [norm_sub_rev] using
      @prox_eq_singleton_nonexpansive E _ _
        ((((1 / L : PosReal) : EReal) • g))
        (x - (1 / (L : ℝ)) • ∇ f x)
        (T[L; f, g] x - (1 / (L : ℝ)) • ∇ f (T[L; f, g] x))
        (T[L; f, g] x)
        (T[L; f, g] (T[L; f, g] x))
        hg_scaled.1 hg_scaled.2.1 hg_scaled.2.2 hx hy
  -- Chain nonexpansivity with the forward-point estimate proved above.
  exact
    le_trans hnonexp <|
      prox_gradient_forward_points_dist_le_step
        f g L hf_convex hf_smooth x

-- Route correction: this proof follows the textbook forward-point comparison plus proximal
-- nonexpansivity, rather than the earlier residual-cocoercivity shortcut.
/-- Lemma 10.12: if `f` is convex and globally `L`-smooth for a positive
stepsize `L`, and `g` is proper closed convex, then one prox-gradient step
does not increase the norm of the gradient mapping:
`‖G_L(T_L(x))‖ ≤ ‖G_L(x)‖`. -/
theorem prox_grad_step_gradient_mapping_norm_monotone
    (f : E → ℝ) (g : E → EReal) (L : PosReal)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_smooth : is_l_smooth_on f Set.univ (PosReal.toNNReal L))
    [IsProperExtendedRealFunction g] [Fact (LowerSemicontinuous g)]
    [Fact (is_convex_function g)] (x : E) :
    ‖G[L; f, g] (T[L; f, g] x)‖ ≤ ‖G[L; f, g] x‖ := by
  let xPlus := T[L; f, g] x
  let xNext := T[L; f, g] xPlus
  have hstep :
      ‖xPlus - xNext‖ ≤ ‖x - xPlus‖ := by
    -- First compare the lengths of two consecutive prox-gradient steps.
    simpa [xPlus, xNext] using
      prox_gradient_step_distance_monotone
        f g L hf_convex hf_smooth x
  have hmul := mul_le_mul_of_nonneg_left hstep (le_of_lt L.2)
  have hGxPlus :
      ‖G[L; f, g] xPlus‖ = (L : ℝ) * ‖xPlus - xNext‖ := by
    -- Rewrite the residual at `x⁺` as the scaled step `L (x⁺ - x⁺⁺)`.
    calc
      ‖G[L; f, g] xPlus‖ =
          ‖(L : ℝ) •
              ((interior_effective_domain_point_of_real f xPlus : E) -
                T[L, f.toEReal, g] (interior_effective_domain_point_of_real f xPlus))‖ := by
            rw [prox_gradient_mapping_apply, gradient_mapping_apply]
      _ = (L : ℝ) *
            ‖(interior_effective_domain_point_of_real f xPlus : E) -
              T[L, f.toEReal, g] (interior_effective_domain_point_of_real f xPlus)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_of_lt L.2)]
      _ = (L : ℝ) * ‖xPlus - xNext‖ := by
            congr 1
  have hGx :
      ‖G[L; f, g] x‖ = (L : ℝ) * ‖x - xPlus‖ := by
    -- The same residual rewrite at the original point gives the right-hand side.
    calc
      ‖G[L; f, g] x‖ =
          ‖(L : ℝ) •
              ((interior_effective_domain_point_of_real f x : E) -
                T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x))‖ := by
            rw [prox_gradient_mapping_apply, gradient_mapping_apply]
      _ = (L : ℝ) *
            ‖(interior_effective_domain_point_of_real f x : E) -
              T[L, f.toEReal, g] (interior_effective_domain_point_of_real f x)‖ := by
            rw [norm_smul, Real.norm_of_nonneg (le_of_lt L.2)]
      _ = (L : ℝ) * ‖x - xPlus‖ := by
            congr 1
  -- After both residual rewrites, the theorem is exactly the step-length monotonicity above.
  calc
    ‖G[L; f, g] (T[L; f, g] x)‖ = ‖G[L; f, g] xPlus‖ := by simp [xPlus]
    _ = (L : ℝ) * ‖xPlus - xNext‖ := hGxPlus
    _ ≤ (L : ℝ) * ‖x - xPlus‖ := hmul
    _ = ‖G[L; f, g] x‖ := hGx.symm

end
