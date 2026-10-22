/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Algorithm_2_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_5
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_10
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_6_6

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient SmoothConvex

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "p" => normSeminorm ℝ E

/-
Primary domain: smooth-convex accelerated first-order methods on real inner-product spaces.

Owner declarations sampled before refining this file:
* `ConvexOn ℝ Set.univ f`, `ContDiff ℝ 1 f`, and `LipschitzWith L (∇ f)` are the intrinsic
  smooth-convex objective data on the ambient real Hilbert space;
* `f ∈ 𝓕[L, normSeminorm ℝ E]¹¹` in `Theorem_2_5` is the finite-dimensional Chapter 2 bridge
  to that intrinsic owner layer;
* `ConstantStepSchemeIIMomentumRecurrence` in `Algorithm_2_4` owns the type-II acceleration data
  `(x_k, y_k, α_k)` together with the scalar and momentum recurrences.
* `ConstantStepSchemeIIRecurrence` in `Algorithm_2_4` adds the analytic side conditions for the
  same owner trajectory.
* `Theorem_2_16` shows the nearby chapter pattern: keep the accelerated trajectory as the
  source-facing owner and use `f ∈ 𝓕[L, p]¹¹` only as a finite-dimensional bridge, not as the
  primitive objective package.

Primitive data here are therefore the owner type-II recurrence specialized to `q_f = 0`,
`α₀ = 1`, together with the intrinsic smooth-convex hypotheses
`ConvexOn ℝ Set.univ f`, `ContDiff ℝ 1 f`, `LipschitzWith L (∇ f)`, and a minimizer `x*`.
The textbook parameters `t_k` are derived from the owner scalar sequence by `t_k = 1 / α_k`, so
this file keeps only bridge/view companion lemmas for that textbook reformulation on the
differentiable type-II owner. The chapter notation `f ∈ 𝓕[L, p]¹¹` is kept only as a thin
finite-dimensional specialization theorem for the main rate statement.
-/

namespace ConstantStepSchemeIIRecurrence

section

variable {L : NNReal}
variable {f : E → ℝ}
variable {x0 xStar : E}
variable
  (scheme :
    _root_.ConstantStepSchemeIIRecurrence
      E E f (L : ℝ) 0 x0 1)

local notation "t" => fun k : ℕ ↦ 1 / scheme.alpha k

private theorem alpha_pos
    (k : ℕ) :
    0 < scheme.alpha k := by
  cases k with
  | zero =>
      simp [scheme.alpha_zero]
  | succ k =>
      exact (scheme.alpha_succ_mem_Ioo k).1

/-- In the Proposition 2.10 specialization `q_f = 0`, `α₀ = 1`, the textbook parameter `t₀`
recovered from the owner scalar sequence by `t_k = 1 / α_k` is `1`. -/
theorem t_zero
    : t 0 = 1 := by
  change 1 / scheme.alpha 0 = 1
  simpa using congrArg (fun a : ℝ ↦ 1 / a) scheme.alpha_zero

/-- In the Proposition 2.10 specialization `q_f = 0`, the reciprocals `t_k = 1 / α_k` satisfy
the textbook scalar recurrence `t_{k+1} = (1 + sqrt (1 + 4 t_k^2)) / 2`. -/
theorem t_succ_eq_textbook
    (k : ℕ) :
    t (k + 1) = (1 + Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) / 2 := by
  have ht_sq :
      (t (k + 1)) ^ (2 : ℕ) =
        t (k + 1) + (t k) ^ (2 : ℕ) := by
    have hαk_ne : scheme.alpha k ≠ 0 := ne_of_gt (alpha_pos scheme k)
    have hαk1_ne : scheme.alpha (k + 1) ≠ 0 := ne_of_gt (alpha_pos scheme (k + 1))
    have hrec :
        (1 / scheme.alpha (k + 1)) ^ (2 : ℕ) =
          1 / scheme.alpha (k + 1) + (1 / scheme.alpha k) ^ (2 : ℕ) := by
      field_simp [hαk_ne, hαk1_ne]
      nlinarith [scheme.alpha_succ_equation k]
    change
      (1 / scheme.alpha (k + 1)) ^ (2 : ℕ) =
        1 / scheme.alpha (k + 1) + (1 / scheme.alpha k) ^ (2 : ℕ)
    exact hrec
  have hsq :
      (2 * t (k + 1) - 1) ^ (2 : ℕ) =
        1 + 4 * (t k) ^ (2 : ℕ) := by
    nlinarith [ht_sq]
  have hnonneg : 0 ≤ 2 * t (k + 1) - 1 := by
    have ht_gt_one : 1 < t (k + 1) := by
      change 1 < 1 / scheme.alpha (k + 1)
      exact one_lt_one_div (alpha_pos scheme (k + 1)) (scheme.alpha_succ_mem_Ioo k).2
    nlinarith
  have hsqrt :
      Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ)) =
        2 * t (k + 1) - 1 := by
    have hsqrt_sq :
        (Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) ^ (2 : ℕ) =
          (2 * t (k + 1) - 1) ^ (2 : ℕ) := by
      rw [Real.sq_sqrt]
      · exact hsq.symm
      · positivity
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsqrt_sq with hEq | hEq
    · exact hEq
    · have hsqrt_nonneg : 0 ≤ Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ)) := Real.sqrt_nonneg _
      linarith
  nlinarith [hsqrt]

/-- In the Proposition 2.10 specialization `q_f = 0`, the owner momentum update rewrites as the
textbook formula `y_{k+1} = x_{k+1} + ((t_k - 1) / t_{k+1}) (x_{k+1} - x_k)` with
`t_k = 1 / α_k`. -/
theorem y_succ_eq_textbook
    (k : ℕ) :
    scheme.y (k + 1) =
      scheme.x (k + 1) +
        ((t k - 1) / t (k + 1)) •
          (scheme.x (k + 1) - scheme.x k) := by
  have hcoeff :
      (scheme.alpha k * (1 - scheme.alpha k)) /
          (scheme.alpha k ^ (2 : ℕ) + scheme.alpha (k + 1)) =
        (t k - 1) / t (k + 1) := by
    have hαk : 0 < scheme.alpha k := alpha_pos scheme k
    have hαk1 : 0 < scheme.alpha (k + 1) := alpha_pos scheme (k + 1)
    change
      (scheme.alpha k * (1 - scheme.alpha k)) /
          (scheme.alpha k ^ (2 : ℕ) + scheme.alpha (k + 1)) =
        ((1 / scheme.alpha k) - 1) / (1 / scheme.alpha (k + 1))
    field_simp [ne_of_gt hαk, ne_of_gt hαk1]
    nlinarith [scheme.alpha_succ_equation k]
  simpa [hcoeff] using scheme.y_succ k

/-- Helper for Proposition 2.10: the textbook scalar sequence satisfies the quadratic identity
`t_{k+1}^2 - t_{k+1} = t_k^2`. -/
private lemma t_succ_sq_sub_t_succ_eq_t_sq
    (k : ℕ) :
    (t (k + 1)) ^ (2 : ℕ) - t (k + 1) = (t k) ^ (2 : ℕ) := by
  -- Clear the reciprocal denominators in the owner scalar equation.
  have hαk_ne : scheme.alpha k ≠ 0 := ne_of_gt (alpha_pos scheme k)
  have hαk1_ne : scheme.alpha (k + 1) ≠ 0 := ne_of_gt (alpha_pos scheme (k + 1))
  change
    (1 / scheme.alpha (k + 1)) ^ (2 : ℕ) - 1 / scheme.alpha (k + 1) =
      (1 / scheme.alpha k) ^ (2 : ℕ)
  field_simp [hαk_ne, hαk1_ne]
  nlinarith [scheme.alpha_succ_equation k]

/-- Helper for Proposition 2.10: the initial objective gap is bounded by the quadratic Taylor
upper model at the minimizer. -/
private lemma initial_objective_gap_le_half_lipschitz_sqdist
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar) :
    f (scheme.x 0) - f xStar ≤ ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
  have hgrad_zero : ∇ f xStar = 0 :=
    isMinOn_gradient_eq_zero hxStar
  -- Apply the smooth Taylor upper bound at the minimizer and kill the linear term.
  calc
    f (scheme.x 0) - f xStar
        ≤ firstOrderTaylorModelAt f xStar (scheme.x 0) - f xStar +
            ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
          have hupper :=
            taylor_upper_bound_of_contDiffOne_withLipschitzGradient
              hcontDiff hgrad_lipschitz xStar (scheme.x 0)
          simpa [firstOrderTaylorModelAt_apply, hgrad_zero, add_comm, add_left_comm, add_assoc]
            using hupper
    _ = ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
          simp [hgrad_zero]

/-- Helper for Proposition 2.10: the textbook scalar sequence grows by at least `1 / 2` at each
step. -/
private lemma t_succ_ge_add_half
    (k : ℕ) :
    t k + (1 : ℝ) / 2 ≤ t (k + 1) := by
  -- Compare the textbook square root with `2 * t_k` and rewrite the recurrence.
  rw [t_succ_eq_textbook scheme k]
  have ht_nonneg : 0 ≤ t k := le_of_lt (one_div_pos.mpr (alpha_pos scheme k))
  have hsq :
      (2 * t k) ^ (2 : ℕ) ≤
        (Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ))) ^ (2 : ℕ) := by
    rw [Real.sq_sqrt]
    · nlinarith
    · positivity
  have hsqrt_lower : 2 * t k ≤ Real.sqrt (1 + 4 * (t k) ^ (2 : ℕ)) := by
    nlinarith [hsq, Real.sqrt_nonneg (1 + 4 * (t k) ^ (2 : ℕ))]
  nlinarith

/-- Helper for Proposition 2.10: the textbook sequence satisfies the elementary lower bound
`(k + 2) / 2 ≤ t_k`. -/
private lemma nat_add_two_div_two_le_t
    : ∀ k : ℕ, ((k + 2 : ℕ) : ℝ) / 2 ≤ t k := by
  intro k
  induction k with
  | zero =>
      -- Start the induction from the explicit initial scalar `t₀ = 1`.
      norm_num [t_zero scheme]
  | succ k hk =>
      -- Each step adds at least `1 / 2`, so the arithmetic lower bound propagates.
      have hstep := t_succ_ge_add_half scheme k
      have hnext : (((k + 3 : ℕ) : ℝ) / 2) ≤ t (k + 1) := by
        have hk' : (((k + 2 : ℕ) : ℝ) / 2) + (1 : ℝ) / 2 ≤ t (k + 1) := by
          nlinarith
        have harith :
            (((k + 3 : ℕ) : ℝ) / 2) = (((k + 2 : ℕ) : ℝ) / 2) + (1 : ℝ) / 2 := by
          have harith' : ((k : ℝ) + 3) / 2 = ((k : ℝ) + 2) / 2 + (1 : ℝ) / 2 := by
            ring
          simpa [Nat.cast_add, add_assoc] using harith'
        rw [harith]
        exact hk'
      simpa [Nat.succ_eq_add_one, add_assoc] using hnext

/-- Helper for Proposition 2.10: the transformed auxiliary point
`z_k = t_k y_k - (t_k - 1) x_k`. -/
private def textbookAuxPoint
    (k : ℕ) : E :=
  (t k) • scheme.y k - (t k - 1) • scheme.x k

/-- Helper for Proposition 2.10: the transformed auxiliary point starts from the initial
iterate. -/
private lemma textbook_aux_point_zero :
    textbookAuxPoint scheme 0 = scheme.x 0 := by
  -- At time `0`, both owner trajectories start from `x₀` and `t₀ = 1`.
  have hyx : scheme.y 0 = scheme.x 0 := by
    simpa [scheme.x_zero] using scheme.y_zero
  simp [textbookAuxPoint, t_zero scheme, hyx]

/-- Helper for Proposition 2.10: the transformed auxiliary point relative to the minimizer splits
into the base displacement and the momentum correction. -/
private lemma textbook_aux_point_affine_identity
    (k : ℕ) :
    textbookAuxPoint scheme k - xStar =
      (scheme.y k - xStar) + (t k - 1) • (scheme.y k - scheme.x k) := by
  -- Separate the `1 • y_k` part from `t_k • y_k` and then regroup the affine terms.
  have ht :
      (t k) • scheme.y k = scheme.y k + (t k - 1) • scheme.y k := by
    calc
      (t k) • scheme.y k = (1 + (t k - 1)) • scheme.y k := by
        congr 1
        ring
      _ = scheme.y k + (t k - 1) • scheme.y k := by
        rw [add_smul, one_smul]
  rw [textbookAuxPoint, ht, smul_sub, sub_eq_add_neg]
  abel

/-- Helper for Proposition 2.10: the momentum coefficient in the textbook `y_{k+1}` update
collapses after multiplication by `t_{k+1}`. -/
private lemma scaled_momentum_coefficient_smul
    (k : ℕ)
    (v : E) :
    (t (k + 1)) • (((t k - 1) / t (k + 1)) • v) = (t k - 1) • v := by
  -- Cancel the explicit `t_{k+1}` denominator before returning to module notation.
  have ht_ne : t (k + 1) ≠ 0 := by
    exact ne_of_gt (one_div_pos.mpr (alpha_pos scheme (k + 1)))
  calc
    (t (k + 1)) • (((t k - 1) / t (k + 1)) • v)
        = (t (k + 1) * ((t k - 1) / t (k + 1))) • v := by
            rw [smul_smul]
    _ = ((t k - 1) * (t (k + 1) * (t (k + 1))⁻¹)) • v := by
          rw [div_eq_mul_inv]
          ring_nf
    _ = (t k - 1) • v := by
          rw [mul_inv_cancel₀ ht_ne, mul_one]

/-- Helper for Proposition 2.10: the transformed auxiliary point satisfies the exact textbook
gradient-step update `z_{k+1} = z_k - (t_k / L) ∇ f(y_k)`. -/
private lemma textbook_aux_point_step
    (k : ℕ) :
    textbookAuxPoint scheme (k + 1) =
      textbookAuxPoint scheme k - ((t k) / (L : ℝ)) • ∇ f (scheme.y k) := by
  -- Rewrite `z_{k+1}` with the textbook `y_{k+1}` formula, cancel the scalar coefficient,
  -- and then substitute the exact gradient step for `x_{k+1}`.
  have hx_succ :
      ((scheme.x (k + 1) : E)) = scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k) := by
    simpa using scheme.x_succ k
  calc
    textbookAuxPoint scheme (k + 1)
        = (t (k + 1)) •
            (scheme.x (k + 1) +
              ((t k - 1) / t (k + 1)) • (scheme.x (k + 1) - scheme.x k)) -
            (t (k + 1) - 1) • scheme.x (k + 1) := by
              rw [textbookAuxPoint, y_succ_eq_textbook scheme k]
    _ = (t (k + 1)) • scheme.x (k + 1) +
          (t k - 1) • (scheme.x (k + 1) - scheme.x k) -
          (t (k + 1) - 1) • scheme.x (k + 1) := by
            rw [smul_add, scaled_momentum_coefficient_smul scheme k]
    _ = (t k) • scheme.x (k + 1) - (t k - 1) • scheme.x k := by
          rw [smul_sub]
          module
    _ = (t k) • (scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k)) -
          (t k - 1) • scheme.x k := by
            change
              (t k) • ((scheme.x (k + 1) : E)) - (t k - 1) • (scheme.x k : E) =
                (t k) • (scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k)) -
                  (t k - 1) • (scheme.x k : E)
            rw [hx_succ]
    _ = textbookAuxPoint scheme k - ((t k) / (L : ℝ)) • ∇ f (scheme.y k) := by
          rw [textbookAuxPoint, smul_sub, smul_smul]
          module

/-- Helper for Proposition 2.10: the convexity inequalities at `y_k` combine into the weighted
textbook bridge
`t_k (f(y_k) - f*) - (t_k - 1) (f(x_k) - f*) ≤ ⟪∇ f(y_k), z_k - x*⟫`. -/
private lemma textbook_weighted_convexity_bridge
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (k : ℕ) :
    (t k) * (f (scheme.y k) - f xStar) -
        (t k - 1) * (f (scheme.x k) - f xStar) ≤
      inner ℝ (∇ f (scheme.y k)) (textbookAuxPoint scheme k - xStar) := by
  let gk : E := ∇ f (scheme.y k)
  have lower_tangent_plane_gap (y : E) :
      f (scheme.y k) - f y ≤ inner ℝ gk (scheme.y k - y) := by
    have hsupport :
        f y ≥ f (scheme.y k) + inner ℝ gk (y - scheme.y k) := by
      simpa [gk, gradientWithin, gradient, fderivWithin_univ] using
        hconvex.lower_tangent_plane
          (scheme.y k) (by simp)
          ((hcontDiff.differentiable_one (scheme.y k)).differentiableWithinAt)
          y (by simp)
    have hinner :
        inner ℝ gk (y - scheme.y k) = -inner ℝ gk (scheme.y k - y) := by
      calc
        inner ℝ gk (y - scheme.y k) = inner ℝ gk (-(scheme.y k - y)) := by
          congr 2
          abel
        _ = -inner ℝ gk (scheme.y k - y) := by
          rw [inner_neg_right]
    rw [hinner] at hsupport
    linarith
  have hy_star :
      f (scheme.y k) - f xStar ≤ inner ℝ gk (scheme.y k - xStar) :=
    lower_tangent_plane_gap xStar
  have hy_x :
      f (scheme.y k) - f (scheme.x k) ≤ inner ℝ gk (scheme.y k - scheme.x k) :=
    lower_tangent_plane_gap (scheme.x k)
  have hweight : 0 ≤ t k - 1 := by
    have ht_lower := nat_add_two_div_two_le_t scheme k
    have hk_nonneg : (0 : ℝ) ≤ k := by
      exact_mod_cast Nat.zero_le k
    have hhalf_decomp : (((k + 2 : ℕ) : ℝ) / 2) = (k : ℝ) / 2 + 1 := by
      calc
        (((k + 2 : ℕ) : ℝ) / 2) = ((k : ℝ) + 2) / 2 := by
          norm_num [Nat.cast_add]
        _ = (k : ℝ) / 2 + 1 := by
          ring
    have hone : (1 : ℝ) ≤ (((k + 2 : ℕ) : ℝ) / 2) := by
      rw [hhalf_decomp]
      nlinarith
    nlinarith
  have hy_x_scaled :
      (t k - 1) * (f (scheme.y k) - f (scheme.x k)) ≤
        inner ℝ gk ((t k - 1) • (scheme.y k - scheme.x k)) := by
    -- Scale the second convexity bound by the nonnegative weight `t_k - 1`.
    have hscaled := mul_le_mul_of_nonneg_left hy_x hweight
    simpa [gk, real_inner_smul_right] using hscaled
  have hsum :
      (f (scheme.y k) - f xStar) + (t k - 1) * (f (scheme.y k) - f (scheme.x k)) ≤
        inner ℝ gk
          ((scheme.y k - xStar) + (t k - 1) • (scheme.y k - scheme.x k)) := by
    -- Add the two tangent-plane inequalities and package the right-hand side as one inner product.
    have hadd := add_le_add hy_star hy_x_scaled
    simpa [gk, inner_add_right] using hadd
  have hlhs :
      (t k) * (f (scheme.y k) - f xStar) -
          (t k - 1) * (f (scheme.x k) - f xStar) =
        (f (scheme.y k) - f xStar) +
          (t k - 1) * (f (scheme.y k) - f (scheme.x k)) := by
    ring
  have haux :
      textbookAuxPoint scheme k - xStar =
        (scheme.y k - xStar) + (t k - 1) • (scheme.y k - scheme.x k) :=
    textbook_aux_point_affine_identity scheme k
  rw [hlhs]
  simpa [haux] using hsum

/-- Helper for Proposition 2.10: the transformed textbook Lyapunov quantity decreases at each
step. -/
private lemma textbook_potential_drop
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (k : ℕ) :
    (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) +
        ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      ((t k) ^ (2 : ℕ) - t k) * (f (scheme.x k) - f xStar) +
        ((L : ℝ) / 2) * ‖textbookAuxPoint scheme k - xStar‖ ^ (2 : ℕ) := by
  let gk : E := ∇ f (scheme.y k)
  have hdescent :
      f (scheme.x (k + 1)) ≤
        f (scheme.y k) - (1 / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Use the direct smooth descent estimate at the extrapolated point `y_k`.
    have hcoeff :
        (1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2) =
          1 / (2 * (L : ℝ)) := by
      field_simp [scheme.L_pos.ne']
      ring
    have hx_succ :
        ((scheme.x (k + 1) : E)) = scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k) := by
      simpa using scheme.x_succ k
    have hstep :
        f (scheme.y k - (1 / (L : ℝ)) • ∇ f (scheme.y k)) ≤
          f (scheme.y k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := by
      simpa [gk] using
        gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
          hcontDiff hgrad_lipschitz (scheme.y k) (1 / (L : ℝ))
    have hstep' :
        f (scheme.x (k + 1)) ≤
          f (scheme.y k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := by
      simpa [hx_succ] using hstep
    calc
      f (scheme.x (k + 1)) ≤
          f (scheme.y k) -
            ((1 / (L : ℝ)) * (1 - ((L : ℝ) * (1 / (L : ℝ))) / 2)) * ‖gk‖ ^ (2 : ℕ) := hstep'
      _ = f (scheme.y k) - (1 / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
          rw [hcoeff]
  have hdescent_scaled :
      (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) ≤
        (t k) ^ (2 : ℕ) * (f (scheme.y k) - f xStar) -
          ((t k) ^ (2 : ℕ) / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Multiply the one-step descent estimate by `t_k^2`.
    have ht_sq_nonneg : 0 ≤ (t k) ^ (2 : ℕ) := by positivity
    have hscaled := mul_le_mul_of_nonneg_left hdescent ht_sq_nonneg
    ring_nf at hscaled ⊢
    linarith
  have ht_nonneg : 0 ≤ t k := le_of_lt (one_div_pos.mpr (alpha_pos scheme k))
  have hbridge_scaled :
      (t k) ^ (2 : ℕ) * (f (scheme.y k) - f xStar) -
          (t k) * (t k - 1) * (f (scheme.x k) - f xStar) ≤
        (t k) * inner ℝ gk (textbookAuxPoint scheme k - xStar) := by
    -- Multiply the weighted convexity bridge by the nonnegative factor `t_k`.
    have hbridge :
        (t k) * (f (scheme.y k) - f xStar) -
            (t k - 1) * (f (scheme.x k) - f xStar) ≤
          inner ℝ (∇ f (scheme.y k)) (textbookAuxPoint scheme k - xStar) :=
      textbook_weighted_convexity_bridge scheme hconvex hcontDiff k
    have hscaled :=
      mul_le_mul_of_nonneg_left hbridge ht_nonneg
    nlinarith
  have hquad :
      ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) =
        ((L : ℝ) / 2) * ‖textbookAuxPoint scheme k - xStar‖ ^ (2 : ℕ) -
          (t k) * inner ℝ gk (textbookAuxPoint scheme k - xStar) +
          ((t k) ^ (2 : ℕ) / (2 * (L : ℝ))) * ‖gk‖ ^ (2 : ℕ) := by
    -- Expand the next norm square after rewriting `z_{k+1}` as a single gradient step from `z_k`.
    have hz :
        textbookAuxPoint scheme (k + 1) - xStar =
          (textbookAuxPoint scheme k - xStar) - ((t k) / (L : ℝ)) • gk := by
      calc
        textbookAuxPoint scheme (k + 1) - xStar
            = (textbookAuxPoint scheme k - ((t k) / (L : ℝ)) • gk) - xStar := by
                rw [textbook_aux_point_step scheme k]
        _ = (textbookAuxPoint scheme k - xStar) - ((t k) / (L : ℝ)) • gk := by
              abel
    have hL_ne : (L : ℝ) ≠ 0 := scheme.L_pos.ne'
    rw [hz, norm_sub_sq_real, norm_smul, real_inner_smul_right, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [real_inner_comm (textbookAuxPoint scheme k - xStar) gk]
    field_simp [hL_ne]
  -- Add the scaled descent inequality to the expanded norm-square identity and cancel the bridge.
  nlinarith [hdescent_scaled, hbridge_scaled, hquad]

/-- Helper for Proposition 2.10: the transformed textbook Lyapunov quantity is bounded by the
initial quadratic energy. -/
private lemma textbook_potential_le_initial
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f)) :
    ∀ k : ℕ,
      (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) +
          ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) ≤
        ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
  intro k
  induction k with
  | zero =>
      -- Start the Lyapunov estimate from the step-`0` drop and the explicit identities `t₀ = 1`,
      -- `z₀ = x₀`.
      have hdrop :
          (t 0) ^ (2 : ℕ) * (f (scheme.x (0 + 1)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (0 + 1) - xStar‖ ^ (2 : ℕ) ≤
            ((t 0) ^ (2 : ℕ) - t 0) * (f (scheme.x 0) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme 0 - xStar‖ ^ (2 : ℕ) :=
        textbook_potential_drop scheme hconvex hcontDiff hgrad_lipschitz 0
      simpa [scheme.alpha_zero, textbook_aux_point_zero scheme] using hdrop
  | succ k hk =>
      -- Use the one-step drop at time `k + 1` and identify the predecessor coefficient
      -- `t_{k+1}^2 - t_{k+1}` with `t_k^2`.
      have hdrop :
          (t (k + 1)) ^ (2 : ℕ) * (f (scheme.x (k + 2)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 2) - xStar‖ ^ (2 : ℕ) ≤
            ((t (k + 1)) ^ (2 : ℕ) - t (k + 1)) * (f (scheme.x (k + 1)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) :=
        textbook_potential_drop scheme hconvex hcontDiff hgrad_lipschitz (k + 1)
      rw [t_succ_sq_sub_t_succ_eq_t_sq scheme k] at hdrop
      exact hdrop.trans hk

/-- Proposition 2.10: for a smooth convex objective, every type-II recurrence specialized to
`q_f = 0`, `α₀ = 1`, and the exact gradient step
`x_{k+1} = y_k - (1 / L) ∇ f(y_k)` satisfies the textbook quadratic function-value bound.

This is the owner-abstraction form of the proposition: the textbook sequence `t_k` is the derived
reciprocal `t_k = 1 / α_k`, and the iterate sequence is the owner field `scheme.x`, equivalently
the coercion `scheme : ℕ → E`. -/
-- Proof sketch: view the `q_f = 0` type-II recurrence as the smooth-convex optimal-method
-- specialization with `γ₀ = 3L` encoded through the owner scalar sequence `α_k`. Apply the
-- chapter's estimating-sequence quadratic-rate argument to the owner trajectory, then rewrite the
-- displayed textbook constants using `scheme.x_zero`, equivalently `scheme.x 0 = x₀`.
theorem objective_gap_le_quadratic_rate
    (hconvex : ConvexOn ℝ Set.univ f)
    (hcontDiff : ContDiff ℝ 1 f)
    (hgrad_lipschitz : LipschitzWith L (∇ f))
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (scheme.x k) - f xStar ≤
      (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) := by
  -- Route correction: the old placeholder cited the later optimal-method theorem. Here we keep
  -- the dependency-closed route inside Proposition 2.10 itself via the textbook `t_k` scalars.
  have hbase :
      f (scheme.x 0) - f xStar ≤
        (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
          (3 * (0 + 1 : ℝ) ^ (2 : ℕ)) := by
    have hinit :=
      initial_objective_gap_le_half_lipschitz_sqdist scheme hcontDiff hgrad_lipschitz hxStar
    have hscaled : ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) ≤
        (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
          (3 * (0 + 1 : ℝ) ^ (2 : ℕ)) := by
      nlinarith [L.2, sq_nonneg ‖scheme.x 0 - xStar‖]
    exact hinit.trans hscaled
  cases k with
  | zero =>
      simpa using hbase
  | succ k =>
      -- Use the Lyapunov bound at index `k`, discard the nonnegative quadratic term,
      -- and convert the remaining `t_k` denominator using the elementary scalar lower bound.
      have hpot :
          (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) +
              ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) :=
        textbook_potential_le_initial scheme hconvex hcontDiff hgrad_lipschitz k
      have hquad_nonneg :
          0 ≤ ((L : ℝ) / 2) * ‖textbookAuxPoint scheme (k + 1) - xStar‖ ^ (2 : ℕ) := by
        positivity
      have hgap :
          (t k) ^ (2 : ℕ) * (f (scheme.x (k + 1)) - f xStar) ≤
            ((L : ℝ) / 2) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
        linarith
      have hgap_nonneg : 0 ≤ f (scheme.x (k + 1)) - f xStar := by
        exact sub_nonneg.mpr ((isMinOn_iff.mp hxStar) (scheme.x (k + 1)) (by simp))
      have ht_lower := nat_add_two_div_two_le_t scheme k
      have hrate_mul :
          (f (scheme.x (k + 1)) - f xStar) * ((k + 2 : ℕ) : ℝ) ^ (2 : ℕ) ≤
            2 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
        have htk :
            (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) ≤ 4 * (t k) ^ (2 : ℕ) := by
          have hk_half_nonneg : 0 ≤ (((k + 2 : ℕ) : ℝ) / 2) := by
            positivity
          have ht_nonneg : 0 ≤ t k := by
            exact le_of_lt (one_div_pos.mpr (alpha_pos scheme k))
          nlinarith
        nlinarith [hgap, htk, hgap_nonneg]
      have hden_pos : 0 < (3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)) := by
        positivity
      have hrate_target_mul :
          (f (scheme.x (k + 1)) - f xStar) * ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))) ≤
            8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ) := by
        nlinarith [hrate_mul]
      have hfinal :
          f (scheme.x (k + 1)) - f xStar ≤
            (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
              ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))) := by
        refine (le_div_iff₀ hden_pos).2 ?_
        nlinarith [hrate_target_mul]
      have hden_eq :
          ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ))) =
            3 * ((((k + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
        calc
          ((3 : ℝ) * (((k + 2 : ℕ) : ℝ) ^ (2 : ℕ)))
              = (3 : ℝ) * ((((k : ℝ) + 1) + 1) ^ (2 : ℕ)) := by
                  norm_num [Nat.cast_add, add_assoc]
          _ = 3 * ((((k + 1 : ℕ) : ℝ) + 1) ^ (2 : ℕ)) := by
                norm_num [Nat.cast_add, add_assoc]
      rw [hden_eq] at hfinal
      exact hfinal

/-- Finite-dimensional Chapter 2 bridge form of Proposition 2.10 using the source notation
`f ∈ 𝓕[L, normSeminorm ℝ E]¹¹`. -/
theorem objective_gap_le_quadratic_rate_of_mem_F11
    [FiniteDimensional ℝ E]
    (hf : f ∈ 𝓕[L, p]¹¹)
    (hxStar : IsMinOn f Set.univ xStar)
    (k : ℕ) :
    f (scheme.x k) - f xStar ≤
      (8 * (L : ℝ) * ‖scheme.x 0 - xStar‖ ^ (2 : ℕ)) /
        (3 * (k + 1 : ℝ) ^ (2 : ℕ)) :=
  objective_gap_le_quadratic_rate scheme
    hf.convexOn hf.contDiff hf.gradient_lipschitz hxStar k

end

end ConstantStepSchemeIIRecurrence

end
