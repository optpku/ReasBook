/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Lemma_2_13
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Theorem_2_13

open scoped Gradient ProjectedGradient StrongConvexSmooth
open scoped ConstrainedArgmin

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- The primary domain here is projected-gradient trajectories on a closed convex feasible set in a
real Hilbert space.

Owner abstractions sampled for this refinement:
* `gradientMapping` from `Definition_2_35_1`, the chapter's source-facing projected-gradient point;
* `euclideanProjection_isProjectionPointOn` from `Theorem_2_33`, the owner projection theorem
  reused after unfolding `gradientMapping`;
* `IsProjectionPointOn Q y p` from `Definition_2_33`, the core nearest-point predicate;
* `f ∈ 𝓢[μ, L]¹¹` and `mem_S11_iff` from `Definition_2_17`, the source-facing objective class
  and its bridge to the core owner predicate `IsStrongConvexSmoothObjective μ L f`.

Best owner abstraction:
* the one-step map `x ↦ gradientMapping Q ⟨x0, hx0_mem⟩ hQ_closed hQ_convex f x γ`.

Primitive data here are the closed/convex feasible-set geometry, the source-facing objective
hypothesis `f ∈ 𝓢[μ, L]¹¹`, the feasible initial point `x0 ∈ Q`, the constrained minimizer
certificate `xStar ∈ argmin[Q] f`, and the iterate sequence `x` satisfying the explicit
projected-gradient recursion. The core owner predicate `IsStrongConvexSmoothObjective μ L f`, the
projection-point view, and feasibility of later iterates are derived API. This keeps the public
theorem surface on the chapter notation and the source-facing recursion rather than packaging the
trajectory as a separate wrapper predicate. -/

namespace ProjectedGradientSequence

section

variable {Q : Set E} {hQ_closed : IsClosed Q} {hQ_convex : Convex ℝ Q}
variable {f : E → ℝ} {γ : NNRealˣ} {x0 : E} {x : ℕ → E}

/-- Each projected-gradient step is a Euclidean projection point of the explicit gradient step
onto `Q`. -/
theorem step_isProjectionPointOn
    (hx0_mem : x0 ∈ Q)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k)) :
    IsProjectionPointOn Q (gradientStep f (x k) γ) (x (k + 1)) := by
  simpa [hx_step] using
    gradientMapping_isProjectionPointOn Q ⟨x0, hx0_mem⟩ hQ_closed hQ_convex f γ (x k)

/-- Every projected-gradient step lands back in the feasible set. -/
theorem mem_succ
    (hx0_mem : x0 ∈ Q)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k)) :
    x (k + 1) ∈ Q :=
  (step_isProjectionPointOn hx0_mem k hx_step).1

/-- The projected-gradient recursion stays in the feasible set. -/
theorem mem
    (hx0_mem : x0 ∈ Q)
    (hx_zero : x 0 = x0)
    (hx_succ : ∀ k : ℕ,
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (k : ℕ) :
    x k ∈ Q := by
  induction k with
  | zero =>
      simpa [hx_zero] using hx0_mem
  | succ k hk =>
      exact mem_succ hx0_mem k (hx_succ k)

end

section

variable {Q : Set E} {hQ_closed : IsClosed Q} {hQ_convex : Convex ℝ Q}
variable {μ L : ℝ} {γ : NNRealˣ} {f : E → ℝ}
variable {x0 xStar : E} {x : ℕ → E}

/-- Helper for Theorem 2.38: a constrained minimizer is a projection point of its own explicit
gradient step on the feasible set. -/
theorem isProjectionPointOn_gradientStep_of_constrainedArgmin
    (hQ_convex : Convex ℝ Q)
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hxStar : xStar ∈ argmin[Q] f) :
    IsProjectionPointOn Q (gradientStep f xStar γ) xStar := by
  rcases mem_constrainedArgmin_iff.mp hxStar with ⟨hxStar_mem, hxStar_min⟩
  have hgrad :
      HasGradientAt f (∇ f xStar) xStar :=
    (hf.contDiff.differentiable_one xStar).hasGradientAt
  -- Turn first-order optimality at the constrained minimizer into the projection inequality.
  have hvariational :
      ∀ x ∈ Q, inner ℝ (gradientStep f xStar γ - xStar) (x - xStar) ≤ 0 := by
    intro x hx
    have hγ_pos : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hdir : x - xStar ∈ posTangentConeAt Q xStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset hxStar_mem hx)
    have hfirstOrder :=
      hxStar_min.localize.hasFDerivWithinAt_nonneg
        hgrad.hasFDerivAt.hasFDerivWithinAt hdir
    have hinner_nonneg : 0 ≤ inner ℝ (∇ f xStar) (x - xStar) := by
      simpa [hgrad.hasFDerivAt.fderiv, innerSL_apply_apply] using hfirstOrder
    have hscaled : 0 ≤ (γ : ℝ)⁻¹ * inner ℝ (∇ f xStar) (x - xStar) :=
      mul_nonneg (inv_nonneg.mpr hγ_pos.le) hinner_nonneg
    simpa [gradientStep, sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      (neg_nonpos.mpr hscaled)
  -- Package that variational inequality into the owner projection-point predicate.
  have hmin :
      ‖gradientStep f xStar γ - xStar‖ =
        ⨅ w : Q, ‖gradientStep f xStar γ - w‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hxStar_mem).2 hvariational
  exact IsProjectionPointOn.of_norm_eq_iInf hxStar_mem hmin

/-- Helper for Theorem 2.38: two projection points onto the same convex feasible set are no
farther apart than their base points. -/
theorem projectionPoint_dist_le_dist
    (hQ_convex : Convex ℝ Q)
    {x₁ p₁ x₂ p₂ : E}
    (hp₁ : IsProjectionPointOn Q x₁ p₁)
    (hp₂ : IsProjectionPointOn Q x₂ p₂) :
    dist p₁ p₂ ≤ dist x₁ x₂ := by
  have h₁ : 0 ≤ inner ℝ (p₁ - x₁) (p₂ - p₁) :=
    hp₁.inner_sub_nonneg hQ_convex hp₂.1
  have h₂ : 0 ≤ inner ℝ (p₂ - x₂) (p₁ - p₂) :=
    hp₂.inner_sub_nonneg hQ_convex hp₁.1
  have hpair : p₂ - p₁ = -(p₁ - p₂) := by
    abel
  have h₁' : inner ℝ (p₁ - x₁) (p₁ - p₂) ≤ 0 := by
    rw [hpair, inner_neg_right] at h₁
    linarith
  -- Add the two projection inequalities and isolate the displacement `p₁ - p₂`.
  have haux : 0 ≤ inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₂ - x₂) (p₁ - p₂) - inner ℝ (p₁ - x₁) (p₁ - p₂) := by
      simp [sub_eq_add_neg, inner_add_left, add_comm, add_left_comm, add_assoc]
    rw [hrewrite]
    linarith
  have hmain : ‖p₁ - p₂‖ ^ (2 : ℕ) ≤ inner ℝ (p₁ - p₂) (x₁ - x₂) := by
    have hrewrite :
        inner ℝ ((x₁ - x₂) - (p₁ - p₂)) (p₁ - p₂) =
          inner ℝ (p₁ - p₂) (x₁ - x₂) - ‖p₁ - p₂‖ ^ (2 : ℕ) := by
      rw [inner_sub_left, real_inner_comm (x₁ - x₂), real_inner_self_eq_norm_sq]
    rw [hrewrite] at haux
    linarith
  have hcs : inner ℝ (p₁ - p₂) (x₁ - x₂) ≤ ‖p₁ - p₂‖ * ‖x₁ - x₂‖ := by
    simpa [Real.norm_eq_abs] using real_inner_le_norm (p₁ - p₂) (x₁ - x₂)
  have hnorm : ‖p₁ - p₂‖ ≤ ‖x₁ - x₂‖ := by
    nlinarith [hmain, hcs, norm_nonneg (p₁ - p₂), norm_nonneg (x₁ - x₂)]
  simpa [dist_eq_norm] using hnorm

/-- Helper for Theorem 2.38: the next projected-gradient iterate is no farther from the minimizer
than the corresponding pair of explicit gradient steps. -/
theorem step_dist_le_gradientStep_dist
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k)) :
    ‖x (k + 1) - xStar‖ ≤ ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ := by
  -- Compare the two projection points attached to the iterate and to the minimizer.
  have hx_proj :
      IsProjectionPointOn Q (gradientStep f (x k) γ) (x (k + 1)) :=
    step_isProjectionPointOn hx0_mem k hx_step
  have hxStar_proj :
      IsProjectionPointOn Q (gradientStep f xStar γ) xStar :=
    isProjectionPointOn_gradientStep_of_constrainedArgmin
      hQ_convex hf hxStar
  -- Projection nonexpansiveness now gives the distance comparison.
  simpa [dist_eq_norm] using
    projectionPoint_dist_le_dist hQ_convex hx_proj hxStar_proj

/-- Helper for Theorem 2.38: strong convexity forces the gradient difference to dominate the point
difference in norm. -/
theorem mu_mul_norm_sub_le_norm_gradient_sub
    (hf : IsStrongConvexSmoothObjective μ L f)
    (x y : E) :
    μ * ‖x - y‖ ≤ ‖∇ f x - ∇ f y‖ := by
  -- Combine strong monotonicity with Cauchy--Schwarz and cancel one nonnegative norm factor.
  have hmono := hf.gradient_strong_mono x y
  have hcs :
      inner ℝ (∇ f x - ∇ f y) (x - y) ≤
        ‖∇ f x - ∇ f y‖ * ‖x - y‖ := by
    exact real_inner_le_norm _ _
  nlinarith [hmono, hcs, hf.mu_pos, norm_nonneg (x - y), norm_nonneg (∇ f x - ∇ f y)]

/-- Helper for Theorem 2.38: the squared distance to the constrained minimizer contracts in one
projected-gradient step by the factor `(1 - μ / γ)^2`. -/
theorem dist_succ_sq_le_contraction_sq
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (hγ : (L + μ) / 2 ≤ (γ : ℝ)) :
    ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
      (1 - μ / (γ : ℝ)) ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) := by
  by_cases hE : Subsingleton E
  · have hxsucc : x (k + 1) = xStar := hE.elim _ _
    have hxk : x k = xStar := hE.elim _ _
    simp [hxsucc, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hμL : μ ≤ L := hf.mu_le_L
    have hγ_pos : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hγ_inv_nonneg : 0 ≤ (γ : ℝ)⁻¹ := inv_nonneg.mpr hγ_pos.le
    have hden : 0 < μ + L := by
      nlinarith [hf.mu_pos, hμL]
    have hstep :=
      step_dist_le_gradientStep_dist hf hx0_mem hxStar k hx_step
    have hstep_sq :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hstep
    have hstep_diff :
        gradientStep f (x k) γ - gradientStep f xStar γ =
          (x k - xStar) - ((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar) := by
      rw [gradientStep, gradientStep, smul_sub]
      abel_nf
    -- Expand the explicit gradient-step difference into a point part and a gradient part.
    have hexpand :
        ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ) =
          ‖x k - xStar‖ ^ (2 : ℕ) -
            2 * (γ : ℝ)⁻¹ *
              inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) +
            ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      calc
        ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ)
            = ‖(x k - xStar) - ((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar)‖ ^ (2 : ℕ) := by
                rw [hstep_diff]
        _ = ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * inner ℝ (x k - xStar) (((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar)) +
              ‖((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar)‖ ^ (2 : ℕ) := by
              simpa using
                norm_sub_sq_real
                  (x k - xStar)
                  (((γ : ℝ)⁻¹) • (∇ f (x k) - ∇ f xStar))
        _ = ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ *
                inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
              rw [real_inner_smul_right, real_inner_comm]
              simp [norm_smul, Real.norm_of_nonneg hγ_inv_nonneg, sq]
              ring
    have hpair := hf.pairing_lower_bound (x k) xStar
    have hμ_grad :=
      mu_mul_norm_sub_le_norm_gradient_sub hf (x k) xStar
    have hμ_grad_sq :
        μ ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) ≤
          ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      have hsq :
          (μ * ‖x k - xStar‖) ^ (2 : ℕ) ≤
            ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
        exact
          (sq_le_sq₀
            (mul_nonneg hf.mu_pos.le (norm_nonneg _))
            (norm_nonneg _)).2 hμ_grad
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    have hγ' : (μ + L) / 2 ≤ (γ : ℝ) := by
      simpa [add_comm] using hγ
    have hhalf_pos : 0 < (μ + L) / 2 := by
      positivity
    have hinv_le :
        (γ : ℝ)⁻¹ ≤ 2 / (μ + L) := by
      simpa [one_div, div_eq_mul_inv, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using
        (one_div_le_one_div_of_le hhalf_pos hγ')
    have hcoeff_nonpos :
        (γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L)) ≤ 0 := by
      exact mul_nonpos_of_nonneg_of_nonpos hγ_inv_nonneg (sub_nonpos.mpr hinv_le)
    -- The secant inequality controls the mixed term, and the remaining gradient term is
    -- nonpositive after substituting the lower bound `‖∇ f x - ∇ f y‖ ≥ μ ‖x - y‖`.
    have hpair' :
        2 * (γ : ℝ)⁻¹ *
            ((μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) +
              (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ)) ≤
          2 * (γ : ℝ)⁻¹ *
            inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) := by
      exact mul_le_mul_of_nonneg_left hpair (by positivity)
    have hstep₁ :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ‖x k - xStar‖ ^ (2 : ℕ) -
            2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) -
            2 * (γ : ℝ)⁻¹ * (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) +
            ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      calc
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ‖gradientStep f (x k) γ - gradientStep f xStar γ‖ ^ (2 : ℕ) :=
          hstep_sq
        _ = ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ *
                inner ℝ (∇ f (x k) - ∇ f xStar) (x k - xStar) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := hexpand
        _ ≤ ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
              nlinarith [hpair']
    have hstep₂ :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) * ‖x k - xStar‖ ^ (2 : ℕ) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
              ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
      calc
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
            ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L)) * ‖x k - xStar‖ ^ (2 : ℕ) -
              2 * (γ : ℝ)⁻¹ * (1 / (μ + L)) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) +
              ((γ : ℝ)⁻¹) ^ (2 : ℕ) * ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) :=
          hstep₁
        _ = (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) * ‖x k - xStar‖ ^ (2 : ℕ) +
              ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
                ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := by
              ring
    have hgrad_term :
        ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
            ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) ≤
          ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
            (μ ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ)) := by
      exact mul_le_mul_of_nonpos_left hμ_grad_sq hcoeff_nonpos
    have hcoeff_eq :
        (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) * μ ^ (2 : ℕ) =
          (1 - μ / (γ : ℝ)) ^ (2 : ℕ) := by
      have hγ_ne : (γ : ℝ) ≠ 0 := ne_of_gt hγ_pos
      have hden_ne : μ + L ≠ 0 := ne_of_gt hden
      field_simp [pow_two, hγ_ne, hden_ne]
      ring
    calc
      ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          (1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) * ‖x k - xStar‖ ^ (2 : ℕ) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) *
              ‖∇ f (x k) - ∇ f xStar‖ ^ (2 : ℕ) := hstep₂
      _ ≤ ((1 - 2 * (γ : ℝ)⁻¹ * (μ * L / (μ + L))) +
            ((γ : ℝ)⁻¹ * ((γ : ℝ)⁻¹ - 2 / (μ + L))) * μ ^ (2 : ℕ)) *
            ‖x k - xStar‖ ^ (2 : ℕ) := by
            nlinarith [hgrad_term]
      _ = (1 - μ / (γ : ℝ)) ^ (2 : ℕ) * ‖x k - xStar‖ ^ (2 : ℕ) := by
            rw [hcoeff_eq]

/-- Under the hypotheses of Theorem 2.38, each projected-gradient step contracts the distance to
the constrained minimizer by the factor `1 - μ / γ`. -/
-- Proof sketch: Theorem 2.35 identifies `xStar` with the projection of its explicit gradient
-- step, and `euclideanProjection_nonexpansive` compares that projection with the one defining
-- `x (k + 1)`. Expanding the resulting squared norm and applying
-- `IsStrongConvexSmoothObjective.pairing_lower_bound` yields the one-step contraction once
-- `γ ≥ (L + μ) / 2` makes the gradient term nonpositive.
theorem dist_succ_le_contraction
    (hf : IsStrongConvexSmoothObjective μ L f)
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (k : ℕ)
    (hx_step :
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (hγ : (L + μ) / 2 ≤ (γ : ℝ)) :
    ‖x (k + 1) - xStar‖ ≤ (1 - μ / (γ : ℝ)) * ‖x k - xStar‖ := by
  by_cases hE : Subsingleton E
  · have hxsucc : x (k + 1) = xStar := hE.elim _ _
    have hxk : x k = xStar := hE.elim _ _
    simp [hxsucc, hxk]
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    have hμL : μ ≤ L := hf.mu_le_L
    have hμγ : μ ≤ (γ : ℝ) := by
      nlinarith
    have hγ_pos : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hρ_nonneg : 0 ≤ 1 - μ / (γ : ℝ) := by
      have hdiv : μ / (γ : ℝ) ≤ 1 := by
        exact (div_le_one hγ_pos).2 hμγ
      nlinarith
    have hsq :=
      dist_succ_sq_le_contraction_sq hf hx0_mem hxStar k hx_step hγ
    have hsq' :
        ‖x (k + 1) - xStar‖ ^ (2 : ℕ) ≤
          ((1 - μ / (γ : ℝ)) * ‖x k - xStar‖) ^ (2 : ℕ) := by
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hsq
    -- Extract the distance estimate from the squared contraction.
    exact
      (sq_le_sq₀
        (norm_nonneg _)
        (mul_nonneg hρ_nonneg (norm_nonneg _))).1 hsq'

end

end ProjectedGradientSequence

/-- Theorem 2.38: if `Q` is closed and convex in a real Hilbert space `E`, `f` belongs to
`𝓢^{1,1}_{μ,L}(E)`, and `xStar ∈ Q` minimizes `f` on `Q`, then every projected-gradient
trajectory with inverse-stepsize parameter `γ ≥ (L + μ) / 2` contracts linearly toward `xStar`, with
`‖x_k - xStar‖ ≤ (1 - μ / γ)^k ‖x0 - xStar‖` for all `k ≥ 0`. Uniqueness of the constrained
minimizer is derived from strong convexity and is not stored as a separate hypothesis; likewise, in
the nontrivial real-Hilbert-space cases the owner hypothesis already forces `μ ≤ L`, while the
subsingleton case is tautological. The textbook `ℝⁿ` theorem is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: because `xStar ∈ Q` minimizes `f` on `Q`, Theorem 2.35 makes `xStar` a fixed
-- point of the projection step. Then use nonexpansiveness of Euclidean projection to compare
-- `x (k + 1)` with `xStar`, expand the squared norm, and apply the standard interpolation
-- inequality for an objective in `𝓢^{1,1}_{μ,L}(E)`. The condition `γ ≥ (L + μ) / 2` makes the
-- gradient term contribute with the correct sign, yielding the one-step contraction
-- `‖x (k + 1) - xStar‖ ≤ (1 - μ / γ) ‖x k - xStar‖`; iterate this inequality over `k`.
theorem projectedGradientSequence_dist_le_geometric
    (Q : Set E) (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {μ L : ℝ} {γ : NNRealˣ} {f : E → ℝ}
    (hf : f ∈ 𝓢[μ, L]¹¹)
    {x0 xStar : E}
    (hx0_mem : x0 ∈ Q)
    (hxStar : xStar ∈ argmin[Q] f)
    (x : ℕ → E)
    (hx_zero : x 0 = x0)
    (hx_succ : ∀ k : ℕ,
      x (k + 1) = x_Q[Q;⟨x0, hx0_mem⟩;hQ_closed;hQ_convex|f;γ](x k))
    (hγ : (L + μ) / 2 ≤ (γ : ℝ))
    (k : ℕ) :
    ‖x k - xStar‖ ≤ (1 - μ / (γ : ℝ)) ^ k * ‖x0 - xStar‖ := by
  have hf' : IsStrongConvexSmoothObjective μ L f := mem_S11_iff.mp hf
  by_cases hE : Subsingleton E
  · have hxk : x k = xStar := hE.elim _ _
    have hx0' : x0 = xStar := hE.elim _ _
    simp [hxk, hx0']
  · letI : Nontrivial E := not_subsingleton_iff_nontrivial.mp hE
    let ρ : ℝ := 1 - μ / (γ : ℝ)
    have hμL : μ ≤ L := hf'.mu_le_L
    have hμγ : μ ≤ (γ : ℝ) := by
      nlinarith
    have hρ_nonneg : 0 ≤ ρ := by
      have hγ : 0 < (γ : ℝ) := by
        exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
      have hdiv : μ / (γ : ℝ) ≤ 1 := by
        exact (div_le_one hγ).2 hμγ
      nlinarith
    induction k with
    | zero =>
        simp [hx_zero]
    | succ k hk =>
        calc
          ‖x (k + 1) - xStar‖ ≤ ρ * ‖x k - xStar‖ := by
            simpa [ρ] using
              ProjectedGradientSequence.dist_succ_le_contraction
                hf' hx0_mem hxStar k (hx_succ k) hγ
          _ ≤ ρ * (ρ ^ k * ‖x0 - xStar‖) := by
            exact mul_le_mul_of_nonneg_left hk hρ_nonneg
          _ = ρ ^ (k + 1) * ‖x0 - xStar‖ := by
            simp [pow_succ, ρ, mul_left_comm, mul_comm]
