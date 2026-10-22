/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {L : NNReal} {f : E → ℝ}
variable (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))

include hf hgrad

/- Primary domain: one-step sufficient-decrease estimates for gradient descent on real Hilbert
spaces.

Relevant owner-style declarations sampled before refining:
* `firstOrderTaylorModelAt` in `FirstOrderTaylorModel.lean`, the chapter owner of the affine
  first-order model;
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Lemma_1_5_10.lean`, the canonical
  quadratic upper model under a Lipschitz gradient bound;
* `gradientMethod_value_drop_ge_sqnorm_of_constant_stepsize` in `Proposition_1_6_7.lean`, the
  direct downstream iterate theorem obtained by applying the present pointwise specialization along
  a trajectory;
* `gradient_step_value_descent_of_lipschitzGradient` in `Chap02/Lemma_2_16.lean`, the weaker
  differentiable-plus-Lipschitz-gradient bridge that reuses this file rather than duplicating the
  descent calculation.

Source/core/bridge triage:
* source-facing: Lemma 1.6.6's explicit gradient-step estimate at a point `x`;
* core/canonical: `taylor_upper_bound_of_contDiffOne_withLipschitzGradient`;
* bridge/view: the evaluation formula `firstOrderTaylorModelAt_apply`.

Primitive data:
* the base point `x`;
* the trial stepsize `h`.

Derived API:
* the value-decrease bound at the antigradient trial point `x - h • ∇ f x`.

The owner quadratic model is
`taylor_upper_bound_of_contDiffOne_withLipschitzGradient` from Lemma 1.5.10.
Lemma 1.6.6 is its antigradient-step specialization, so we keep only that textbook statement as
public API and let downstream uses specialize it directly. The theorem itself is stated on the
same canonical real inner-product-space owner layer as Lemma 1.5.10; specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝⁿ` formulation. -/

-- Proof sketch: apply
-- `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` with
-- `y = x - h • ∇ f x`, then simplify the linear term and the squared norm of the step vector.
/-- Lemma 1.6.6: specializing the owner quadratic upper bound at the trial point
`x - h • ∇ f x` gives the standard gradient-step estimate
`f (x - h ∇ f x) ≤ f x - h (1 - L h / 2) ‖∇ f(x)‖²`. -/
theorem gradient_step_value_decrease_of_contDiffOne_withLipschitzGradient
    (x : E) (h : ℝ) :
    f (x - h • ∇ f x) ≤
      f x - (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f x‖ ^ (2 : ℕ) := by
  -- Rewrite the affine Taylor model at the antigradient trial point into the textbook linear term.
  have hmodel :
      firstOrderTaylorModelAt f x (x - h • ∇ f x) =
        f x - h * ‖∇ f x‖ ^ (2 : ℕ) := by
    simp [sub_eq_add_neg, inner_smul_right, inner_self_eq_norm_sq_to_K, pow_two]
  -- Rewrite the squared displacement so the quadratic remainder is measured by `‖∇ f x‖²`.
  have hsq :
      ‖(x - h • ∇ f x) - x‖ ^ (2 : ℕ) = h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ) := by
    simp [sub_eq_add_neg, norm_smul, mul_pow, sq_abs]
  -- Specialize the quadratic upper model from Lemma 1.5.10 and simplify the resulting scalar factor.
  calc
    f (x - h • ∇ f x) ≤
        firstOrderTaylorModelAt f x (x - h • ∇ f x) +
          ((L : ℝ) / 2) * ‖(x - h • ∇ f x) - x‖ ^ (2 : ℕ) :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hf hgrad x (x - h • ∇ f x)
    _ = f x - h * ‖∇ f x‖ ^ (2 : ℕ) +
          ((L : ℝ) / 2) * (h ^ (2 : ℕ) * ‖∇ f x‖ ^ (2 : ℕ)) := by
      rw [hmodel, hsq]
    _ = f x - (h * (1 - ((L : ℝ) * h) / 2)) * ‖∇ f x‖ ^ (2 : ℕ) := by
      ring

omit hf hgrad

end
