/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Theorem_1_4_13

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

/- Primary domain: differentiable minimization of quadratically regularized objectives on a real
inner-product space.

Owner declarations sampled before refining:
* `quadraticallyRegularizedObjective` in `FirstOrderTaylorModel.lean`, the owner quadratic
  regularization;
* `isMinOn_hasGradientAt_zero_of_differentiableAt` in `Theorem_1_4_13.lean`, the owner
  stationary-point theorem for differentiable whole-space minimizers;
* `DifferentiableAt.hasGradientAt` is the owner bridge from differentiability to gradients;
* `hasFDerivAt_sub_const` together with `HasFDerivAt.norm_sq` gives the centered quadratic
  penalty derivative canonically.

Best owner abstraction:
* source-facing: Proposition 2.13 for `f : ℝⁿ → ℝ`;
* core/canonical: the real inner-product-space objective
  `quadraticallyRegularizedObjective f δ x0` together with `HasGradientAt` and `IsMinOn`;
* bridge/view: the Euclidean specialization obtained by instantiating
  `E := EuclideanSpace ℝ (Fin n)`.

Primitive data:
* the objective `f`;
* the regularization parameter `δ`;
* the center `x0`.

Derived API:
* the stationary condition at a minimizer of `quadraticallyRegularizedObjective f δ x0`. -/

section Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- Proposition 2.13: at a minimizer of the quadratically regularized objective
`x ↦ f x + (δ / 2) ‖x - x₀‖²`, if `f` is differentiable at the
minimizer then the gradient of `f` balances the centered quadratic penalty:
`∇ f xδStar + δ • (xδStar - x0) = 0`.

The source proposition is stated for `f : ℝⁿ → ℝ`, but the proof uses only the canonical real
inner-product-space gradient calculus. Convexity of `f` and positivity of `δ` belong to the
ambient optimization setting, while the displayed first-order identity itself uses only
differentiability at the minimizer and the minimizing hypothesis. -/
-- Proof sketch: the regularized objective is differentiable, with gradient
-- `x ↦ ∇ f x + δ • (x - x0)`. The whole-space minimizer theorem
-- `isMinOn_hasGradientAt_zero_of_differentiableAt` gives vanishing gradient at `xδStar`;
-- uniqueness of gradients then identifies the displayed vector with `0`.
theorem gradient_add_quadratic_regularization_eq_zero_of_isMinOn
    (f : E → ℝ) (δ : ℝ) (x0 xδStar : E)
    (hf_diff : DifferentiableAt ℝ f xδStar)
    (hxδStar : IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xδStar) :
    ∇ f xδStar + δ • (xδStar - x0) = 0 := by
  let penalty : E → ℝ := fun x ↦ (δ / 2) * ‖x - x0‖ ^ (2 : ℕ)
  have hpenalty :
      HasGradientAt penalty (δ • (xδStar - x0)) xδStar := by
    have hsub : HasFDerivAt (fun x : E ↦ x - x0) (.id ℝ E) xδStar := by
      simpa using
        (hasFDerivAt_sub_const x0 :
          HasFDerivAt (fun x : E ↦ x - x0) (.id ℝ E) xδStar)
    have hnormSq :
        HasFDerivAt (fun x : E ↦ ‖x - x0‖ ^ (2 : ℕ))
          (2 • innerSL ℝ (xδStar - x0)) xδStar := by
      simpa using hsub.norm_sq
    have hsmul :
        HasFDerivAt (fun x : E ↦ (δ / 2) * ‖x - x0‖ ^ (2 : ℕ))
          ((δ / 2) • (2 • innerSL ℝ (xδStar - x0))) xδStar := by
      simpa [smul_eq_mul] using hnormSq.const_smul (δ / 2)
    have hlin :
        ((δ / 2) • (2 • innerSL ℝ (xδStar - x0))) =
          InnerProductSpace.toDual ℝ E (δ • (xδStar - x0)) := by
      ext y
      simp [InnerProductSpace.toDual_apply_apply, two_smul]
      ring
    have hsmul' :
        HasFDerivAt penalty
          (InnerProductSpace.toDual ℝ E (δ • (xδStar - x0))) xδStar := by
      exact hlin ▸ hsmul
    simpa [penalty] using hsmul'.hasGradientAt
  have hregularized :
      HasGradientAt (quadraticallyRegularizedObjective f δ x0)
        (∇ f xδStar + δ • (xδStar - x0)) xδStar := by
    have hf_fderiv := hf_diff.hasGradientAt.hasFDerivAt
    have hsum_fderiv := hf_fderiv.add hpenalty.hasFDerivAt
    simpa [penalty, quadraticallyRegularizedObjective_apply] using
      hsum_fderiv.hasGradientAt
  have hstationary :
      HasGradientAt (quadraticallyRegularizedObjective f δ x0) 0 xδStar := by
    exact isMinOn_hasGradientAt_zero_of_differentiableAt hregularized.differentiableAt hxδStar
  exact hregularized.unique hstationary

end Gradient
