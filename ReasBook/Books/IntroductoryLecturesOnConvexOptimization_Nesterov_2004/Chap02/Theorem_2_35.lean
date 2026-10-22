/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1

open scoped Gradient ProjectedGradient

noncomputable section

universe u

/- Theorem 2.35 lies in constrained projected-gradient fixed points and projection optimality on
real inner-product spaces, with the textbook fixed-point statement specialized back to `ℝⁿ`.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn Q y p` in `Chap07/Definition_7_3`, the owner predicate for nearest-point
  data;
* `gradientMapping` in `Definition_2_35_1`, the source-facing projected-gradient point;
* `HasGradientAt`, the canonical gradient owner predicate on real inner-product spaces;
* `ConvexOn.isMinOn_iff_variational_inequality_of_hasGradientAt` in `Theorem_2_29`, the chapter
  owner theorem for convex first-order optimality;
* `sub_mem_posTangentConeAt_of_segment_subset` and
  `IsLocalMinOn.hasFDerivWithinAt_nonneg`, the owner first-order optimality API for a
  differentiable minimizer on a convex feasible set;
* `norm_eq_iInf_iff_real_inner_le_zero`, the owner characterization of projection points on a
  convex set by the variational inequality.

Best owner abstraction:
* `HasGradientAt f g xStar` together with
  `IsProjectionPointOn Q (xStar - γ⁻¹ • g) xStar`.

Source/core/bridge triage:
* source-facing: Theorem 2.35 as the fixed-point statement for the textbook projected-gradient map
  on `ℝⁿ`;
* core/canonical: `IsProjectionPointOn Q (xStar - γ⁻¹ • g) xStar`;
* bridge/view: the specialization from an explicit gradient witness to the textbook gradient
  step, followed by the chosen Euclidean projection map.

Primitive data:
* the feasible set `Q`, objective `f`, minimizer `xStar`, gradient witness `g`, and positive
  inverse-stepsize parameter `γ`;
* convexity of `Q`;
* feasibility of `xStar`, optimality of `xStar` on `Q`, and a gradient witness for `f` at
  `xStar`.

Derived API:
* the owner projection-point statement for `xStar`;
* the fixed-point equality for `gradientMapping`, obtained from the chosen Euclidean projection.
-/

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

variable
  {Q : Set E}
  {f : E → ℝ}
  {xStar : E}
  {g : E}
  {γ : NNRealˣ}

/-- Helper for Theorem 2.35: a constrained minimizer on a convex set is the projection of the
explicit step determined by any gradient witness `g` at `xStar`. -/
theorem isProjectionPointOn_gradientStep_of_isMinOn
    (hQ_convex : Convex ℝ Q)
    (hxStar : xStar ∈ Q) (hopt : IsMinOn f Q xStar)
    (hf_grad : HasGradientAt f g xStar) :
    IsProjectionPointOn Q (xStar - ((γ : ℝ)⁻¹) • g) xStar := by
  -- Convert first-order optimality at the minimizer into the projection variational inequality
  -- for the explicit gradient step.
  have hvariational :
      ∀ x ∈ Q, inner ℝ ((xStar - ((γ : ℝ)⁻¹) • g) - xStar) (x - xStar) ≤ 0 := by
    intro x hx
    have hγ : 0 < (γ : ℝ) := by
      exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
    have hdir : x - xStar ∈ posTangentConeAt Q xStar := by
      exact sub_mem_posTangentConeAt_of_segment_subset (hQ_convex.segment_subset hxStar hx)
    have hfirstOrder :=
      hopt.localize.hasFDerivWithinAt_nonneg hf_grad.hasFDerivAt.hasFDerivWithinAt hdir
    have hgrad :
        0 ≤ inner ℝ g (x - xStar) := by
      simpa [hf_grad.hasFDerivAt.fderiv, innerSL_apply_apply] using hfirstOrder
    have hscaled : 0 ≤ (γ : ℝ)⁻¹ * inner ℝ g (x - xStar) :=
      mul_nonneg (inv_nonneg.mpr hγ.le) hgrad
    simpa [sub_eq_add_neg, inner_smul_left, mul_comm, mul_left_comm, mul_assoc] using
      (neg_nonpos.mpr hscaled)
  -- Package that variational inequality into the canonical projection-point predicate.
  have hmin :
      ‖(xStar - ((γ : ℝ)⁻¹) • g) - xStar‖ =
        ⨅ w : Q, ‖(xStar - ((γ : ℝ)⁻¹) • g) - w‖ :=
    (norm_eq_iInf_iff_real_inner_le_zero hQ_convex hxStar).2 hvariational
  exact IsProjectionPointOn.of_norm_eq_iInf hxStar hmin

/-- Theorem 2.35: every optimal solution on a closed convex feasible set is a fixed point of the
projected-gradient mapping for every positive inverse-stepsize parameter on a complete real
inner-product space.
The textbook `ℝⁿ` statement is the specialization `E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: let `p = gradientMapping Q ⟨xStar, hxStar⟩ hQ_closed hQ_convex f xStar γ
--`. The minimizing property of `p` gives the projection variational
-- inequality, while the optimality of `xStar` and differentiability of `f` at `xStar` give the
-- first-order necessary optimality inequality at `xStar`. Evaluating these two inequalities at
-- `xStar` and `p` respectively yields `‖p - xStar‖ ^ 2 = 0`, so `p = xStar`.
theorem gradientMapping_eq_of_isMinOn
    (Q : Set E) {f : E → ℝ} {xStar : E} {γ : NNRealˣ}
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (hxStar : xStar ∈ Q) (hopt : IsMinOn f Q xStar)
    (hf_diff : DifferentiableAt ℝ f xStar) :
    x_Q[Q; ⟨xStar, hxStar⟩; hQ_closed; hQ_convex | f; γ](xStar) = xStar := by
  let hQ_nonempty : Q.Nonempty := ⟨xStar, hxStar⟩
  -- First show that the minimizer is itself a projection point of its gradient step.
  have hproj :
      IsProjectionPointOn Q (gradientStep f xStar γ) xStar :=
    by
      simpa [gradientStep] using
        isProjectionPointOn_gradientStep_of_isMinOn hQ_convex hxStar hopt hf_diff.hasGradientAt
  -- Then identify that projection point with the chosen Euclidean projection used by
  -- `gradientMapping`.
  simpa [hQ_nonempty, gradientMapping] using
    (hproj.eq_euclideanProjection hQ_nonempty hQ_closed hQ_convex).symm
end
