/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: projected-gradient / Euclidean-projection step formulas on a complete real
inner-product space, with the textbook `ℝⁿ` formulas recovered by specialization.

Owner declarations sampled for this refinement:
* `IsProjectionPointOn` in `Chap07/Definition_7_3`, the primitive nearest-point predicate;
* `euclideanProjection` and `euclideanProjection_univ` in `Theorem_2_33`, the chapter's chosen
  projection map and its owner `Set.univ` specialization;
* `gradientMapping` and `reducedGradient` in `Definition_2_35_1`, the source-facing
  projected-gradient point and residual.

Best owner abstraction:
* source-facing: `gradientMapping` and `reducedGradient`;
* core/canonical: `IsProjectionPointOn` and `euclideanProjection`;
* bridge/view: the solved-form step identity and the `Set.univ` specializations in this remark.

Primitive data:
* the feasible set `Q` with nonempty / closed / convex structure;
* the objective `f`, base point `xBar`, and parameter `γ`.

Derived API:
* the explicit step identity recovered from `reducedGradient`;
* the whole-space formulas recovered from `euclideanProjection_univ`.

This file therefore keeps only the source-facing bridge theorems and reuses the owner projection
theorem for the `Set.univ` specialization instead of reproving projection uniqueness locally. -/

section

variable
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ)

/-- Remark 2.35.1: the projected-gradient point is obtained from `xBar` by a step of size `1 / γ`
in the direction of the reduced gradient. -/
-- Proof sketch: start from the defining identity
-- `reducedGradient = γ • (xBar - gradientMapping)` and multiply by `γ⁻¹`.
theorem gradientMapping_eq_point_sub_inv_smul_reducedGradient
    :
    x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) =
      xBar - (γ : ℝ)⁻¹ • g_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) := by
  have hγ : (γ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero γ
  simp [reducedGradient, smul_smul, hγ]

end

/-- When the feasible set is all of the ambient space, the projected-gradient point is the ordinary
gradient step with stepsize `1 / γ`. The textbook statement on `ℝⁿ` is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: unfold `gradientMapping` and apply the owner theorem `euclideanProjection_univ`
-- to the explicit gradient step.
@[simp] theorem gradientMapping_univ_eq_gradient_step
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    x_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; γ](xBar) =
      gradientStep f xBar γ := by
  simp [gradientMapping]

/-- For the unconstrained problem on the ambient space, the reduced gradient equals the ordinary
gradient. The textbook statement on `ℝⁿ` is the specialization
`E = EuclideanSpace ℝ (Fin n)`. -/
-- Proof sketch: substitute `gradientMapping_univ_eq_gradient_step` into the defining identity
-- `reducedGradient = γ • (xBar - gradientMapping)` and simplify the scalar factor
-- `γ * γ⁻¹ = 1`.
@[simp] theorem reducedGradient_univ_eq_gradient
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    g_Q[(Set.univ : Set E); Set.univ_nonempty; isClosed_univ; convex_univ | f; γ](xBar) =
      ∇ f xBar := by
  rw [reducedGradient, gradientMapping_univ_eq_gradient_step]
  have hγ : (γ : ℝ) ≠ 0 := by
    exact_mod_cast Units.ne_zero γ
  simp [gradientStep, hγ]

end
