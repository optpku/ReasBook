/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_35_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient ProjectedGradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain: projected-gradient quadratic model subproblems on a nonempty closed convex set
in a complete real inner-product space.

Owner declarations sampled for this item:
* `firstOrderTaylorModelAt` and `quadraticallyRegularizedObjective` in
  `Definition_1_4_17.lean`, which own the affine tangent model and its quadratic regularization;
* `gradient_quadratic_model_eq_completedSquare` in `Chap01/FirstOrderTaylorModel.lean`, the
  owner completed-square bridge for that regularized first-order model;
* `gradientStep`, `gradientMapping`, and `reducedGradient` in `Definition_2_35_1.lean`, which own
  the projected-gradient step, its projected point, and the scaled residual;
* `gradientMapping_isProjectionPointOn` in `Definition_2_35_1.lean`, the canonical projection
  certificate for the projected-gradient point.

Source/core/bridge triage:
* source-facing: Definition 2.35's minimizer formula and reduced-gradient residual formula;
* core/canonical: `gradientMapping` and `reducedGradient`;
* bridge/view: the minimizing-property theorem below, together with the reused owner rewrite
  `gradient_quadratic_model_eq_completedSquare`.

This file therefore keeps the owner declarations themselves as direct recalls and states only the
thin bridge theorem needed to recover the textbook minimizer characterization, reusing the Chapter
1 completed-square identity directly instead of duplicating it locally. -/

/- Definition 2.35: the textbook gradient mapping and reduced gradient are represented by the
canonical owner declarations `gradientMapping` and `reducedGradient`. The point
`gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ` is the unique minimizer of the
quadratically regularized first-order Taylor model over `Q`, and
`reducedGradient Q hQ_nonempty hQ_closed hQ_convex f xBar γ` is the scaled residual
`γ • (xBar - gradientMapping Q hQ_nonempty hQ_closed hQ_convex f xBar γ)`. -/
recall gradientMapping
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E

recall reducedGradient
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (Q : Set E) (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    (f : E → ℝ) (xBar : E) (γ : NNRealˣ) :
    E

/-- The projected-gradient point belongs to `Q` and minimizes the quadratically regularized
first-order Taylor model from Definition 2.35 over `Q`. -/
-- Proof sketch: rewrite the objective using
-- `gradient_quadratic_model_eq_completedSquare`; up to an additive constant it becomes the squared
-- distance to `gradientStep f xBar γ`. Then apply the projection optimality of
-- `gradientMapping_isProjectionPointOn`.
theorem gradientMapping_minimizes_objective
    {Q : Set E} (hQ_nonempty : Q.Nonempty)
    (hQ_closed : IsClosed Q) (hQ_convex : Convex ℝ Q)
    {f : E → ℝ} {xBar : E} {γ : NNRealˣ} :
    x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) ∈ Q ∧
      IsMinOn
        (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) γ xBar)
        Q
        x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar) := by
  let xQ := x_Q[Q; hQ_nonempty; hQ_closed; hQ_convex | f; γ](xBar)
  let step := gradientStep f xBar γ
  have hproj : IsProjectionPointOn Q step xQ := by
    simpa [xQ, step] using
      gradientMapping_isProjectionPointOn Q hQ_nonempty hQ_closed hQ_convex f γ xBar
  refine ⟨hproj.1, ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hγ : 0 < (γ : ℝ) := by
    exact NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (Units.ne_zero γ))
  have hdist : ‖xQ - step‖ ≤ ‖y - step‖ :=
    isMinOn_iff.mp hproj.isMinOn y hy
  have hsq : ‖xQ - step‖ ^ (2 : ℕ) ≤ ‖y - step‖ ^ (2 : ℕ) :=
    pow_le_pow_left₀ (norm_nonneg _) hdist 2
  have hxQ_model :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (γ : ℝ) xBar xQ =
        f xBar + ((γ : ℝ) / 2) * ‖xQ - step‖ ^ (2 : ℕ) -
          (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
      simpa [xQ, step, gradientStep] using
        gradient_quadratic_model_eq_completedSquare f xBar xQ hγ.ne'
  have hy_model :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (γ : ℝ) xBar y =
        f xBar + ((γ : ℝ) / 2) * ‖y - step‖ ^ (2 : ℕ) -
          (1 / (2 * (γ : ℝ))) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa [step, gradientStep] using
      gradient_quadratic_model_eq_completedSquare f xBar y hγ.ne'
  rw [hxQ_model, hy_model]
  nlinarith [hsq, hγ]

end
