/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Algorithm_1_6_1
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.FirstOrderTaylorModel
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Lemma_1_5_10

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Gradient

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/- Primary domain:
* first-order smooth optimization on real Hilbert spaces

Relevant owner-style declarations sampled before refining:
* `firstOrderTaylorModelAt` in `FirstOrderTaylorModel.lean`
* `quadraticallyRegularizedObjective` in `FirstOrderTaylorModel.lean`
* `gradient_quadratic_model_eq_completedSquare` in `FirstOrderTaylorModel.lean`
* `gradientMethod` in `Algorithm_1_6_1.lean`
* `isMinOn_univ_iff` in mathlib's `Order.Filter.Extr`
* `taylor_upper_bound_of_contDiffOne_withLipschitzGradient` in `Lemma_1_5_10.lean`

Source/core/bridge triage:
* source-facing: Proposition 1.8.1's quadratically regularized first-order Taylor model,
  its minimizer, and its global upper-approximation inequality
* core/canonical owner:
  `quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar`
  together with `gradient_quadratic_model_eq_completedSquare`, `IsMinOn`, `gradientMethod`, and
  the smooth upper Taylor estimate from `Lemma_1_5_10`
* bridge/view: the owner completed-square rewrite, which turns the regularized model into a
  manifestly nonnegative quadratic error term

Primitive data:
* the objective `f`, the base point `xBar`, and the step size `h`
* the smoothness hypotheses `ContDiff ℝ 1 f` and `LipschitzWith L (∇ f)`

Derived API:
* the source-facing minimizer statement for the regularized first-order model
* the global upper-approximation inequality

The public API is therefore organized around the source-facing regularized first-order model.
Since the proposition uses only the Hilbert-space owners above and no coordinate-specific data,
the Euclidean matrix quadratic bridge is removed rather than retained as a parallel local API. -/

/-- Proposition 1.8.1 (1): the regularized first-order Taylor model with quadratic parameter `1 / h`
is minimized at the first iterate of the constant-step gradient method. -/
-- Proof sketch: rewrite the regularized first-order model by completing the square around the
-- gradient step `xBar - h • ∇ f xBar`, identify that point with
-- `gradientMethod (fun _ ↦ h) f xBar 1`, using the owner theorem
-- `gradient_quadratic_model_eq_completedSquare`, and then use nonnegativity of the remaining
-- quadratic term.
theorem gradientMethodUpperModel_isMinOn (f : E → ℝ)
    (xBar : E) {h : ℝ} (hh : 0 < h) :
    IsMinOn
      (quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar)
      Set.univ
      (gradientMethod (fun _ ↦ h) f xBar 1) := by
  rw [isMinOn_univ_iff]
  intro x
  have hδ : (1 / h : ℝ) ≠ 0 := one_div_ne_zero hh.ne'
  have hstep : gradientMethod (fun _ ↦ h) f xBar 1 = xBar - h • ∇ f xBar := by
    simp
  have hstepModel :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar
        (gradientMethod (fun _ ↦ h) f xBar 1) =
        f xBar - (h / 2) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa [hstep, one_div, hh.ne'] using
      gradient_quadratic_model_eq_completedSquare
        f xBar (gradientMethod (fun _ ↦ h) f xBar 1) hδ
  have hxModel :
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x =
        f xBar + ((1 / h : ℝ) / 2) * ‖x - (xBar - h • ∇ f xBar)‖ ^ (2 : ℕ) -
          (h / 2) * ‖∇ f xBar‖ ^ (2 : ℕ) := by
    simpa [one_div, hh.ne'] using gradient_quadratic_model_eq_completedSquare f xBar x hδ
  rw [hstepModel, hxModel]
  have hnonneg : 0 ≤ ((1 / h : ℝ) / 2) * ‖x - (xBar - h • ∇ f xBar)‖ ^ (2 : ℕ) := by
    positivity
  linarith

/-- Proposition 1.8.1 (2): if `f` belongs to the chapter's `C^{1,1}_L` owner class and
`0 < h` with `(L : ℝ) * h ≤ 1`, then the regularized first-order Taylor model with quadratic
parameter `1 / h` is a global upper approximation of `f`. -/
-- Proof sketch: apply the standard quadratic upper Taylor bound at `xBar` and compare the
-- coefficient `L / 2` with `((1 / h) / 2)` using `(L : ℝ) * h ≤ 1`.
theorem gradientMethodUpperModel_isGlobalUpperApproximation {L : NNReal}
    (f : E → ℝ) (xBar x : E) {h : ℝ}
    (hf : ContDiff ℝ 1 f) (hgrad : LipschitzWith L (∇ f))
    (hh : 0 < h) (hLh : (L : ℝ) * h ≤ 1) :
    f x ≤
      quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x := by
  have hcoeff : ((L : ℝ) / 2) ≤ (1 / h) / 2 := by
    have hLinv : (L : ℝ) ≤ 1 / h := by
      rw [le_div_iff₀ hh]
      simpa [mul_comm] using hLh
    exact div_le_div_of_nonneg_right hLinv (by norm_num)
  calc
    f x ≤ firstOrderTaylorModelAt f xBar x + ((L : ℝ) / 2) * ‖x - xBar‖ ^ (2 : ℕ) :=
      taylor_upper_bound_of_contDiffOne_withLipschitzGradient hf hgrad xBar x
    _ ≤ quadraticallyRegularizedObjective (firstOrderTaylorModelAt f xBar) (1 / h) xBar x := by
      rw [quadraticallyRegularizedObjective_apply]
      gcongr

end
