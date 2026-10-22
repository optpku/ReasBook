/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Primary domain: quadratic norm inequalities over a seminormed additive group.

Sampled owner-style declarations in this domain:
- `sq_nonneg`, the exact algebraic owner for the weighted quadratic inequality;
- `norm_sub_le`, the triangle inequality in subtraction form;
- `sq_le_sq₀`, the canonical passage from a nonnegative inequality to the squared inequality;
- `mul_le_mul_of_nonneg_left`, the owner monotonicity lemma for nonnegative scalar multiplication;

Best owner abstraction:
- there is no higher project owner object here; the canonical owners are the four mathlib scalar
  and norm inequalities above, and this file should remain a thin source-facing bridge.

Source/core/bridge triage:
- source-facing: the two-step weighted quadratic chain from the textbook lemma;
- core/canonical: the four owner lemmas above;
- bridge/view: specializing those owner inequalities to the weights `α` and `1 - α`.

Primitive data:
- a seminormed additive group `E`,
- points `x y : E`,
- a weight `α : ℝ`.

Derived API:
- the two atomic weighted quadratic inequalities below;
- the chained quadratic bound of Lemma 2.4, recovered as a thin wrapper.
-/

variable {E : Type*} [SeminormedAddGroup E]

/-- For every real weight `α`, the weighted square of `‖x‖ + ‖y‖` is bounded above by the
corresponding affine combination of `‖x‖²` and `‖y‖²`. -/
-- Proof sketch: the difference between the right-hand side and the left-hand side is the exact
-- square `(α * ‖x‖ - (1 - α) * ‖y‖)^2`.
theorem weighted_norm_sum_sq_le_convex_combination_norm_sq
    (x y : E) (α : ℝ) :
    α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 ≤ α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  nlinarith [sq_nonneg (α * ‖x‖ - (1 - α) * ‖y‖)]

/-- For `α ∈ [0, 1]`, the weighted squared distance `‖x - y‖²` is bounded above by the weighted
squared sum bound coming from the triangle inequality. -/
-- Proof sketch: square `norm_sub_le x y` and multiply by the nonnegative factor
-- `α * (1 - α)`.
theorem weighted_norm_sub_sq_le_weighted_norm_sum_sq
    (x y : E) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    α * (1 - α) * ‖x - y‖ ^ 2 ≤ α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 := by
  have hα0 : 0 ≤ α := hα.1
  have h1α : 0 ≤ 1 - α := sub_nonneg.mpr hα.2
  have hsq : ‖x - y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).2
      (norm_sub_le x y)
  exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hα0 h1α)

/-- Lemma 2.4: for `α ∈ [0, 1]`, the weighted squared distance is bounded by the intermediate
weighted square of `‖x‖ + ‖y‖`, which is bounded by the convex combination of `‖x‖²` and
`‖y‖²`. -/
theorem convex_combination_norm_sq_bounds
    (x y : E) (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    α * (1 - α) * ‖x - y‖ ^ 2 ≤ α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 ∧
      α * (1 - α) * (‖x‖ + ‖y‖) ^ 2 ≤ α * ‖x‖ ^ 2 + (1 - α) * ‖y‖ ^ 2 := by
  exact ⟨weighted_norm_sub_sq_le_weighted_norm_sum_sq x y α hα,
    weighted_norm_sum_sq_le_convex_combination_norm_sq x y α⟩

end
