/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Proposition_6_10

-- Declarations for this item will be appended below by the statement pipeline.

/- Example 6.1.3 lies in the chapter's explicit-model smoothing / within-set differential-calculus
domain.

Primary domain:
- within-set differentiability and gradient Lipschitzness for the explicit-model smoothed
  objective, with the textbook `ℝⁿ` / `ℝᵐ` presentation obtained by specializing the ambient
  spaces to `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin m)`

Sampled owner-style declarations:
- `explicitModelSmoothedProblem` in `Chap06/Definition_6_9`, the chapter owner of the smoothed
  explicit-model objective;
- `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn` in
  `Chap06/Proposition_6_10`, the canonical derivative/Lipschitz theorem for that owner;
- mathlib `HasFDerivWithinAt`, the pointwise within-set derivative owner;
- mathlib `LipschitzOnWith`, the canonical owner of the set-restricted Lipschitz bound.

Best owner abstraction:
- source-facing: the explicit-model smoothed objective from Definition 6.9;
- core/canonical: `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn`;
- bridge/view: the Euclidean specialization of that theorem to the textbook finite-dimensional
  spaces.

Primitive data:
- the feasible set `Q₁`, model term `hatf`, smoothing term `fμ`, and their chosen derivative
  fields;
- the within-set derivative hypotheses;
- the Lipschitz constants `M` and `Real.toNNReal ((1 / μ) * ‖A‖ ^ (2 : ℕ))`.

Derived API:
- the derivative selection of the smoothed objective;
- the Lipschitz estimate for the summed derivative field.

Source/core/bridge triage:
- source-facing: the explicit-model smoothing example stated in equation `(6.1.26)`;
- core/canonical: `explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn`;
- bridge/view: the Euclidean textbook specialization.

The previous file introduced a Euclidean-specialized theorem shell whose proof was a single
`simpa` from the Chapter 6 owner theorem, together with a one-off abbreviation for the displayed
constant `L_μ = M + (1 / μ) ‖A‖²`. Neither declaration carried new mathematical content or owned
primitive data, so this refinement removes that parallel API and keeps Example 6.1.3 as a direct
recall of the canonical chapter theorem. -/

/- Example 6.1.3 is the Euclidean specialization of the chapter owner theorem
`explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn`. -/
recall explicitModelSmoothedProblem_hasFDerivWithinAt_and_gradient_lipschitzOn
