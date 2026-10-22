/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_4_17

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/- Definition 2.24 lies in the quadratic-regularization domain for unconstrained minimization.

Sampled owner-style declarations:
* `quadraticallyRegularizedObjective` in `Chap01/Definition_1_4_17`, the canonical owner of the
  regularized objective `x ↦ f x + (δ / 2) ‖x - x₀‖²`;
* `quadraticallyRegularizedObjective_apply`, the evaluation formula for that owner;
* `IsMinOn`, the canonical whole-space minimizer predicate;
* `isMinOn_univ_iff`, the bridge from whole-space minimization to the textbook pointwise
  inequality.

Best owner abstraction:
* source-facing/core: `quadraticallyRegularizedObjective f δ x₀`;
* bridge/view: `quadraticallyRegularizedObjective_apply`;
* bridge/view: `IsMinOn (quadraticallyRegularizedObjective f δ x₀) Set.univ xδStar`.

Primitive data:
* the objective `f : E → ℝ`;
* the regularization parameter `δ : ℝ`;
* the center `x₀ : E`.

Derived API:
* the explicit evaluation formula for the regularized objective;
* for a named point `xδStar`, the whole-space minimizing predicate for the regularized objective;
* the equivalent textbook inequality formulation on `Set.univ`.

This item is therefore a recall-style use of the existing owner declarations, not a new local
wrapper around regularized objectives or optimal points. The source-facing entry is the
regularized objective itself; minimizer statements are only companion views once a candidate point
has been specified. -/

section

variable (f : E → ℝ) (δ : ℝ) (x0 : E)

/- Definition 2.24: the regularized function
`f_δ(x) = f(x) + (δ / 2) ‖x - x₀‖²` is the canonical quadratic-regularization owner
`quadraticallyRegularizedObjective f δ x₀`. -/
recall quadraticallyRegularizedObjective

set_option linter.hashCommand false in
#check quadraticallyRegularizedObjective f δ x0

recall quadraticallyRegularizedObjective_apply

example (x : E) :
    quadraticallyRegularizedObjective f δ x0 x =
      f x + (δ / 2) * ‖x - x0‖ ^ (2 : ℕ) :=
  quadraticallyRegularizedObjective_apply f δ x0 x

end

section

variable (f : E → ℝ) (δ : ℝ) (x0 xDeltaStar : E)

recall IsMinOn
recall isMinOn_univ_iff

/- The whole-space optimality statement for the regularized objective is exactly the canonical
`IsMinOn` owner specialized to `Set.univ`. -/
example :
    IsMinOn (quadraticallyRegularizedObjective f δ x0) Set.univ xDeltaStar ↔
      ∀ x : E,
        quadraticallyRegularizedObjective f δ x0 xDeltaStar ≤
          quadraticallyRegularizedObjective f δ x0 x :=
  isMinOn_univ_iff

end
