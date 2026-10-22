/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_47

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

/- Definition 2.49 lies in the Chapter 2 constrained regularized local-model-value domain.

Sampled owner declarations:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44.lean`, the owner ambient
  constrained problem carrying the feasible set, objective, and constraint family;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, the fixed-`t` bridge to the chapter's smooth minimax owner;
* `SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue` in
  `Definition_2_47.lean`, the owner constrained regularized affine-model value;
* `quadraticallyRegularizedObjective` in `Definition_1_4_17.lean`, the underlying regularized
  affine model whose feasible-set infimum defines that owner value.

Best owner abstraction:
* `problem.regularizedModelValue t xBar γ`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the base point `xBar`;
* the regularization parameter `γ`.

Derived API:
* the fixed-`t` bridge problem `problem.toParametricSmoothMinimaxProblem t`;
* its affine approximation at `xBar`;
* the explicit constrained `sInf` formula obtained by unfolding the owner definition.

Source/core/bridge triage:
* source-facing: the textbook constrained regularized model value;
* core/canonical: `problem.regularizedModelValue t xBar γ`;
* bridge/view: the explicit feasible-set infimum of the quadratically regularized affine model.

This recall file therefore reuses the owner declaration from `Definition_2_47` directly instead
of restating the same `sInf` expression as a parallel main API.
-/

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)

/- Definition 2.49: the constrained regularized local-model value is the owner scalar function
`problem.regularizedModelValue`. -/
recall SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue

section

variable (t γ : ℝ) (xBar : E)

#check problem.regularizedModelValue t xBar γ

/- Unfolding the recalled owner gives the textbook constrained infimum formula. -/
#check
  (by
    simp [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] :
      problem.regularizedModelValue t xBar γ =
        sInf
          ((quadraticallyRegularizedObjective
              ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
              γ
              xBar) '' problem.ambientSet))

end

end
