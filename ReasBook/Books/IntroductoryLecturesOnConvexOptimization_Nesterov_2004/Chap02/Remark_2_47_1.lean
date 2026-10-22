/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Text_2_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

namespace SmoothFunctionalConstraintsMinimizationProblem

/- Remark 2.47.1 lies in the constrained smooth minimax local-model domain.

Domain-style sampling for this refinement:
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47.lean`, the bridge from the constrained problem to the fixed-`t`
  `SmoothMinimaxProblem` owner;
* `SmoothFunctionalConstraintsMinimizationProblem`
  `.existsUnique_isMinOn_regularizedAffineApproximation` in `Text_2_4.lean`, the constrained
  owner well-definedness theorem for the fixed-`t` quadratically regularized affine model;
* `SmoothFunctionalConstraintsMinimizationProblem.constrainedGradientMapping` and
  `SmoothFunctionalConstraintsMinimizationProblem.constrainedReducedGradient` in
  `Definition_2_47.lean`, the source-facing constrained exact-step abbreviations already built on
  that bridge owner;
* `SmoothMinimaxProblem.lowerRegularizedModelValue_le_optimalValue` and
  `SmoothMinimaxProblem.optimalValue_le_upperRegularizedModelValue` in `Text_2_4.lean`, the owner
  optimal-value comparison theorems for the regularized affine models.

Best owner abstraction:
* the fixed-`t` bridge `problem.toParametricSmoothMinimaxProblem t`.

Primitive data:
* the constrained problem `problem`;
* the scalar parameter `t`;
* the linearization point `xBar`;
* the regularization parameter `γ`.

Derived API:
* the constrained exact step and reduced gradient, obtained by specializing the max-type owner to
  the fixed-`t` bridge problem;
* the regularized model-value comparisons at parameters `μ` and `L`;
* the constrained optimal value
  `sInf ((problem.toParametricSmoothMinimaxProblem t) ''
    (problem.toParametricSmoothMinimaxProblem t).feasibleSet)`.

Source/core/bridge triage:
* source-facing: the constrained gradient mapping, constrained reduced gradient, and the two
  constrained optimal-value inequalities in the remark;
* core/canonical: the fixed-`t` owner `problem.toParametricSmoothMinimaxProblem t`, together with
  the max-type exact-step owners and the `SmoothMinimaxProblem` model-value comparisons;
* bridge/view: the constrained step and reduced-gradient abbreviations already provided by
  `Definition_2_47.lean`.

Accordingly this file reuses the constrained step and reduced-gradient owners already introduced in
`Definition_2_47.lean`, and adds only the genuinely new remark-level well-definedness and
optimal-value comparison statements. It keeps no parallel package or surrogate local-model API. -/

section ExactStep

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (t : ℝ)

/-- Remark 2.47.1 (1): for every `t`, the constrained gradient mapping is well defined as the
unique feasible minimizer of the regularized affine model of the fixed-`t` bridge problem. -/
-- Proof sketch: apply the existing constrained owner theorem from `Text_2_4` at the positive
-- regularization parameter `γ`.
theorem existsUnique_constrainedGradientMapping
    (xBar : E) (γ : NNRealˣ) :
    ∃! xPlus : E,
      xPlus ∈ problem.ambientSet ∧
        IsMinOn
          (quadraticallyRegularizedObjective
            ((problem.toParametricSmoothMinimaxProblem t).affineApproximation xBar)
            γ
            xBar)
          problem.ambientSet
          xPlus :=
    problem.existsUnique_isMinOn_regularizedAffineApproximation t xBar γ

end ExactStep

section ModelValueComparison

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L)
variable (t : ℝ) (xBar : E)

/-- Remark 2.47.1 (2): the constrained regularized model value with curvature `μ` is bounded above
by the constrained optimal value of the fixed-`t` bridge problem. -/
-- Proof sketch: apply
-- `SmoothMinimaxProblem.lowerRegularizedModelValue_le_optimalValue` to
-- `problem.toParametricSmoothMinimaxProblem t` at base point `xBar`, then rewrite its feasible
-- set as `problem.ambientSet`.
theorem lowerRegularizedModelValue_le_parametricProblemOptimalValue :
    problem.regularizedModelValue t xBar μ ≤
      sInf ((problem.toParametricSmoothMinimaxProblem t) '' problem.ambientSet) := by
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (problem.toParametricSmoothMinimaxProblem t).lowerRegularizedModelValue_le_optimalValue xBar

/-- Remark 2.47.1 (3): the constrained optimal value of the fixed-`t` bridge problem is bounded
above by the constrained regularized model value with curvature `L`. -/
-- Proof sketch: apply
-- `SmoothMinimaxProblem.optimalValue_le_upperRegularizedModelValue` to
-- `problem.toParametricSmoothMinimaxProblem t` at base point `xBar`, then rewrite its feasible
-- set as `problem.ambientSet`.
theorem parametricProblemOptimalValue_le_upperRegularizedModelValue :
    sInf ((problem.toParametricSmoothMinimaxProblem t) '' problem.ambientSet) ≤
      problem.regularizedModelValue t xBar L := by
  simpa [SmoothFunctionalConstraintsMinimizationProblem.regularizedModelValue] using
    (problem.toParametricSmoothMinimaxProblem t).optimalValue_le_upperRegularizedModelValue xBar

end ModelValueComparison

end SmoothFunctionalConstraintsMinimizationProblem
