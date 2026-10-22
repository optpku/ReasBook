/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap04.Definition_4_1_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open scoped CubicRegularizationModelNotation

/- Definition 4.2.13 lies in the chapter cubic-regularization / model-value domain.

Sampled owner declarations:
* `secondOrderTaylorModelAt` in `Chap01/Definition_1_4_17`, the upstream quadratic owner whose
  cubic penalization is already packaged in Chapter 4;
* `cubicRegularizationQuadraticApproximation` in `Definition_4_1_3`, the chapter owner for the
  cubic model, with source-facing notation `m[f; M](x; y)`;
* `cubicRegularizationProblem` in `Definition_4_1_3`, the source-facing whole-space minimization
  problem for the cubic model;
* `Φ[f; M](x)`, the Chapter 4 canonical owner for `Φ_M(x)`;
* `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn` in `Definition_4_1_3`, the
  attained-minimum bridge back to the textbook real value.

Best owner abstraction:
* source-facing: `cubicRegularizationProblem f M x`;
* core/canonical: `Φ[f; M](x)`;
* bridge/view: `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`.

Primitive data:
* `f`
* `M`
* `x`

Derived API:
* the owner optimal value `Φ[f; M](x)`
* realization of its real part at a minimizing trial point via
  `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`

Source/core/bridge triage:
* source-facing: the textbook cubic-regularized proximal value `Φ_M(x)`
* core/canonical: `Φ[f; M](x)`
* bridge/view: `cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`

Definition 4.2.13 adds no new owner beyond Definition 4.1.3: the previous local
`cubicRegularizationProximalValue` and `cubicRegularizationProximalValue_eq_of_isMinOn`
duplicated that exact owner interface. This file therefore keeps only the canonical recall/use
surface. -/

section

variable (f : E → ℝ) (M : ℝ) (x T : E)

/- Definition 4.2.13: the cubic-regularized proximal problem at `x` is the source-facing owner
`cubicRegularizationProblem f M x`, and `Φ_M(x)` is its canonical optimal value. -/
recall cubicRegularizationProblem

/- Any global minimizer of the cubic model realizes `Φ_M(x)` through the existing owner theorem
`cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn`. -/
recall cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn

set_option linter.hashCommand false in
#check (Φ[f; M](x) : EReal)

set_option linter.hashCommand false in
#check (f̄[f; M](x) : ℝ)

set_option linter.hashCommand false in
#check
  (show
      IsMinOn (m[f; M](x)) Set.univ T →
        f̄[f; M](x) = m[f; M](x; T) from
    cubicRegularizationProblem_optimalValue_toReal_eq_of_isMinOn)

end
