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

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {m : ℕ} {μ L : ℝ}

section

variable (problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L) (t : ℝ)

/-
Primary domain: constrained max-type minimization on a complete real inner-product space for a
fixed parameter `t`.

Owner declarations sampled before refining:
* `SmoothFunctionalConstraintsMinimizationProblem` in `Definition_2_44`, which owns the primitive
  ambient set `Q`, objective `f₀`, and constraint family `fᵢ`;
* `SmoothFunctionalConstraintsMinimizationProblem.toParametricSmoothMinimaxProblem` in
  `Definition_2_47`, the bridge to the fixed-`t` owner `SmoothMinimaxProblem`;
* `SmoothMinimaxProblem` in `Definition_2_38`, which owns the feasible set/objective pair for the
  max-type problem;
* `SmoothMinimaxProblem.existsUnique_isMinOn` in `Definition_2_38`, the owner unique-minimizer
  theorem for a fixed-parameter smooth minimax problem.

Best owner abstraction:
* `problem.toParametricSmoothMinimaxProblem t`.

Primitive data:
* the constrained problem `problem : SmoothFunctionalConstraintsMinimizationProblem E m μ L`;
* the scalar parameter `t`.

Derived API:
* the fixed-`t` max-type objective as the coerced objective
  `problem.toParametricSmoothMinimaxProblem t`;
* the feasible set
  `(problem.toParametricSmoothMinimaxProblem t).feasibleSet = problem.ambientSet`;
* the unique-minimizer conclusion stated by `IsMinOn`.

Source/core/bridge triage:
* source-facing: Proposition 2.24's unique minimizer claim for
  `x ↦ max {f₀(x) - t, f₁(x), …, fₘ(x)}` on `Q`;
* core/canonical: the owner fixed-`t` problem `parametricProblem`;
* bridge/view: the explicit
  `problem.toLagrangianProblem.constrainedAuxiliaryObjective t` presentation, which remains a
  companion view but not the main public surface here.

This proposition is exact owner recall: the fixed-`t` textbook max-type problem is the canonical
owner `problem.toParametricSmoothMinimaxProblem t`, and
`toParametricSmoothMinimaxProblem_feasibleSet` identifies its feasible set with
`problem.ambientSet`. This file therefore adds no parallel unique-minimizer theorem shell.
-/

/- Proposition 2.24: for each `t`, the constrained max-type problem is the owner
`problem.toParametricSmoothMinimaxProblem t`, so existence and uniqueness of its feasible
minimizer are given directly by the canonical owner theorem
`SmoothMinimaxProblem.existsUnique_isMinOn`. -/
recall SmoothMinimaxProblem.existsUnique_isMinOn

set_option linter.hashCommand false in
#check (problem.toParametricSmoothMinimaxProblem t).existsUnique_isMinOn

end
