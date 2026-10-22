/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30

/- Definition 6.25 lies in the Chapter 6 smoothed dual-oracle / maximizer domain.

Mandatory domain-style sampling before refinement:
- `smoothedPrimalObjectiveMaximand` in `Definition_6_30`, the chapter owner of
  the regularized dual maximand `u ↦ ⟪A x, u⟫ - \hat φ(u) - μ d₂(u)`;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter owner of
  the corresponding oracle argmax set;
- `mem_smoothedPrimalObjectiveArgmax_iff` in `Definition_6_30`, the companion
  bridge expanding argmax membership to feasible maximality;
- mathlib `IsMaxOn`, the canonical extremum owner on a feasible set.

Best owner abstraction:
- source-facing: the oracle subproblem for the smoothed function at the fixed
  iterate `y_k`, consisting of the regularized dual maximand and its maximizer
  set on `Q₂`;
- core/canonical: `smoothedPrimalObjectiveMaximand A hatφ d₂ μ yk` and
  `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ yk`;
- bridge/view: `mem_smoothedPrimalObjectiveArgmax_iff`, which restates oracle
  membership as feasibility together with the textbook maximality predicate.

Primitive data:
- the linear map `A`, iterate `y_k`, smoothing parameter `μ`, feasible set
  `Q₂`, dual penalty `hatφ`, and prox-function `d₂`.

Derived API:
- the pointwise maximand formula from
  `smoothedPrimalObjectiveMaximand`;
- the oracle argmax set from `smoothedPrimalObjectiveArgmax`;
- the membership specification theorem
  `mem_smoothedPrimalObjectiveArgmax_iff`.

Source/core/bridge triage:
- source-facing: Definition 6.25's oracle subproblem at the fixed iterate
  `y_k`;
- core/canonical: `smoothedPrimalObjectiveMaximand`,
  `smoothedPrimalObjectiveArgmax`, and `IsMaxOn`;
- bridge/view: this numbered file, which is recall-only because the exact
  oracle owners already exist upstream in `Definition_6_30`.

The previous version introduced the duplicate public wrappers
`smoothedFunctionOracleMaximand` and `smoothedFunctionOracleComputation`. Those
were exact-interface restatements of the Chapter 6 owners specialized at
`x = y_k`, so this file now keeps only the direct recall surface.
-/

noncomputable section

universe u v

section

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]

variable
  (A : E₁ →L[ℝ] StrongDual ℝ E₂)
  (yk : E₁) (μ : NNReal) (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (u : E₂)

/- Definition 6.25's oracle subproblem is the Chapter 6 regularized dual
maximand at the fixed iterate `y_k` together with its canonical argmax owner on
`Q₂`. -/
recall smoothedPrimalObjectiveMaximand
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff

set_option linter.hashCommand false in
#check smoothedPrimalObjectiveMaximand A hatφ d₂ (μ : ℝ) yk u

set_option linter.hashCommand false in
#check smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ (μ : ℝ) yk

set_option linter.hashCommand false in
#check u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ (μ : ℝ) yk

set_option linter.hashCommand false in
#check mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ (μ : ℝ) yk u

end
