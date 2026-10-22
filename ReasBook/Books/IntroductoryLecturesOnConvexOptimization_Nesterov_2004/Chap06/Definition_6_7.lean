/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_30
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_31

/- Definition 6.7 lies in the chapter's prox-function smoothing domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter's canonical owner
  of the regularized maximization formula, specialized here to zero smooth part;
- `smoothedPrimalObjectiveArgmax` in `Definition_6_30`, the chapter's
  canonical owner for the associated maximizer layer `u_μ(x)`;
- `NesterovIsProxFunction` in `Definition_6_31`, the chapter's canonical owner for the
  prox-function hypothesis on `d₂`;
- `NesterovIsProxCenter` in `Definition_6_31`, the chapter's canonical owner for the
  normalized prox-center condition.

Best owner abstraction:
- source-facing: the prox-smoothed approximation `f_μ` together with its
  associated maximizer layer `u_μ(x)`;
- core/canonical: `smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ` and
  `smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ`;
- bridge/view: the prox-regularizer assumptions `NesterovIsProxFunction p Q₂ d₂` and
  `NesterovIsProxCenter Q₂ d₂ u₀`, together with the membership specification
  `u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x ↔
    u ∈ Q₂ ∧ IsMaxOn (smoothedPrimalObjectiveMaximand A hatφ d₂ μ x) Q₂ u`.

Primitive data:
- the feasible dual set `Q₂`, the dual penalty `hatφ`, the prox-function `d₂`,
  the smoothing parameter `μ`, and the linear map `A`;
- the prox-function and prox-center hypotheses, already owned by
  `NesterovIsProxFunction` and `NesterovIsProxCenter`.

Derived API:
- the smoothed objective itself, via `smoothedPrimalObjective` with zero smooth
  part;
- the canonical argmax set for the textbook point `u_μ(x)`, via
  `smoothedPrimalObjectiveArgmax`;
- its pointwise supremum formula, via `smoothedPrimalObjective_apply`;
- the pointwise maximizer specification, via
  `mem_smoothedPrimalObjectiveArgmax_iff`.

Source/core/bridge triage:
- source-facing: Definition 6.7's prox-smoothed objective `f_μ` and the
  associated maximizer layer `u_μ(x)`;
- core/canonical: `smoothedPrimalObjective`, `smoothedPrimalObjectiveArgmax`,
  `NesterovIsProxFunction`, and `NesterovIsProxCenter`;
- bridge/view: this numbered file, which only recalls those owners instead of
  packaging them into a second smoothing structure, together with the membership
  specification theorem that expands the argmax owner to feasible maximality.

The previous version introduced a parallel public owner `ProxFunctionSmoothing`
and exact wrapper API around `smoothedPrimalObjective` and `IsMaxOn`. Those notions
already have canonical owners upstream in the chapter, so this file now keeps
only the direct recall surface for the objective, its argmax owner, and the
prox hypotheses.
-/

universe u v

section

variable {E₁ : Type u} {E₂ : Type v}
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
variable (p : Seminorm ℝ E₂) [Seminorm.IsNorm p]

variable
  (A : E₁ →L[ℝ] StrongDual ℝ E₂)
  (Q₂ : Set E₂) (hatφ d₂ : E₂ → ℝ) (μ : ℝ) (u₀ : E₂) (x : E₁) (u : E₂)

/- Definition 6.7: Nesterov's prox-smoothed approximation `f_μ` is the chapter's
canonical regularized-max owner `smoothedPrimalObjective` specialized to zero
smooth part. -/
recall smoothedPrimalObjective
recall smoothedPrimalObjective_apply

/- Definition 6.7 uses the chapter's canonical prox-function owner for `d₂` and
the canonical prox-center owner for the normalized center `u₀`. -/
recall NesterovIsProxFunction
recall NesterovIsProxCenter

/- Definition 6.7's textbook maximizer `u_μ(x)` is owned by the chapter's
canonical argmax-set declaration, and membership in that set expands to the
feasible-maximizer statement. -/
recall smoothedPrimalObjectiveArgmax
recall mem_smoothedPrimalObjectiveArgmax_iff

set_option linter.hashCommand false in
#check smoothedPrimalObjective A Q₂ 0 hatφ d₂ μ x

set_option linter.hashCommand false in
#check smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x

set_option linter.hashCommand false in
#check NesterovIsProxFunction p Q₂ d₂

set_option linter.hashCommand false in
#check NesterovIsProxCenter Q₂ d₂ u₀

set_option linter.hashCommand false in
#check u ∈ smoothedPrimalObjectiveArgmax A Q₂ hatφ d₂ μ x

set_option linter.hashCommand false in
#check mem_smoothedPrimalObjectiveArgmax_iff A Q₂ hatφ d₂ μ x u

end
