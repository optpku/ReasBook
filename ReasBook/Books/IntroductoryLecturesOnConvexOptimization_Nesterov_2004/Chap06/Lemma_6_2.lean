/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_1

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 6.2 lies in the chapter's prox-function smoothing / first-order smoothness domain.

Sampled owner-style declarations:
- `smoothedPrimalObjective` in `Definition_6_30`, the chapter's canonical regularized-max
  smoothing owner, specialized in `Theorem_6_1` to zero smooth part;
- `ContinuousLinearMap.flip` in `Proposition_6_3`, the chapter's canonical transpose owner for
  `A : E₁ →L[ℝ] StrongDual ℝ E₂`;
- `nesterovSmoothedObjective_hasFDerivAt` in `Theorem_6_1`, the canonical derivative identification for
  the smoothed objective;
- `smoothedObjective_gradient_lipschitz` in `Theorem_6_1`, the chapter's canonical Lipschitz
  smoothness theorem for the derivative selection.

Best owner abstraction:
- source-facing: the prox-smoothed objective `f_μ` defined by regularized maximization over the
  feasible dual set;
- core/canonical: `smoothedPrimalObjective A Q 0 phiHat d2 μ` together with `A.flip`,
  `nesterovSmoothedObjective_hasFDerivAt` and `smoothedObjective_gradient_lipschitz`;
- bridge/view: this numbered lemma file, which should only recall the upstream owner theorem
  pair instead of introducing a second smoothing construction.

Primitive data:
- the linear map `A`;
- the feasible set `Q`, dual penalty `phiHat`, prox-function `d2`, and smoothing parameter `μ`;
- the maximizer selection `uMu`;
- the positivity, closed-convex, differentiability, and strong-convexity hypotheses already
  required by `Theorem_6_1`.

Derived API:
- the canonical transpose field `x ↦ A.flip (uMu x)`;
- the derivative identification `nesterovSmoothedObjective_hasFDerivAt`;
- the Lipschitz smoothness theorem `smoothedObjective_gradient_lipschitz`.

Source/core/bridge triage:
- source-facing: Lemma 6.2's smoothness statement for the prox-smoothed objective;
- core/canonical: `A.flip`, `nesterovSmoothedObjective_hasFDerivAt`, and
  `smoothedObjective_gradient_lipschitz`;
- bridge/view: this recall-only numbered surface.

The previous version introduced an averaging-based Euclidean-ball smoothing operator. That was a
different construction from the chapter's structured prox-smoothing objective and duplicated the
existing owner theorem. This file now reuses the chapter owner directly, recalling both the
derivative identification for `f_μ` and the Lipschitz estimate for the canonical field
`x ↦ A.flip (uMu x)`.
-/

recall nesterovSmoothedObjective_hasFDerivAt
recall smoothedObjective_gradient_lipschitz
