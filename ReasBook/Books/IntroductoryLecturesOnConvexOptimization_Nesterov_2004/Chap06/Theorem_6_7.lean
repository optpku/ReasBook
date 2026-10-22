/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Theorem_6_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 6.7 is a recall-only item in the Chapter 6 excessive-gap / adjoint-gradient update
domain.

Primary mathematical domain:
- odd-step preservation of the `μ₁ = 0` excessive-gap condition under the strongly convex dual
  update.

Sampled owner-style declarations:
- `StronglyConvexDualUpdate.excessive_gap_condition_preserved` in `Chap06/Theorem_6_2_3`, the
  chapter owner theorem for odd-step preservation;
- `StronglyConvexDualUpdate.updatedPrimalPoint` in `Chap06/Theorem_6_2_3`, the canonical owner of
  the updated primal iterate;
- `StronglyConvexDualUpdate.updatedDualPoint` in `Chap06/Theorem_6_2_3`, the canonical owner of
  the updated dual iterate;
- `IsAdjointGradientMappingOn` in `Chap06/Definition_6_39`, the source-facing owner hypothesis for
  the dual update map.

Best owner abstraction:
- source-facing: Theorem 6.7's odd-step preservation statement;
- core/canonical: `StronglyConvexDualUpdate.excessive_gap_condition_preserved`;
- bridge/view: none. The previous local theorem duplicated the owner interface exactly, so this
  numbered item should be recall-only rather than a second public theorem shell.

Primitive data:
- the feasible sets `Q₁`, `Q₂` and their convexity;
- the smoothed primal objective `fμ`, the dual objective `φ`, and the update maps `x₀`, `uμ`,
  `V`;
- the current feasible pair `(xBar, uBar)` and the step-size data.

Derived API:
- the reduced smoothing parameter `μ₂⁺ = (1 - τ) μ₂`;
- the updated primal-dual pair from `StronglyConvexDualUpdate`;
- the preserved `μ₁ = 0` excessive-gap certificate.

This file keeps no parallel local theorem. The earlier declaration had the same binders,
hypotheses, and conclusion as the chapter owner theorem and only forwarded to it, so the correct
refinement is direct canonical recall/use. -/

/- Theorem 6.7 recalls the chapter owner theorem for odd-step preservation of the `μ₁ = 0`
excessive-gap condition. -/
recall StronglyConvexDualUpdate.excessive_gap_condition_preserved
