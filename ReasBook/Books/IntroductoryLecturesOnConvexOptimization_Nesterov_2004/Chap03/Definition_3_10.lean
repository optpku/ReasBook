/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.10 lies in the chapter's convex-analysis/minimax-linearization domain.

Sampled owner-style declarations:
- mathlib `unitInterval`
- mathlib `AffineMap.lineMap`
- `IsMinimaxLinearizationParameter`
- `isMinimaxLinearizationParameter_iff`

Best owner abstraction:
- the upstream source-facing owner `IsMinimaxLinearizationParameter`

Primitive data:
- a domain `Q`
- two functions `f₁ f₂ : Q → ℝ`
- a parameter `lam : unitInterval`

Derived API:
- the companion specification theorem `isMinimaxLinearizationParameter_iff`

Source/core/bridge triage:
- source-facing: the textbook notion of a minimax linearization parameter
- core/canonical: the earlier owner predicate `IsMinimaxLinearizationParameter` from
  `Definition_3_1_2_3`
- bridge/view: the displayed `EReal`-infimum equality recalled by
  `isMinimaxLinearizationParameter_iff`

Definition 3.10 adds no new mathematical data beyond that owner predicate, so this file recalls
the owner declarations directly instead of keeping a parallel local wrapper. -/

recall IsMinimaxLinearizationParameter

recall isMinimaxLinearizationParameter_iff
