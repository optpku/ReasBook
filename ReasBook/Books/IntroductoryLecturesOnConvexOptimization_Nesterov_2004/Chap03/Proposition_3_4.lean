/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_1_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.4 lies in the chapter's closed-convex `WithTop`-valued convex-analysis domain.

Primary domain:
- continuous convex real-valued functions viewed through the owner predicate
  `ClosedConvexFunction`.

Sampled owner-style declarations:
- `closedConvexFunction_coe_of_convexOn_continuous` in `Proposition_3_1_1_3`, the existing
  chapter theorem with the same mathematical content at the intrinsic real topological-module
  level;
- `ClosedConvexFunction` and `ClosedConvexOn` in `Definition_3_1_1_5`, the source-facing owners
  for closed convex extended-real-valued functions;
- mathlib `ConvexOn.convex_epigraph`;
- mathlib `IsClosed.epigraph`.

Best owner abstraction:
- `closedConvexFunction_coe_of_convexOn_continuous`.

Primitive data:
- a real-valued function `f`;
- its convexity on `Set.univ`;
- its continuity.

Derived API:
- the closed-convex owner statement for the `WithTop ℝ` coercion of `f`.

Source/core/bridge triage:
- source-facing: Proposition 3.4 as the Euclidean `ℝⁿ` statement;
- core/canonical: `ClosedConvexFunction` together with `ConvexOn` and closed epigraphs;
- bridge/view: the already-proved intrinsic theorem
  `closedConvexFunction_coe_of_convexOn_continuous`.

This file is therefore recall-only. Keeping a second Euclidean theorem shell here would duplicate
an existing owner-level declaration instead of reusing the chapter's canonical abstraction. -/

recall closedConvexFunction_coe_of_convexOn_continuous
