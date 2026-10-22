/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_1_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.5 is a source-facing recall in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions and their real sublevel sets.

Sampled owner-style declarations:
- `ClosedConvexOn`
- `ClosedConvexFunction`
- `ClosedConvexFunction.isClosed_convex_sublevelSet`

Best owner abstraction:
- `ClosedConvexFunction`

Primitive data:
- the effective-domain closed-convex owner hypothesis `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.isClosed_convex_sublevelSet`

Source/core/bridge triage:
- source-facing: Theorem 3.5, the sublevel-set consequence of closed convexity
- core/canonical: `ClosedConvexFunction`
- bridge/view: `ClosedConvexOn` and the constrained-epigraph API behind it

This file therefore reuses the canonical owner theorem directly, without introducing a second
sublevel-set wrapper or theorem-shaped alias. -/

recall ClosedConvexFunction.isClosed_convex_sublevelSet
