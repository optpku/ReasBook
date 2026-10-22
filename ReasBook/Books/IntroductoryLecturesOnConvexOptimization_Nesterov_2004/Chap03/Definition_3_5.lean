/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_1_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.5 is a source-facing recall in the chapter's closed-convex-function domain.

Primary domain:
- closed convex `WithTop ℝ`-valued functions on real modules, specializing to the textbook
  Euclidean setting.

Sampled owner-style declarations:
- `constrainedEpigraph`
- `ConvexOn`
- `ClosedConvexOn`
- `ClosedConvexFunction`

Best owner abstraction:
- the source-facing owner predicate `ClosedConvexOn Q f`, with `ClosedConvexFunction f` as the
  exact owner-derived special case `ClosedConvexOn (dom f) f`.

Primitive data:
- `dom f`
- `constrainedEpigraph Q f`

Derived API:
- `ClosedConvexFunction`
- `ClosedConvexOn.subset_withTopEffectiveDomain`, projecting the owner field `Q ⊆ dom f`
- `ClosedConvexOn.isClosed_constrainedEpigraph`
- `ClosedConvexOn.convex_constrainedEpigraph`
- `ClosedConvexOn.convexOn_withTopRealPart`

Source/core/bridge triage:
- source-facing: `ClosedConvexOn`, `ClosedConvexFunction`
- core/canonical: `dom f`, `constrainedEpigraph`, `ConvexOn`
- bridge/view: the projection lemmas out of `ClosedConvexOn` and the textbook specialization
  `X = EuclideanSpace ℝ (Fin n)`

This file therefore recalls the upstream owner declarations directly and introduces no parallel
chapter-local reformulation of closed convexity. -/

recall ClosedConvexOn

recall ClosedConvexFunction
