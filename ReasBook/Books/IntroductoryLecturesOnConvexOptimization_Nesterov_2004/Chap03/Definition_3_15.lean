/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_5_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.15 is a bridge/view item in the chapter's convex-analysis normal-cone API.

Primary domain:
- convex analysis of extended-real-valued functions on Euclidean space.

Relevant owner-style declarations sampled before refinement:
- `extendedRealEffectiveDomain`
- the source-facing sublevel set `{x ∈ dom f | f x ≤ f x0}`
- `normalCone`
- `level_set_inequality_at_iff`

Best owner abstraction:
- `normalCone`

Primitive data:
- the finite-value domain `extendedRealEffectiveDomain f`
- the level set `{x ∈ dom f | f x ≤ f x0}`

Derived API:
- the bridge theorem `level_set_inequality_at_iff`

Source/core/bridge triage:
- source-facing: the textbook level-set inequality at `x0`
- core/canonical: `normalCone`
- bridge/view: `level_set_inequality_at_iff`

The normal-cone and sublevel-set vocabulary is already owned upstream, so this file recalls only
the numbered bridge statement rather than re-recalling that upstream surface. -/

recall level_set_inequality_at_iff
