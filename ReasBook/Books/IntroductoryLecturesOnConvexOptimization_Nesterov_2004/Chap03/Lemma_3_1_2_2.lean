/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.2.2 is a source-facing recall in the chapter's univariate closed-convex continuity
domain.

Primary domain:
- relative continuity of univariate closed convex `WithTop ℝ`-valued functions on their effective
  domain.

Sampled owner-style declarations:
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`
- mathlib `ConvexOn.continuousOn`
- mathlib `ConvexOn.continuousOn_interior`

Best owner abstraction:
- the chapter owner `ClosedConvexFunction`, together with its exact univariate continuity theorem
  `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Primitive data:
- the effective domain `dom f`
- the constrained-epigraph data packaged by `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Source/core/bridge triage:
- source-facing: the one-dimensional continuity consequence stated in this lemma
- core/canonical: `ClosedConvexFunction`
- bridge/view: `dom f`, `withTopRealPart f`, and the ambient `ConvexOn` continuity lemmas sampled
  for domain style

The previous file kept a second public theorem
`ClosedConvexFunction.continuousOn_effectiveDomain_univariate` with the exact same interface as
the upstream owner theorem. That shell carried no new mathematics, so this file now recalls the
canonical chapter theorem directly instead of maintaining a parallel local copy. -/

recall ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional
