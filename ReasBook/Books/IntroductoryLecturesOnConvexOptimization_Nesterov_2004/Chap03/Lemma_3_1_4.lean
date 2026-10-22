/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_4

-- Declarations for this item will be appended below by the statement pipeline.

open scoped WithTopConvexAnalysis

/- Lemma 3.1.4 is a source-facing recall in the chapter's univariate closed-convex continuity
domain.

Primary domain:
- relative continuity of univariate closed convex `WithTop ℝ`-valued functions on their effective
  domain.

Sampled owner-style declarations:
- `dom f`, `withTopRealPart` from `Definition_3_3`
- `ClosedConvexFunction` from `Definition_3_1_1_5`
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional` from `Lemma_3_4`
- mathlib `continuousWithinAt_iff_continuousAt_restrict`

Best owner abstraction:
- `ClosedConvexFunction f`, with `dom f` and `withTopRealPart f` as the canonical derived
  domain/view data.

Primitive data:
- the effective domain `dom f`
- the finite-value representative `withTopRealPart f`
- the owner hypothesis `ClosedConvexFunction f`

Derived API:
- `ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional`

Source/core/bridge triage:
- source-facing: continuity of the finite-value representative on the effective domain
- core/canonical: `ClosedConvexFunction`
- bridge/view: the restriction-based continuity formalization on the effective-domain subtype

This file therefore recalls the upstream owner theorem directly instead of maintaining a second
proof of the same continuity statement.
-/

recall ClosedConvexFunction.continuousOn_effectiveDomain_one_dimensional
    {f : ℝ → WithTop ℝ} (hf : ClosedConvexFunction f) :
    ContinuousOn (withTopRealPart f) (dom f)
