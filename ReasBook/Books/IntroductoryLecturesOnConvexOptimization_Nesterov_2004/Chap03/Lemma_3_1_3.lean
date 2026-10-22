/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.1.3 lies in the chapter's support-function domain.

Primary domain:
- support functions of subsets of a real inner-product space and their behavior under convex hulls
  of two-set unions.

Sampled owner-style declarations:
- `supportFunction` from `Definition_3_9`
- `supportFunction_apply`
- `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`
- the recall-only downstream use in `Lemma_3_1_2_1`

Best owner abstraction:
- the exact upstream theorem `supportFunction_convexHull_union_eq_max` from `Lemma_3_3`, stated at
  the same ambient owner level as `supportFunction`

Primitive data:
- two sets `Q₁ Q₂ : Set E`
- a direction `x : E`

Derived API:
- the support function of `convexHull ℝ (Q₁ ∪ Q₂)`
- its identification with the pointwise maximum of the two support functions

Source/core/bridge triage:
- source-facing: this two-set convex-hull support-function identity
- core/canonical: the exact upstream theorem `supportFunction_convexHull_union_eq_max`
- bridge/view: none needed; the target interface already exists upstream

This file previously repeated the exact theorem already owned by `Lemma_3_3`. Since the chapter
already has the precise owner interface, this numbered item is refined to direct canonical
recall/use instead of keeping a parallel local theorem shell. The textbook `ℝⁿ` statement is a
specialization of that generalized owner theorem.
-/
recall supportFunction_convexHull_union_eq_max
