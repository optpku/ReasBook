/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

/- Primary domain: strong convexity on convex subsets of `ℝⁿ` with respect to an explicit
norm-like seminorm.

Sampled owner-style declarations before refining this file:
* mathlib `UniformConvexOn.add`
* mathlib `ConvexOn.smul`
* project `StrongConvexOnWith` in `Definition_2_14`
* project `StrongConvexOnWith.nonneg_combo_inter` in `Definition_2_14`

Best owner abstraction:
* `StrongConvexOnWith p μ Q f`

Primitive data:
* the owner predicate `StrongConvexOnWith p μ Q f`

Derived API:
* `StrongConvexOnWith.nonneg_combo_inter`, which belongs with the rest of the owner API in
  `Definition_2_14`

Source/core/bridge triage:
* source-facing: the weighted-sum closure statement
* core/canonical: `StrongConvexOnWith.nonneg_combo_inter`
* bridge/view: later Euclidean specializations should reuse that owner theorem directly

This numbered item is therefore a direct owner recall, not a second declaration site.
-/

/- Lemma 2.6 is the direct owner recall of nonnegative weighted-sum closure for
`StrongConvexOnWith`. -/
recall StrongConvexOnWith.nonneg_combo_inter
