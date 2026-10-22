/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Definition_2_4

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 2.1 lies in the first-order convex-analysis function-class domain for the source-facing
class `𝓕¹(Q)`.

Sampled owner-style declarations:
- mathlib `ContDiffOn.const_smul`
- mathlib `ConvexOn.smul`
- mathlib `ConvexOn.add`
- Chapter 2 `ConvexC1On` in `Definition_2_4`

Best owner abstraction:
- `ConvexC1On`, the chapter owner for the source class `𝓕¹(Q)`.

Primitive data:
- the feasible set `Q`
- the objective functions `f₁`, `f₂`
- the owner hypotheses `ConvexC1On Q f₁` and `ConvexC1On Q f₂`

Derived API:
- owner closure under nonnegative scalar multiplication and addition
- the weighted-sum closure theorem `ConvexC1On.nonneg_combo`

Source/core/bridge triage:
- source-facing: the textbook closure of `𝓕¹(Q)` under nonnegative linear combinations
- core/canonical: `ConvexC1On.nonneg_combo`
- bridge/view: the notation `𝓕¹(Q)` as the set-level source presentation of the owner predicate

This numbered item is therefore a direct owner recall rather than a second declaration site.
-/

recall ConvexC1On.nonneg_combo
