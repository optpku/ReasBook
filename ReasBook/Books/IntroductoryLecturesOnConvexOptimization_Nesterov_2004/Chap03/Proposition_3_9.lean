/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_1_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 3.9 is recall-only in the chapter's weighted pointwise-supremum API.

Primary domain:
- weighted pointwise suprema of `WithTop ℝ`-valued functions on a real topological module.

Sampled owner-style declarations:
- `pointwiseSupremumOn`
- `ClosedConvexOn.pointwise_sSup`
- `ClosedConvexOn.nonneg_smul`
- `ClosedConvexOn.add_inter`

Best owner abstraction:
- the source-facing bridge theorem already owned by
  `closedConvexFunction_pointwiseSupremumOn_nonneg_weighted` in
  `Proposition_3_1_2_1`

Primitive data:
- a weight set `Δ : Set (ι → ℝ)`
- a family `f : ι → X → WithTop ℝ`
- nonemptiness of `Δ`
- coordinatewise nonnegativity of the weights in `Δ`
- closed-convexity of each component `f i`

Derived API:
- the recalled weighted pointwise-supremum closed-convexity theorem

This later file no longer redeclares the same bridge theorem under a second owner file. It reuses
the earlier source-facing proposition directly. -/

/- Proposition 3.9 reuses the source-facing weighted pointwise-supremum bridge theorem already
established in Proposition 3.1.2.1. -/
recall closedConvexFunction_pointwiseSupremumOn_nonneg_weighted

end
