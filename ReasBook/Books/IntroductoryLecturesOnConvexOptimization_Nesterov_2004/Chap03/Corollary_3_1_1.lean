/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Corollary 3.1.1 is a source-facing recall in the convex-analysis maximum-principle domain.

Primary domain:
- convex functions and the finite convex-hull maximum principle

Sampled owner-style declarations:
- `ConvexOn.map_sum_le`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`
- `convexOn_value_le_max_of_convex_combination`

Best owner abstraction:
- `ConvexOn.le_sup_of_mem_convexHull`

Primitive data:
- a finite vertex set `t : Finset E`
- a convex function `hf : ConvexOn ℝ s f`
- the inclusion `(t : Set E) ⊆ s`
- a point `x` with `x ∈ convexHull ℝ (t : Set E)`

Derived API:
- the canonical bound `f x ≤ t.sup' ... f`

Source/core/bridge triage:
- source-facing: the textbook corollary for finitely many points `x₁, …, xₘ`
- core/canonical: `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: the earlier chapter theorem
  `convexOn_value_le_max_of_convex_combination`, which packages the convex-combination input in the
  chapter owner `is_convex_combination_of`; the textbook coefficient display is kept only in the
  companion theorem `convexOn_value_le_max_of_convex_combination_of_coefficients`

The coefficient-based chapter statement is bridge API, while this corollary is governed directly by
the convex-hull owner theorem. This file therefore recalls the canonical owner declaration instead
of keeping a specialized local shell. -/

recall ConvexOn.le_sup_of_mem_convexHull
