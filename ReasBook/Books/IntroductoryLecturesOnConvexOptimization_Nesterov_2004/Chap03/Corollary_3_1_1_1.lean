/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Corollary 3.1.1.1 lies in the convex-analysis domain of the finite convex-hull maximum principle.

Sampled owner-style declarations:
- `ConvexOn.map_sum_le`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`
- `convexOn_value_le_max_of_convex_combination`

Best owner abstraction:
- `ConvexOn.le_sup_of_mem_convexHull`

Primitive data:
- a finite set `t : Finset E`
- a convex function `hf : ConvexOn ℝ s f`
- the inclusion `(t : Set E) ⊆ s`
- a point `x` with `x ∈ convexHull ℝ (t : Set E)`

Derived API:
- the canonical bound `f x ≤ t.sup' ... f`

Source/core/bridge triage:
- source-facing: the corollary that the value at a convex combination is bounded by the maximum of
  the endpoint values
- core/canonical: `ConvexOn.le_sup_of_mem_convexHull`
- bridge/view: the chapter theorem
  `convexOn_value_le_max_of_convex_combination`, which uses the chapter owner
  `is_convex_combination_of`; the displayed equality `x = ∑ i, α i • points i` is kept only in the
  companion theorem `convexOn_value_le_max_of_convex_combination_of_coefficients`

The coefficient-level theorem is bridge API, not the owner of this item. This file therefore
recalls the canonical convex-hull maximum principle directly; when the source presentation names a
point by an equality `x = ∑ i, α i • points i`, that equality should be used only as a bridge to
`x ∈ convexHull ℝ (Set.range points)` at the call site or in a companion theorem.
-/

recall ConvexOn.le_sup_of_mem_convexHull
