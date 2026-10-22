/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/-
Corollary 3.1.1.2 lies in the convex-analysis domain of the finite convex-hull maximum principle.

Sampled owner-style declarations:
- `ConvexOn.exists_ge_of_mem_convexHull`
- `ConvexOn.le_sup_of_mem_convexHull`
- `ConvexOn.inf_le_of_mem_convexHull`

Best owner abstraction:
- `ConvexOn.exists_ge_of_mem_convexHull`

Primitive data:
- a vertex set `t : Set E`, or equivalently a finite vertex family viewed through `Set.range`
- a set `s` and a convex function `hf : ConvexOn ℝ s f`
- the inclusion `t ⊆ s`
- a point `x ∈ convexHull ℝ t`

Derived API:
- a vertex `y ∈ t` with `f x ≤ f y`

Source/core/bridge triage:
- source-facing: the corollary that the maximum of a convex function on a finite convex hull is
  attained at a vertex
- core/canonical: `ConvexOn.exists_ge_of_mem_convexHull`
- bridge/view: the finite-sup theorem `ConvexOn.le_sup_of_mem_convexHull` and coefficient or
  index-level attainment formulations derived from the owner theorem

The chapter theorem `convexOn_value_le_max_of_convex_combination` is a bridge/view reformulation;
this file keeps only the canonical witness-level convex-hull maximum-principle recall.
-/

recall ConvexOn.exists_ge_of_mem_convexHull
