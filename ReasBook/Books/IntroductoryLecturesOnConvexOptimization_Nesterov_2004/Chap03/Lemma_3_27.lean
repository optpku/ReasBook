/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.27 lies in the chapter's Euclidean strong-convexity and one-sided directional-
derivative domain.

Sampled owner-style declarations:
- mathlib `StrongConvexOn`
- mathlib `ConvexOn.rightDeriv_le_slope_of_mem_interior`
- chapter `HasDirectionalDerivAt` in `Definition_3_1_3_1`
- chapter `StrongConvexOn.lower_tangent_derivWithin_of_mem_interior` in `Lemma_3_2_3`

Best owner abstraction:
- `StrongConvexOn.lower_tangent_derivWithin_of_mem_interior`

Primitive data:
- a feasible set `Q`, a modulus `μ`, an objective `f`, and points `x`, `y`
- the owner hypothesis `StrongConvexOn Q μ f`
- the membership assumptions `x ∈ interior Q` and `y ∈ Q`

Derived API:
- the one-sided directional-derivative term, canonically expressed by
  `derivWithin (fun t : ℝ ↦ f (x + t • (y - x))) (Set.Ici 0) 0`
- any later namespace-style or item-style reuse of the same lower-support estimate

Source/core/bridge triage:
- source-facing/core:
  `StrongConvexOn.lower_tangent_derivWithin_of_mem_interior`
- bridge/view:
  this file's former alias `rightDirectionalDeriv` and its renamed shell theorem

The earlier chapter file already owns the source statement exactly, so this file now recalls that
owner theorem directly instead of reintroducing a parallel derivative alias and duplicate wrapper
API.
-/

/- Lemma 3.27 is the direct owner recall of the quadratic lower-support estimate already
formalized in `Lemma_3_2_3`. -/
recall StrongConvexOn.lower_tangent_derivWithin_of_mem_interior
