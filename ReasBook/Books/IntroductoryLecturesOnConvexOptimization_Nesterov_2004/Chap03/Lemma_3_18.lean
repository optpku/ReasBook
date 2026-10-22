/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_18

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 3.18 is a source-facing recall in the chapter's tangent-cone domain.

Primary domain:
- tangent cones of convex subsets of real normed spaces.

Relevant owner-style declarations sampled before refinement:
- mathlib `posTangentConeAt`, the ambient positive tangent-cone owner;
- mathlib `mem_posTangentConeAt_of_segment_subset`, the canonical segment-based entry lemma for
  feasible displacements;
- mathlib `PointedCone.hull`, the canonical cone-hull owner for feasible directions;
- mathlib `tangentConeAt NNReal`, the underlying owner behind `posTangentConeAt`;
- mathlib `Set.vsub_singleton`, the canonical displacement-set view.

Best owner abstraction:
- `posTangentConeAt Q xBar`
- `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`

Primitive data:
- the feasible set `Q`;
- the base point `xBar`.

Derived API:
- `Q -ᵥ ({xBar} : Set E)`;
- `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`;
- the owner-shaped closure characterization
  `posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton`.

Source/core/bridge triage:
- source-facing: the textbook boundary-point statement that the tangent cone is the closure of the
  conical hull of feasible displacements;
- core/canonical: mathlib's `posTangentConeAt Q xBar`;
- core/canonical: mathlib's `PointedCone.hull ℝ (Q -ᵥ ({xBar} : Set E))`;
- bridge/view: the direct displacement expression `Q -ᵥ ({xBar} : Set E)`.

The exact source-facing theorem is already owned upstream by `Lemma_3_1_18.lean`, exported in the
atomic owner-shaped equality form with hypotheses `Convex ℝ Q` and `xBar ∈ Q`; it is stated for
the positive tangent cone `posTangentConeAt`, whose underlying mathlib owner is
`tangentConeAt NNReal`. The textbook closed boundary-point case is a direct specialization. This
file therefore recalls the upstream owner theorem directly instead of staging local binders only to
`#check` an applied term, and it maintains no parallel `displacementSet`/`conicalHull` wrappers or
`bouligandTangentCone` layer.
-/

recall posTangentConeAt_eq_closure_pointedConeHull_vsub_singleton
