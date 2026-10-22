/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_15

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.4.1 is a recall-only file in the chapter's affine-nesterovHyperplane strong-separation
domain.

Relevant sampled declarations:
- `AffineHyperplane` in `Definition_3_1_4_1`, the owner of a nonzero normal vector and offset
- `AreStronglySeparable` in `Definition_3_12`, the set-level owner predicate
- `areStronglySeparable_of_disjoint_closed_convex_of_bounded_one_side` in `Theorem_3_1_13`, the
  chapter owner theorem with the natural argument order
- `areStronglySeparable_of_disjoint_closed_convex_of_one_bounded` in `Theorem_3_15`, the exact
  source-facing theorem surface already present upstream

Best owner abstraction:
- `AreStronglySeparable`

Primitive data:
- the sets `Q₁`, `Q₂`
- nonemptiness, closedness, convexity, disjointness, and one-sided boundedness

Derived API:
- the existing chapter theorem
  `areStronglySeparable_of_disjoint_closed_convex_of_one_bounded`

Source/core/bridge triage:
- source-facing: this numbered theorem item
- core/canonical: `AreStronglySeparable`
- bridge/view: this recall-only file, which now reuses the exact upstream theorem surface instead
  of keeping a second renamed declaration

The previous version duplicated the exact theorem interface already provided by `Theorem_3_15`
under a longer local name. This file now recalls that existing theorem directly, keeping the
source semantics unchanged while removing the parallel wrapper API.
-/

/- Theorem 3.1.4.1 is the direct chapter recall of the existing strong-separation theorem with the
same interface. -/
recall areStronglySeparable_of_disjoint_closed_convex_of_one_bounded
