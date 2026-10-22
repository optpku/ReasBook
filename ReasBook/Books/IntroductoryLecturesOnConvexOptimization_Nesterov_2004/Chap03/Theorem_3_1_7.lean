/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_2_3

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.1.7 is a recall-only surface in the chapter's constrained partial-infimum /
extended-real convex-analysis domain.

Primary mathematical domain:
- constrained fiberwise infima of real-valued convex functions, viewed through the chapter's
  `EReal` finite-value bridge.

Relevant owner-style declarations sampled before refinement:
- `partialInfProjection` in `Theorem_3_1_2_3`, the source-facing owner for constrained fiberwise
  infima;
- `extendedRealRealPart` in `Definition_3_1_1_3`, the chapter bridge from `EReal` values to their
  real part on the finite-value domain;
- `partialInfProjection_convexOn` in `Theorem_3_1_2_3`, the canonical convexity theorem for that
  owner surface;
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the later `WithTop` analogue
  that reuses the same owner abstraction.

Best owner abstraction:
- `partialInfProjection_convexOn`.

Primitive data:
- none in this file; the owner object and its convexity theorem already live upstream.

Derived API:
- this recall-only numbered entry point.

Source/core/bridge triage:
- source-facing: Theorem 3.1.7's statement that the constrained partial infimum of a real-valued
  convex function is convex;
- core/canonical: `partialInfProjection_convexOn` on the chapter owner `partialInfProjection`;
- bridge/view: the chapter `EReal` convexity surface
  `ConvexOn ℝ (dom ψ) (extendedRealRealPart ψ)`.

The previous file introduced a second theorem name with exactly the same statement as
`partialInfProjection_convexOn`. Since the upstream theorem already lives on the correct owner
abstraction and is reused elsewhere in the chapter, this file now recalls that canonical theorem
directly instead of maintaining a duplicate wrapper.
-/

recall partialInfProjection_convexOn
