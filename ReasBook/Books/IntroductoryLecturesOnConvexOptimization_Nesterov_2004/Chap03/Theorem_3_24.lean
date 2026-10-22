/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_19

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.24 lies in the chapter's common-subdifferential / convex-analysis domain.

Mandatory domain-style sampling before refinement:
- `constrainedSubdifferential` in `Definition_3_1_5`, the earlier source-facing owner for
  subgradients on a set;
- `commonRegularSubdifferential` and `mem_commonRegularSubdifferential_iff` in
  `Definition_3_1_5_4`, the common owner abstraction already used elsewhere in the chapter;
- `eq_add_inner_of_mem_commonRegularSubdifferential` in `Theorem_3_1_19`;
- `map_segment_eq_of_commonRegularSubdifferential_nonempty` in `Theorem_3_1_19`.

Best owner abstraction:
- `commonRegularSubdifferential`.

Primitive data:
- a set `X`;
- a real-valued convex function `f`;
- membership of a vector in the common regular subdifferential on `X`.

Derived API:
- the affine increment identity on `X`;
- the affine-on-segments consequence when the common regular subdifferential is nonempty.

Source/core/bridge triage:
- source-facing: the two textbook consequences recorded in this numbered item;
- core/canonical: `commonRegularSubdifferential`;
- bridge/view: this recall-only numbered surface.

The previous file duplicated a weaker Euclidean-local owner layer
`IsSubgradientOnAt` / `subdifferentialOn` / `commonSubdifferential` and restated both theorems
with redundant hypotheses. Since the chapter already has the intrinsic owner
`commonRegularSubdifferential` and the exact source-facing theorems upstream on the minimal
owner-layer hypotheses, this file now reuses those declarations directly instead of keeping a
parallel local API. -/

/- Theorem 3.24 (1): every common subgradient gives the affine increment formula on `X`. -/
recall eq_add_inner_of_mem_commonRegularSubdifferential

/- Theorem 3.24 (2): if the common regular subdifferential is nonempty, then the function is
affine on every segment contained in `X`. -/
recall map_segment_eq_of_commonRegularSubdifferential_nonempty
