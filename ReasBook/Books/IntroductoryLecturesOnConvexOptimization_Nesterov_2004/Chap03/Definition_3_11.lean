/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_3

-- Declarations for this item will be appended below by the statement pipeline.

/-
Definition 3.11 is a source-facing recall in the chapter's one-sided directional-derivative
domain.

Primary mathematical domain:
- one-sided directional derivatives of `EReal`-valued functions on real modules.

Sampled owner-style declarations:
- `HasDerivWithinAt`
- `HasDirectionalDerivAt`
- `DirectionallyDifferentiableAt`
- `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

Best owner abstraction:
- `HasDirectionalDerivAt`

Primitive data:
- none in this file; the owner predicate lives upstream in `Definition_3_1_3_1`, and the earlier
  chapter recall surface already lives in `Definition_3_1_3`.

Derived API:
- the source-facing owner predicate `HasDirectionalDerivAt`
- its existential wrapper `DirectionallyDifferentiableAt`
- the thin specification theorem `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

Source/core/bridge triage:
- source-facing: `HasDirectionalDerivAt`, `DirectionallyDifferentiableAt`
- core/canonical: the earlier chapter recall `Definition_3_1_3`, backed by `HasDerivWithinAt` on
  the scalar slice
- bridge/view: `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt`

Definition 3.11 adds no new mathematical data beyond the earlier chapter recall surface in
`Definition_3_1_3`. This file therefore reuses that surface directly instead of restating the full
signatures a second time.
-/

recall HasDirectionalDerivAt

recall DirectionallyDifferentiableAt

recall directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt
