/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_1_3_1

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.1.3 belongs to the chapter's canonical one-sided directional-derivative API in
`Nesterov.Chap03.Definition_3_1_3_1`.

Primary domain:
- one-sided directional derivatives of extended-real-valued functions on real modules.

Relevant owner-style declarations sampled before refinement:
- `extendedRealEffectiveDomain`
- `HasDerivWithinAt`
- `HasDirectionalDerivAt`
- `DirectionallyDifferentiableAt`

Owner abstraction:
- `HasDirectionalDerivAt`

Primitive data:
- `extendedRealEffectiveDomain f`, the finite-value condition at the base point and along the ray.
- the scalar slice `fun α ↦ extendedRealRealPart f (x + α • p)`, organized canonically by the
  one-sided derivative owner `HasDerivWithinAt ... (Set.Ici 0) 0`.

Derived API:
- `HasDirectionalDerivAt` is the owner predicate for the one-sided directional derivative in every
  direction, including `p = 0` via the constant ray.
- `DirectionallyDifferentiableAt` is the existential wrapper around `HasDirectionalDerivAt`.
- `directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt` is the companion specification
  theorem.

Source/core/bridge triage:
- source-facing: `HasDirectionalDerivAt`, `DirectionallyDifferentiableAt`
- core/canonical: `HasDerivWithinAt` on the scalar slice
  `fun α ↦ extendedRealRealPart f (x + α • p)`
- bridge/view: the secant-slope presentation of that scalar slice

The support vocabulary is already owned upstream, so this file recalls only the source-facing
owner surface and its thin specification theorem. As in the owner file, the source prose is
Euclidean, but the declaration surface itself needs only the real-module structure used to form
the ray `x + α • p`. -/
recall HasDirectionalDerivAt

recall DirectionallyDifferentiableAt

recall directionallyDifferentiableAt_iff_exists_hasDirectionalDerivAt
