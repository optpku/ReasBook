/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_1_25

-- Declarations for this item will be appended below by the statement pipeline.

/- Theorem 3.31 is recall-only in the chapter's partial-infimal-projection /
subdifferential-transfer domain.

Primary domain:
- partial infimal projection and subdifferential transfer for convex extended-real objectives.

Sampled owner-style declarations:
- `partialInfProjection_convexOn_of_convexWithTop` in `Theorem_3_8`, the upstream convexity
  owner for the canonical `partialInfProjection`;
- `partialInfProjection_realPart_convexOn_of_convexWithTop` in `Theorem_3_1_25`, the
  canonical convexity theorem on the owner partial infimal projection;
- `mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient` in
  `Theorem_3_1_25`, the source-faithful subgradient-transfer theorem.

Best owner abstraction:
- the two chapter owner-level recall targets in `Theorem_3_1_25`.

Primitive data:
- none in this file.

Derived API:
- this numbered recall surface.

Source/core/bridge triage:
- source-facing: Theorem 3.31's convexity and subgradient-transfer statements for partial
  infimal projection;
- core/canonical: the owner declarations in `Theorem_3_1_25`;
- bridge/view: this recall surface.

The previous file kept parallel theorem wrappers around declarations that now already live on the
correct owner abstractions in `Theorem_3_1_25`. The redundant wrappers are deleted here in favor
of direct recall/use. -/

recall partialInfProjection_realPart_convexOn_of_convexWithTop

recall mem_subdifferentialWithin_partialInfProjection_realPart_of_mem_argmin_of_subgradient
