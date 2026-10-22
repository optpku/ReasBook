/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.1.1.7 lies in the chapter's source-facing unit-disk boundary-extension domain.

Primary domain:
- lower-semicontinuity of a `WithTop ℝ`-valued boundary extension on the Euclidean unit disk.

Sampled owner-style declarations:
- `unitDiskBoundaryExtension` in `Proposition_3_8`, the existing source-facing owner for the
  textbook construction;
- `unitDiskBoundaryExtension_convex_and_effectiveDomain` in `Proposition_3_8`, the companion
  theorem supplying the owner-level convexity and effective-domain data of the same owner;
- `unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero` in `Proposition_3_8`, which already
  has the exact textbook interface of this item;
- mathlib `LowerSemicontinuous` together with the chapter's closed-convex recall surface in
  `Theorem_3_1_4`.

Best owner abstraction:
- the imported source-facing owner `unitDiskBoundaryExtension`.

Primitive data:
- the boundary datum `φ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 → ℝ`;
- the owner construction `unitDiskBoundaryExtension φ`.

Derived API:
- the open-disk value theorem already proved in `Proposition_3_8`;
- the convexity/effective-domain companion theorem
  `unitDiskBoundaryExtension_convex_and_effectiveDomain`;
- the lower-semicontinuity criterion
  `unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero`.

Source/core/bridge triage:
- source-facing: the unit-disk boundary extension and its vanishing criterion on the unit circle;
- core/canonical: `LowerSemicontinuous` for `WithTop ℝ`-valued functions;
- bridge/view: the owner-level convexity and effective-domain companion theorem from
  `Proposition_3_8`.

This file previously rebuilt the same owner and theorem family under duplicate local declarations.
Since `Proposition_3_8` already provides the correct source-facing owner in the minimal chapter
closure, this item is recall-only and reuses that canonical chapter declaration directly. -/

recall unitDiskBoundaryExtension_lowerSemicontinuous_iff_eq_zero
