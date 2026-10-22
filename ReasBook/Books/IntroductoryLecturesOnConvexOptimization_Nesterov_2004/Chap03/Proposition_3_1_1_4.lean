/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 3.1.1.4 lies in the chapter's one-dimensional extended-real convex-analysis domain.

Primary domain:
- the reciprocal function on `(0, ∞)` and its `WithTop ℝ` epigraph/lower-semicontinuity package.

Sampled owner-style declarations:
- chapter `positiveReciprocalExtension`
- chapter `reciprocalEpigraphOnPositiveRay`
- chapter `dom f` and `constrainedEpigraph Q f` from `Definition_3_3`
- mathlib `strictConvexOn_zpow`
- mathlib `lowerSemicontinuous_iff_isClosed_epigraph`

Best owner abstraction:
- the existing chapter owner declaration `positiveReciprocalExtension` from `Proposition_3_5`,
  together with the Chapter 2 owner set `reciprocalEpigraphOnPositiveRay` and the chapter
  canonical epigraph/domain owners `constrainedEpigraph` and `dom` from `Definition_3_3`.

Primitive data:
- the extended reciprocal function on `ℝ`

Derived API:
- the epigraph identification bridge to `reciprocalEpigraphOnPositiveRay`
- convexity on `Set.Ioi 0`
- lower semicontinuity
- closedness of the epigraph
- identification and openness of the effective domain

Source/core/bridge triage:
- source-facing: the reciprocal-extension proposition package already owned by `Proposition_3_5`
- core/canonical: `reciprocalEpigraphOnPositiveRay`, `dom`, `constrainedEpigraph`, and the
  mathlib convexity/lower-semicontinuity owners
- bridge/view: this numbering-local file, which should only recall the upstream chapter owner
  declarations and canonical expressions instead of reintroducing a parallel duplicate API

This file is therefore recall-only. Keeping local names such as `reciprocalWithTop` would create a
second public owner for the same mathematics with the same interface, which is exactly the
duplicate-wheel pattern the chapter policy forbids. -/

recall positiveReciprocalExtension

recall reciprocalEpigraphOnPositiveRay

recall positiveReciprocalExtensionEpigraph_eq_reciprocalEpigraphOnPositiveRay

recall mem_reciprocalEpigraphOnPositiveRay_iff

recall convexOn_one_div_Ioi_zero

recall lowerSemicontinuous_positiveReciprocalExtension

recall reciprocalEpigraphOnPositiveRay_isClosed

recall positiveReciprocalExtension_effectiveDomain_eq_Ioi

recall isOpen_positiveReciprocalExtension_effectiveDomain
