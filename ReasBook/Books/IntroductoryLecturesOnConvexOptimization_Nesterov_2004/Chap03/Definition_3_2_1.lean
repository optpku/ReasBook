/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_2_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 3.2.1 lies in the cutting-plane localization-set / localization-radius domain.

Primary mathematical domain:
- cutting-plane localization sets in real inner-product spaces together with their associated
  pointwise and best localization radii.

Sampled owner-style declarations:
- `localizationSet`
- `mem_localizationSet_iff`
- `subgradientLocalizationMeasure`
- `localization_radius`

Best owner abstraction for this file:
- `source-facing`: the stage localization set `localizationSet Q xSeq gSeq k`, the associated
  pointwise radii `subgradientLocalizationMeasure g xStar (xSeq i)`, and their minimum
  `localization_radius xStar g xSeq k`
- `core/canonical`: the same project owners from `Lemma_3_2_1` and `Theorem_3_2_9`
- `bridge/view`: `localization_radius_le_measure` and the closed-ball comparison theorems
  `closedBall_subset_localizationSet_of_le_localization_radius` and
  `le_localization_radius_of_closedBall_subset_localizationSet`

Primitive data:
- a feasible region `Q`
- a reference point `xStar`
- a query-point sequence `xSeq`
- either a cut sequence `gSeq` for `S_k`, or the chosen subgradient selection `g` feeding the
  generic owner `subgradientLocalizationMeasure` behind `v_i` and `v_k^*`
- a stage index `k`

Derived API:
- the defining expansion of `S_k` via `mem_localizationSet_iff`
- the comparison `v_k^* ≤ v_i` via `localization_radius_le_measure`
- the centered-ball characterization of `v_k^*` via the closed-ball inclusion and converse
  theorems

This file stays at the source-facing layer: it recalls the canonical owners for `S_k`, the
associated radii `v_i` and `v_k^*`, and the ball characterization of `v_k^*`, without introducing
any local wrapper or parallel chapter API. -/

recall localizationSet

recall mem_localizationSet_iff

recall subgradientLocalizationMeasure

recall localization_radius

recall localization_radius_le_measure

recall closedBall_subset_localizationSet_of_le_localization_radius

recall le_localization_radius_of_closedBall_subset_localizationSet
