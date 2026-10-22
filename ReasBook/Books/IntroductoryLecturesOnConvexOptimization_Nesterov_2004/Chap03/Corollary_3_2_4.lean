/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_52

-- Declarations for this item will be appended below by the statement pipeline.

/-
Corollary 3.2.4 lives in the localization-radius / ellipsoid-volume domain.

Sampled owner declarations:
- `localization_radius` and `localization_radius_le_outer_radius_mul_volume_ratio_rpow`
  from `Theorem_3_2_9`
- `inner_ball_radius_le_outer_radius_mul_volume_ratio_rpow_of_convex` from `Theorem_3_51`
- `selected_radius_bound_of_positive_index` and `selected_index_pos_of_volume_drop`
  from `Theorem_3_52`

Owner abstraction:
- the chapter localization-radius API, with `Theorem_3_52` as the selected-index bridge.

Primitive data:
- `Q`, the raw query sequence `querySeq`, the localization map `g`, the comparison sequence
  `Ell`, and the owner selected-index data `Nat.count` / `Nat.nth`.

Derived API:
- the corollary's two source-facing conclusions are already exactly the bridge theorems from
  `Theorem_3_52`, so adding local copies here would only duplicate API.

Triage:
- source-facing: the selected-stage radius bound and positivity of
  `Nat.count (fun j ↦ querySeq j ∈ Q) k`
- core/canonical: the localization-radius bound from `Theorem_3_2_9`
- bridge/view: the selected-index specialization from `Theorem_3_52`

This file therefore keeps Corollary 3.2.4 as direct canonical recalls and adds no parallel
wrapper theorems.
-/

recall selected_radius_bound_of_positive_index

recall selected_index_pos_of_volume_drop
