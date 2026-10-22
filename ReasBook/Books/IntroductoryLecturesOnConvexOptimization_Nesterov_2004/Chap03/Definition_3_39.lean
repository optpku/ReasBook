/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_2_1

-- Declarations for this item will be appended below by the statement pipeline.

recall localizationSet

recall mem_localizationSet_iff

recall subgradientLocalizationMeasure

/- Definition 3.39 [Chapter3_3.json:138]: for a feasible region `Q`, a cut map `g`, a query
sequence `xSeq`, and a reference point `xStar`, the textbook localization set
`S_k = {x ∈ Q | ⟪g(x_i), x_i - x⟫ ≥ 0 for all i = 0, ..., k}` is the chapter owner
`localizationSet Q xSeq (g ∘ xSeq) k`, the pointwise quantities `v_i` are the localization
measures `v[g; xStar] (xSeq i)`, and the best localization radius
`v_k^* = min_{0 ≤ i ≤ k} v_i` is the owner `localization_radius xStar g xSeq k`.
The equivalent closed-ball characterization of `v_k^*` is already provided by the companion
localization-set inclusion theorems, so this item remains a pure canonical recall with no
parallel local wrapper. -/
recall localization_radius

recall localization_radius_le_measure

recall closedBall_subset_localizationSet_of_le_localization_radius

recall le_localization_radius_of_closedBall_subset_localizationSet
