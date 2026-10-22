/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_2_4

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 3.28 lies in the Euclidean closed-ball / midpoint-bisection-box domain.

Sampled owner-style declarations:
- mathlib `Metric.closedBall`
- project `FeasibilityResistingOracleState.currentCenter`
- project `FeasibilityResistingOracleState.currentBox`
- project `FeasibilityResistingOracleState.closedBall_subset_currentBox`

Best owner abstraction:
- the earlier chapter owner theorem
  `FeasibilityResistingOracleState.closedBall_subset_currentBox`.

Primitive data:
- a radius parameter `R`
- the positive dimension witness `hn`
- the resisting-oracle transcript `state`

Derived API:
- the textbook-radius closed-ball inclusion in the current realized midpoint-bisection box.

Source/core/bridge triage:
- source-facing: the textbook-radius ball inclusion in the current realized box
- core/canonical: the midpoint-bisection box owner in `Algorithm_3_5`
- bridge/view: the earlier chapter theorem
  `FeasibilityResistingOracleState.closedBall_subset_currentBox`, which already expresses exactly
  this source-level consequence

This item is recall-only: `Lemma_3_28` duplicated the earlier chapter theorem exactly, so the file
keeps the canonical recall instead of a second parallel public theorem.
-/

recall FeasibilityResistingOracleState.closedBall_subset_currentBox
