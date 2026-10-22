/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_7

-- Declarations for this item will be appended below by the statement pipeline.

/-
Lemma 3.39 lies in the complete-data level-method geometric-decay domain.

Sampled owner-style declarations:
- `selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay` in
  `Lemma_3_3_7.lean`, the earlier chapter theorem with the same geometric-decay content and the
  sharper Lean interface keeping only the mathematically effective hypotheses;
- `HasGeometricRateOfConvergence` in `Chap01/Definition_1_2_6.lean`, the scalar owner predicate
  for geometric decay;
- `HasGeometricRateOfConvergence.of_step_bound` in `Chap01/Definition_1_2_6.lean`, the canonical
  one-step-to-geometric bridge used throughout the project;
- `constrainedMinimizationInternalGap_hasGeometricRateOfConvergence` in
  `Chap02/Proposition_2_30.lean`, the chapter style example of exposing the source-facing theorem
  through that scalar owner abstraction.

Best owner abstraction:
- source-facing owner for this exact statement:
  `selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay`;
- core/canonical owner beneath it: `HasGeometricRateOfConvergence`.

Primitive data:
- the scalar sequences `t` and `j`;
- the exact and estimated value families;
- the comparison, initialization, and step-size hypotheses.

Derived API:
- the geometric upper bound for the selected exact values.

Source/core/bridge triage:
- source-facing: Lemma 3.39 itself, stated in the complete-data `exactValue` / `estimatedValue`
  notation;
- core/canonical: `HasGeometricRateOfConvergence` and `of_step_bound`;
- bridge/view: the earlier chapter theorem from `Lemma_3_3_7`, whose parameter name `ε` is only a
  binder-name variation of the present source notation `α`, and whose public header already drops
  the redundant textbook-side hypotheses.

The former version of this file duplicated both the source-facing theorem and its local helper
chain. Since `Lemma_3_3_7` already owns the exact public statement, this file stays recall-only
and introduces no parallel theorem shell; the direct owner use below is a `recall` of that owner
theorem rather than a second declaration.
-/

recall selected_exactValue_le_initial_gap_div_one_sub_epsilon_mul_geometric_decay
