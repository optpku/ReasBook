/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Proposition_3_55

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

open scoped LevelMethodNotation

variable {E : Type u} [NormedAddCommGroup E]

/- Theorem 3.55 lies in the constrained level-method full-step complexity domain.

Relevant owner declarations sampled before refining:
- `ConstrainedLevelMethod.history` in `Algorithm_3_11`, the canonical inner scalar history at a
  master step;
- `ConstrainedLevelMethod.stoppingIndex` in `Algorithm_3_11`, the canonical full-step internal
  count `j(k) - j(k - 1)`;
- `LevelMethodHistory.gap_le_kappa_mul_optimalValue_of_termination_rule` in `Proposition_3_55`,
  the gap-control companion for the relative stopping rule;
- `ConstrainedLevelMethod.full_step_increment_le_uniform_internal_iteration_bound` in
  `Proposition_3_55`, the chapter owner of the one-step full-step complexity estimate.

Best owner abstraction:
- source-facing: the internal-iteration bound for one full master step of a
  `ConstrainedLevelMethod`;
- core/canonical: `ConstrainedLevelMethod.full_step_increment_le_uniform_internal_iteration_bound`;
- bridge/view: Proposition `3.55 (1)`, which converts the relative stopping inequality into the
  canonical gap bound used in the full-step estimate.

Primitive data:
- `method : ConstrainedLevelMethodInput E` together with the recursion hypotheses
  `hrelative : method.RelativeStoppingExists` and
  `hfinite : method.SelectedThresholdFinite hrelative`;
- a master-step index `k` and the block estimate `hblock` on the inner history
  `ConstrainedLevelMethod.history method hrelative hfinite k`;
- the full-step hypothesis
  `method.epsilon ≤
    (ConstrainedLevelMethod.history method hrelative hfinite k).optimalValue
      (ConstrainedLevelMethod.stoppingIndex method hrelative hfinite k)`.

Derived API:
- the canonical bound
  `ConstrainedLevelMethod.stoppingIndex method hrelative hfinite k ≤
    levelMethodIterationCap M_f D (method.chi * method.epsilon) method.levelCoefficient`.

Source/core/bridge triage:
- source-facing: the one-step full-step complexity estimate;
- core/canonical: `ConstrainedLevelMethod.full_step_increment_le_uniform_internal_iteration_bound`;
- bridge/view: the relative-stopping gap estimate from Proposition `3.55 (1)`.

This file is recall-only: the chapter already owns the exact theorem interface upstream in
`Proposition_3_55`, so a second local declaration here would only duplicate that owner API.
-/

/- Theorem 3.55: at a full master step, the canonical internal iteration count
`ConstrainedLevelMethod.stoppingIndex method hrelative hfinite k = j(k) - j(k - 1)` is bounded
by the chapter owner `levelMethodIterationCap` evaluated at the uniform tolerance `χ ε`. -/
recall ConstrainedLevelMethod.full_step_increment_le_uniform_internal_iteration_bound

end
