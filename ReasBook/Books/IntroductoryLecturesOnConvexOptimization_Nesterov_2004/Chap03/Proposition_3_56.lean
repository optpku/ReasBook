/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 3.56 lies in the constrained level-method final-step complexity domain.

Relevant owner declarations sampled before refining:
- `ConstrainedLevelMethod.history`, `ConstrainedLevelMethod.stoppingIndex`, and
  `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical inner-history and
  iteration-count owners;
- `ConstrainedLevelMethod.last_step_internal_iterations_le_uniform_internal_iteration_bound` in
  `Lemma_3_3_9`, the chapter owner of the terminal-step complexity estimate;
- `constrainedLevelMethodInternalIterationBound` in `Theorem_3_3_3`, the displayed uniform
  per-step internal-iteration bound.

Best owner abstraction:
- source-facing: the final inner run of a constrained level method up to the first globally
  stopping index;
- core/canonical:
  `ConstrainedLevelMethod.last_step_internal_iterations_le_uniform_internal_iteration_bound`;
- bridge/view: the predecessor-gap comparison already packaged in the owner theorem above.
-/

/- Proposition 3.56: the terminal-step internal-iteration estimate is already owned by
`Lemma_3_3_9` under the canonical constrained-level method API. -/
recall ConstrainedLevelMethod.last_step_internal_iterations_le_uniform_internal_iteration_bound

end
