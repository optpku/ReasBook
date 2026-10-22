/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_3_3

noncomputable section

/- Proposition 3.57 lies in the constrained level-method total internal-complexity domain.

Relevant owner declarations sampled before refining:
- `ConstrainedLevelMethod.stoppingIndex` in `Algorithm_3_11`, the canonical full-step internal
  iteration count at one master step;
- `ConstrainedLevelMethod.globalStopIndex` in `Algorithm_3_11`, the canonical terminal-step
  internal iteration count at the first globally stopping master step;
- `constrainedLevelMethodInternalIterationBound` in `Theorem_3_3_3`, the uniform per-step
  internal-iteration bound;
- `constrained_level_total_internal_iterations_le` in `Theorem_3_3_3`, the chapter owner theorem
  for the total internal-iteration estimate.

Best owner abstraction:
- source-facing: the total internal iteration count of a constrained level method up to the first
  globally stopping master step;
- core/canonical: `constrained_level_total_internal_iterations_le`;
- bridge/view: none.

Primitive data:
- the constrained level method and its canonical full-step and terminal-step iteration counts;
- the logarithmic outer-step threshold and uniform per-step complexity bound.

Derived API:
- none beyond direct recall of the chapter owner theorem.

Source/core/bridge triage:
- source-facing: the constrained level method and its actual internal iteration counts;
- core/canonical: `constrained_level_total_internal_iterations_le`;
- bridge/view: none.

The former file duplicated the theorem from `Theorem_3_3_3` under a second public name with the
same interface. This refinement removes that parallel wrapper and keeps Proposition 3.57 as a
direct recall of the canonical chapter theorem. -/

/- Proposition 3.57 is the direct recall of the chapter owner theorem
`constrained_level_total_internal_iterations_le`. -/
recall constrained_level_total_internal_iterations_le

end
