/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Proposition 3.55 lies in the constrained level-method full-step complexity domain.

Relevant owner declarations sampled before refining:
- `LevelMethodHistory.gap` and `LevelMethodHistory.shouldStop` in `Lemma_3_3_1`, the canonical
  scalar-history owners;
- `ConstrainedLevelMethod.history` and `ConstrainedLevelMethod.stoppingIndex` in
  `Algorithm_3_11`, the canonical inner-history and full-step iteration-count owners;
- `ConstrainedLevelMethod.full_step_increment_le_uniform_internal_iteration_bound` in
  `Lemma_3_3_9`, the chapter owner of the one-step full-step complexity estimate.

Best owner abstraction:
- source-facing: Proposition 3.55's relative stopping inequality and the resulting full-step
  internal-iteration estimate;
- core/canonical: `LevelMethodHistory.gap` and
  `ConstrainedLevelMethod.full_step_increment_le_uniform_internal_iteration_bound`;
- bridge/view: the scalar rearrangement converting the relative stopping inequality into a gap
  bound.
-/

namespace LevelMethodHistory

/-- Proposition 3.55 (1): if the relative termination rule
`fhat(history, k) ≥ (1 - κ) fstar(history, k)` holds at a selected full step, then the owner gap
`δ[history](k) = fstar(history, k) - fhat(history, k)` is bounded by
`κ fstar(history, k)`. -/
theorem gap_le_kappa_mul_optimalValue_of_termination_rule
    (history : LevelMethodHistory) {κ : ℝ} (k : ℕ)
    (htermination :
      history.approximateOptimalValue k ≥ (1 - κ) * history.optimalValue k) :
    history.gap k ≤ κ * history.optimalValue k := by
  -- Rewrite the gap into the source-proof difference `f* - f̂*`.
  rw [history.gap_eq_sub]
  -- Rearrange the termination inequality to isolate the gap on the left-hand side.
  linarith

end LevelMethodHistory

namespace ConstrainedLevelMethod

/- Proposition 3.55 (2): the chapter already owns the full-step internal-iteration estimate in
`Lemma_3_3_9` under the canonical constrained-level method API. -/
recall full_step_increment_le_uniform_internal_iteration_bound

end ConstrainedLevelMethod

end
