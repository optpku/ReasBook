/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_3_1

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped LevelMethodNotation

/- Lemma 3.35 lies in the chapter's level-method scalar-history domain.

Sampled owner declarations:
- `LevelMethodHistory` in `Lemma_3_3_1`, the owner bundle for `(\hat f_k^*, f_k^*)`
- `LevelMethodHistory.gap` in `Lemma_3_3_1`, the canonical gap `δ_k`
- the notation `δ[history](k)` in `Lemma_3_3_1`, the source-facing surface for those gaps
- `LevelMethodHistory.levelValue_eq_optimal_sub_one_sub_alpha_mul_gap` in `Lemma_3_3_1`, the
  nearby owner-level scalar rewrite using the same `1 - α` gap factor

Best owner abstraction:
- `LevelMethodHistory` with derived gap sequence `δ[history](k)`

Primitive data:
- `history.approximateOptimalValue`
- `history.optimalValue`

Derived API:
- `history.gap`
- the notation `δ[history](k)`

Source/core/bridge triage:
- source-facing: the scalar bound on the drop from `δ_k` to `δ_p`
- core/canonical: the gap owner `LevelMethodHistory.gap`
- bridge/view: this file's one-line inequality consequence on the owner-derived gap values

The previous declaration exposed a raw sequence `δ : ℕ → ℝ`, duplicating the chapter owner for
these scalar quantities. This file now states the same inequality directly for the canonical gap
API, with no change in mathematical content.
-/

namespace LevelMethodHistory

/-- Lemma 3.35: if the later gap satisfies `δ_p ≥ (1 - α) δ_k`, then the gap drop
`δ_k - δ_p` is bounded above by `α δ_k`. -/
-- Proof sketch: rearrange the target inequality
-- `δ_k - δ_p ≤ α δ_k` to `(1 - α) δ_k ≤ δ_p`, which is exactly the hypothesis.
lemma gap_drop_le_alpha_mul_gap_of_gap_ge_one_sub_alpha_mul_gap
    (history : LevelMethodHistory) {k p : ℕ} {α : ℝ}
    (hgap : δ[history](p) ≥ (1 - α) * δ[history](k)) :
    δ[history](k) - δ[history](p) ≤ α * δ[history](k) := by
  linarith

end LevelMethodHistory

end
