/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import Mathlib.Tactic.Recall
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_2_5

-- Declarations for this item will be appended below by the statement pipeline.

/- Proposition 1.7.4 lies in the chapter's scalar convergence-rate and complexity-threshold domain.

Primary domain:
* square-root decay bounds for real-valued error sequences

Sampled owner-style declarations:
* `sqrt_rate_complexity_bound`
* `exists_power_law_bound_of_sqrt_bound`
* `IsOptimizationErrorSequence.hasConvergenceRateOfOrder_of_sqrt_bound`
* `HasGeometricRateOfConvergence.complexity_bound`

Best owner abstraction:
* `sqrt_rate_complexity_bound` from `Definition_1_2_5.lean`

Primitive data:
* the sequence `r`
* the constant `c`
* the pointwise square-root estimate `r k ≤ c / Real.sqrt (k : ℝ)` on positive indices

Derived API:
* the explicit complexity threshold `(c / ε)^2`

Source/core/bridge triage:
* source-facing: the textbook square-root complexity threshold
* core/canonical: `sqrt_rate_complexity_bound`
* bridge/view: the pointwise square-root rate hypothesis

The former declaration in this file duplicated the owner theorem with exactly the same interface and
no extra mathematics. This recall file therefore keeps Proposition 1.7.4 machine-checkable as a
direct owner recall and introduces no parallel theorem name. -/

recall sqrt_rate_complexity_bound
    {r : ℕ → ℝ} {c ε : ℝ}
    (h : ∀ ⦃k : ℕ⦄, 0 < k → r k ≤ c / Real.sqrt (k : ℝ))
    (hε : 0 < ε)
    {k : ℕ} (hk : 0 < k)
    (hkComplexity : (c / ε) ^ (2 : ℕ) ≤ (k : ℝ)) :
    r k ≤ ε
